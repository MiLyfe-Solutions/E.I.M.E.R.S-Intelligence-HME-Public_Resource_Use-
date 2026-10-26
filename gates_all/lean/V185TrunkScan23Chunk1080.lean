import V185TrunkScan23Chunk1079

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6393967 : List Nat := [1, 1, 2, 1, 3, 5, 2, 2, 1, 5]
def baseStart_6393967 : Nat := 118140960795 + 6393967 * 2 ^ 59
def prefixEnd_6393967 : Nat := 4983230072969 + 3 ^ 40 * 6393967 * 2
def baseEnd_6393967 : Nat := 1094392786662163436135729

theorem tailTrace_6393967 : CollatzResearch.WordTrace tailWord_6393967 prefixEnd_6393967 1094392786662163436135729 := by
  unfold tailWord_6393967
  simp only [CollatzResearch.WordTrace]
  refine ⟨233207135226757036469940155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155471423484504690979960103 233207135226757036469940155)
  ·
    refine ⟨349810702840135554704910233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233207135226757036469940155 349810702840135554704910233)
    ·
      refine ⟨262358027130101666028682675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349810702840135554704910233 262358027130101666028682675)
      ·
        refine ⟨393537040695152499043024013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262358027130101666028682675 393537040695152499043024013)
        ·
          refine ⟨147576390260682187141134005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 393537040695152499043024013 147576390260682187141134005)
          ·
            refine ⟨13835286586938955044481313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147576390260682187141134005 13835286586938955044481313)
            ·
              refine ⟨10376464940204216283360985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13835286586938955044481313 10376464940204216283360985)
              ·
                refine ⟨7782348705153162212520739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10376464940204216283360985 7782348705153162212520739)
                ·
                  refine ⟨11673523057729743318781109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7782348705153162212520739 11673523057729743318781109)
                  ·
                    refine ⟨1094392786662163436135729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11673523057729743318781109 1094392786662163436135729)
                    ·
                      rfl

theorem cell23_6393967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 5].length) (baseStart_6393967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393967 prefixEnd_6393967 := by exact prefixLift 6393967
  have htrace : WordTrace (prefixWord ++ tailWord_6393967) baseStart_6393967 baseEnd_6393967 := by
    simpa [prefixWord, tailWord_6393967, baseEnd_6393967] using wordTrace_append hprefix tailTrace_6393967
  have hstable : (prefixWord ++ tailWord_6393967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393967).length < 2 ^ (prefixWord ++ tailWord_6393967).sum := by decide
  have hdescent : baseEnd_6393967 < baseStart_6393967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393974 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2]
def baseStart_6393974 : Nat := 118140960795 + 6393974 * 2 ^ 59
def prefixEnd_6393974 : Nat := 4983230072969 + 3 ^ 40 * 6393974 * 2
def baseEnd_6393974 : Nat := 3283181954351071781019655

theorem tailTrace_6393974 : CollatzResearch.WordTrace tailWord_6393974 prefixEnd_6393974 3283181954351071781019655 := by
  unfold tailWord_6393974
  simp only [CollatzResearch.WordTrace]
  refine ⟨14575461908608229791590311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155471593691821117776963317 14575461908608229791590311)
  ·
    refine ⟨21863192862912344687385467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14575461908608229791590311 21863192862912344687385467)
    ·
      refine ⟨32794789294368517031078201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21863192862912344687385467 32794789294368517031078201)
      ·
        refine ⟨24596091970776387773308651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32794789294368517031078201 24596091970776387773308651)
        ·
          refine ⟨36894137956164581659962977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24596091970776387773308651 36894137956164581659962977)
          ·
            refine ⟨27670603467123436244972233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36894137956164581659962977 27670603467123436244972233)
            ·
              refine ⟨20752952600342577183729175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27670603467123436244972233 20752952600342577183729175)
              ·
                refine ⟨31129428900513865775593763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20752952600342577183729175 31129428900513865775593763)
                ·
                  refine ⟨46694143350770798663390645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31129428900513865775593763 46694143350770798663390645)
                  ·
                    refine ⟨4377575939134762374692873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46694143350770798663390645 4377575939134762374692873)
                    ·
                      refine ⟨3283181954351071781019655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4377575939134762374692873 3283181954351071781019655)
                      ·
                        rfl

theorem cell23_6393974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_6393974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393974 prefixEnd_6393974 := by exact prefixLift 6393974
  have htrace : WordTrace (prefixWord ++ tailWord_6393974) baseStart_6393974 baseEnd_6393974 := by
    simpa [prefixWord, tailWord_6393974, baseEnd_6393974] using wordTrace_append hprefix tailTrace_6393974
  have hstable : (prefixWord ++ tailWord_6393974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393974).length < 2 ^ (prefixWord ++ tailWord_6393974).sum := by decide
  have hdescent : baseEnd_6393974 < baseStart_6393974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393981 : List Nat := [1, 4, 1, 1, 3, 2, 3, 3, 1, 1, 3]
def baseStart_6393981 : Nat := 118140960795 + 6393981 * 2 ^ 59
def prefixEnd_6393981 : Nat := 4983230072969 + 3 ^ 40 * 6393981 * 2
def baseEnd_6393981 : Nat := 3283185548715653253632123

theorem tailTrace_6393981 : CollatzResearch.WordTrace tailWord_6393981 prefixEnd_6393981 3283185548715653253632123 := by
  unfold tailWord_6393981
  simp only [CollatzResearch.WordTrace]
  refine ⟨233207645848706316860949797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155471763899137544573966531 233207645848706316860949797)
  ·
    refine ⟨43726433596632434411428087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233207645848706316860949797 43726433596632434411428087)
    ·
      refine ⟨65589650394948651617142131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43726433596632434411428087 65589650394948651617142131)
      ·
        refine ⟨98384475592422977425713197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65589650394948651617142131 98384475592422977425713197)
        ·
          refine ⟨36894178347158616534642449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98384475592422977425713197 36894178347158616534642449)
          ·
            refine ⟨27670633760368962400981837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36894178347158616534642449 27670633760368962400981837)
            ·
              refine ⟨10376487660138360900368189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27670633760368962400981837 10376487660138360900368189)
              ·
                refine ⟨3891182872551885337638071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10376487660138360900368189 3891182872551885337638071)
                ·
                  refine ⟨5836774308827828006457107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3891182872551885337638071 5836774308827828006457107)
                  ·
                    refine ⟨8755161463241742009685661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5836774308827828006457107 8755161463241742009685661)
                    ·
                      refine ⟨3283185548715653253632123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8755161463241742009685661 3283185548715653253632123)
                      ·
                        rfl

theorem cell23_6393981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_6393981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393981 prefixEnd_6393981 := by exact prefixLift 6393981
  have htrace : WordTrace (prefixWord ++ tailWord_6393981) baseStart_6393981 baseEnd_6393981 := by
    simpa [prefixWord, tailWord_6393981, baseEnd_6393981] using wordTrace_append hprefix tailTrace_6393981
  have hstable : (prefixWord ++ tailWord_6393981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393981).length < 2 ^ (prefixWord ++ tailWord_6393981).sum := by decide
  have hdescent : baseEnd_6393981 < baseStart_6393981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393987 : List Nat := [1, 1, 1, 3, 3, 3, 2, 3, 1, 1, 4]
def baseStart_6393987 : Nat := 118140960795 + 6393987 * 2 ^ 59
def prefixEnd_6393987 : Nat := 4983230072969 + 3 ^ 40 * 6393987 * 2
def baseEnd_6393987 : Nat := 3283188629599580230157095

theorem tailTrace_6393987 : CollatzResearch.WordTrace tailWord_6393987 prefixEnd_6393987 3283188629599580230157095 := by
  unfold tailWord_6393987
  simp only [CollatzResearch.WordTrace]
  refine ⟨233207864686684579885668215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155471909791123053257112143 233207864686684579885668215)
  ·
    refine ⟨349811797030026869828502323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233207864686684579885668215 349811797030026869828502323)
    ·
      refine ⟨524717695545040304742753485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349811797030026869828502323 524717695545040304742753485)
      ·
        refine ⟨196769135829390114278532557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 524717695545040304742753485 196769135829390114278532557)
        ·
          refine ⟨73788425936021292854449709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196769135829390114278532557 73788425936021292854449709)
          ·
            refine ⟨27670659726007984820418641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73788425936021292854449709 27670659726007984820418641)
            ·
              refine ⟨20752994794505988615313981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27670659726007984820418641 20752994794505988615313981)
              ·
                refine ⟨7782373047939745730742743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20752994794505988615313981 7782373047939745730742743)
                ·
                  refine ⟨11673559571909618596114115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7782373047939745730742743 11673559571909618596114115)
                  ·
                    refine ⟨17510339357864427894171173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11673559571909618596114115 17510339357864427894171173)
                    ·
                      refine ⟨3283188629599580230157095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17510339357864427894171173 3283188629599580230157095)
                      ·
                        rfl

theorem cell23_6393987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_6393987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393987 prefixEnd_6393987 := by exact prefixLift 6393987
  have htrace : WordTrace (prefixWord ++ tailWord_6393987) baseStart_6393987 baseEnd_6393987 := by
    simpa [prefixWord, tailWord_6393987, baseEnd_6393987] using wordTrace_append hprefix tailTrace_6393987
  have hstable : (prefixWord ++ tailWord_6393987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393987).length < 2 ^ (prefixWord ++ tailWord_6393987).sum := by decide
  have hdescent : baseEnd_6393987 < baseStart_6393987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6393998 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3]
def baseStart_6393998 : Nat := 118140960795 + 6393998 * 2 ^ 59
def prefixEnd_6393998 : Nat := 4983230072969 + 3 ^ 40 * 6393998 * 2
def baseEnd_6393998 : Nat := 3283194277886779687119545

theorem tailTrace_6393998 : CollatzResearch.WordTrace tailWord_6393998 prefixEnd_6393998 3283194277886779687119545 := by
  unfold tailWord_6393998
  simp only [CollatzResearch.WordTrace]
  refine ⟨29151033236205591095539831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155472177259763152509545765 29151033236205591095539831)
  ·
    refine ⟨43726549854308386643309747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29151033236205591095539831 43726549854308386643309747)
    ·
      refine ⟨65589824781462579964964621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43726549854308386643309747 65589824781462579964964621)
      ·
        refine ⟨24596184293048467486861733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65589824781462579964964621 24596184293048467486861733)
        ·
          refine ⟨4611784554946587653786575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24596184293048467486861733 4611784554946587653786575)
          ·
            refine ⟨6917676832419881480679863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4611784554946587653786575 6917676832419881480679863)
            ·
              refine ⟨10376515248629822221019795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6917676832419881480679863 10376515248629822221019795)
              ·
                refine ⟨15564772872944733331529693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10376515248629822221019795 15564772872944733331529693)
                ·
                  refine ⟨5836789827354274999323635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15564772872944733331529693 5836789827354274999323635)
                  ·
                    refine ⟨8755184741031412498985453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5836789827354274999323635 8755184741031412498985453)
                    ·
                      refine ⟨3283194277886779687119545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8755184741031412498985453 3283194277886779687119545)
                      ·
                        rfl

theorem cell23_6393998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_6393998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6393998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6393998 prefixEnd_6393998 := by exact prefixLift 6393998
  have htrace : WordTrace (prefixWord ++ tailWord_6393998) baseStart_6393998 baseEnd_6393998 := by
    simpa [prefixWord, tailWord_6393998, baseEnd_6393998] using wordTrace_append hprefix tailTrace_6393998
  have hstable : (prefixWord ++ tailWord_6393998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6393998).length < 2 ^ (prefixWord ++ tailWord_6393998).sum := by decide
  have hdescent : baseEnd_6393998 < baseStart_6393998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6393998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394098 : List Nat := [3, 2, 1, 3, 2, 1, 4, 1, 1, 3, 2]
def baseStart_6394098 : Nat := 118140960795 + 6394098 * 2 ^ 59
def prefixEnd_6394098 : Nat := 4983230072969 + 3 ^ 40 * 6394098 * 2
def baseEnd_6394098 : Nat := 3283245625952229295869085

theorem tailTrace_6394098 : CollatzResearch.WordTrace tailWord_6394098 prefixEnd_6394098 3283245625952229295869085 := by
  unfold tailWord_6394098
  simp only [CollatzResearch.WordTrace]
  refine ⟨58302978297320611460739737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155474608792854963895305965 58302978297320611460739737)
  ·
    refine ⟨43727233722990458595554803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58302978297320611460739737 43727233722990458595554803)
    ·
      refine ⟨65590850584485687893332205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43727233722990458595554803 65590850584485687893332205)
      ·
        refine ⟨24596568969182132959999577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65590850584485687893332205 24596568969182132959999577)
        ·
          refine ⟨18447426726886599719999683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24596568969182132959999577 18447426726886599719999683)
          ·
            refine ⟨27671140090329899579999525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18447426726886599719999683 27671140090329899579999525)
            ·
              refine ⟨5188338766936856171249911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27671140090329899579999525 5188338766936856171249911)
              ·
                refine ⟨7782508150405284256874867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5188338766936856171249911 7782508150405284256874867)
                ·
                  refine ⟨11673762225607926385312301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7782508150405284256874867 11673762225607926385312301)
                  ·
                    refine ⟨4377660834602972394492113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11673762225607926385312301 4377660834602972394492113)
                    ·
                      refine ⟨3283245625952229295869085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4377660834602972394492113 3283245625952229295869085)
                      ·
                        rfl

theorem cell23_6394098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_6394098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394098 prefixEnd_6394098 := by exact prefixLift 6394098
  have htrace : WordTrace (prefixWord ++ tailWord_6394098) baseStart_6394098 baseEnd_6394098 := by
    simpa [prefixWord, tailWord_6394098, baseEnd_6394098] using wordTrace_append hprefix tailTrace_6394098
  have hstable : (prefixWord ++ tailWord_6394098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394098).length < 2 ^ (prefixWord ++ tailWord_6394098).sum := by decide
  have hdescent : baseEnd_6394098 < baseStart_6394098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394147 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 2, 5]
def baseStart_6394147 : Nat := 118140960795 + 6394147 * 2 ^ 59
def prefixEnd_6394147 : Nat := 4983230072969 + 3 ^ 40 * 6394147 * 2
def baseEnd_6394147 : Nat := 1094423595501433201385453

theorem tailTrace_6394147 : CollatzResearch.WordTrace tailWord_6394147 prefixEnd_6394147 1094423595501433201385453 := by
  unfold tailWord_6394147
  simp only [CollatzResearch.WordTrace]
  refine ⟨233213700366104927211492695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155475800244069951474328463 233213700366104927211492695)
  ·
    refine ⟨349820550549157390817239043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233213700366104927211492695 349820550549157390817239043)
    ·
      refine ⟨524730825823736086225858565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349820550549157390817239043 524730825823736086225858565)
      ·
        refine ⟨98387029841950516167348481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 524730825823736086225858565 98387029841950516167348481)
        ·
          refine ⟨73790272381462887125511361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98387029841950516167348481 73790272381462887125511361)
          ·
            refine ⟨55342704286097165344133521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73790272381462887125511361 55342704286097165344133521)
            ·
              refine ⟨41507028214572874008100141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55342704286097165344133521 41507028214572874008100141)
              ·
                refine ⟨15565135580464827753037553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41507028214572874008100141 15565135580464827753037553)
                ·
                  refine ⟨11673851685348620814778165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15565135580464827753037553 11673851685348620814778165)
                  ·
                    refine ⟨1094423595501433201385453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11673851685348620814778165 1094423595501433201385453)
                    ·
                      rfl

theorem cell23_6394147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 5].length) (baseStart_6394147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394147 prefixEnd_6394147 := by exact prefixLift 6394147
  have htrace : WordTrace (prefixWord ++ tailWord_6394147) baseStart_6394147 baseEnd_6394147 := by
    simpa [prefixWord, tailWord_6394147, baseEnd_6394147] using wordTrace_append hprefix tailTrace_6394147
  have hstable : (prefixWord ++ tailWord_6394147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394147).length < 2 ^ (prefixWord ++ tailWord_6394147).sum := by decide
  have hdescent : baseEnd_6394147 < baseStart_6394147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394164 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_6394164 : Nat := 118140960795 + 6394164 * 2 ^ 59
def prefixEnd_6394164 : Nat := 4983230072969 + 3 ^ 40 * 6394164 * 2
def baseEnd_6394164 : Nat := 1094426505225142012547927

theorem tailTrace_6394164 : CollatzResearch.WordTrace tailWord_6394164 prefixEnd_6394164 1094426505225142012547927 := by
  unfold tailWord_6394164
  simp only [CollatzResearch.WordTrace]
  refine ⟨116607160203521669557430773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155476213604695559409907697 116607160203521669557430773)
  ·
    refine ⟨10931921269080156521009135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116607160203521669557430773 10931921269080156521009135)
    ·
      refine ⟨16397881903620234781513703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10931921269080156521009135 16397881903620234781513703)
      ·
        refine ⟨24596822855430352172270555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16397881903620234781513703 24596822855430352172270555)
        ·
          refine ⟨36895234283145528258405833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24596822855430352172270555 36895234283145528258405833)
          ·
            refine ⟨27671425712359146193804375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36895234283145528258405833 27671425712359146193804375)
            ·
              refine ⟨41507138568538719290706563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27671425712359146193804375 41507138568538719290706563)
              ·
                refine ⟨62260707852808078936059845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41507138568538719290706563 62260707852808078936059845)
                ·
                  refine ⟨11673882722401514800511221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62260707852808078936059845 11673882722401514800511221)
                  ·
                    refine ⟨1094426505225142012547927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11673882722401514800511221 1094426505225142012547927)
                    ·
                      rfl

theorem cell23_6394164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_6394164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394164 prefixEnd_6394164 := by exact prefixLift 6394164
  have htrace : WordTrace (prefixWord ++ tailWord_6394164) baseStart_6394164 baseEnd_6394164 := by
    simpa [prefixWord, tailWord_6394164, baseEnd_6394164] using wordTrace_append hprefix tailTrace_6394164
  have hstable : (prefixWord ++ tailWord_6394164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394164).length < 2 ^ (prefixWord ++ tailWord_6394164).sum := by decide
  have hdescent : baseEnd_6394164 < baseStart_6394164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394174 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_6394174 : Nat := 118140960795 + 6394174 * 2 ^ 59
def prefixEnd_6394174 : Nat := 4983230072969 + 3 ^ 40 * 6394174 * 2
def baseEnd_6394174 : Nat := 3283284650481970998518735

theorem tailTrace_6394174 : CollatzResearch.WordTrace tailWord_6394174 prefixEnd_6394174 3283284650481970998518735 := by
  unfold tailWord_6394174
  simp only [CollatzResearch.WordTrace]
  refine ⟨29151835642125888852840697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155476456758004740548483717 29151835642125888852840697)
  ·
    refine ⟨21863876731594416639630523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29151835642125888852840697 21863876731594416639630523)
    ·
      refine ⟨32795815097391624959445785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21863876731594416639630523 32795815097391624959445785)
      ·
        refine ⟨24596861323043718719584339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32795815097391624959445785 24596861323043718719584339)
        ·
          refine ⟨36895291984565578079376509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24596861323043718719584339 36895291984565578079376509)
          ·
            refine ⟨13835734494212091779766191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36895291984565578079376509 13835734494212091779766191)
            ·
              refine ⟨20753601741318137669649287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13835734494212091779766191 20753601741318137669649287)
              ·
                refine ⟨31130402611977206504473931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20753601741318137669649287 31130402611977206504473931)
                ·
                  refine ⟨46695603917965809756710897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31130402611977206504473931 46695603917965809756710897)
                  ·
                    refine ⟨35021702938474357317533173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46695603917965809756710897 35021702938474357317533173)
                    ·
                      refine ⟨3283284650481970998518735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35021702938474357317533173 3283284650481970998518735)
                      ·
                        rfl

theorem cell23_6394174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_6394174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394174 prefixEnd_6394174 := by exact prefixLift 6394174
  have htrace : WordTrace (prefixWord ++ tailWord_6394174) baseStart_6394174 baseEnd_6394174 := by
    simpa [prefixWord, tailWord_6394174, baseEnd_6394174] using wordTrace_append hprefix tailTrace_6394174
  have hstable : (prefixWord ++ tailWord_6394174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394174).length < 2 ^ (prefixWord ++ tailWord_6394174).sum := by decide
  have hdescent : baseEnd_6394174 < baseStart_6394174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394184 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 2, 4, 2]
def baseStart_6394184 : Nat := 118140960795 + 6394184 * 2 ^ 59
def prefixEnd_6394184 : Nat := 4983230072969 + 3 ^ 40 * 6394184 * 2
def baseEnd_6394184 : Nat := 3283289785288515959393689

theorem tailTrace_6394184 : CollatzResearch.WordTrace tailWord_6394184 prefixEnd_6394184 3283289785288515959393689 := by
  unfold tailWord_6394184
  simp only [CollatzResearch.WordTrace]
  refine ⟨116607524933485441265294803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155476699911313921687059737 116607524933485441265294803)
  ·
    refine ⟨174911287400228161897942205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116607524933485441265294803 174911287400228161897942205)
    ·
      refine ⟨65591732775085560711728327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174911287400228161897942205 65591732775085560711728327)
      ·
        refine ⟨98387599162628341067592491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65591732775085560711728327 98387599162628341067592491)
        ·
          refine ⟨147581398743942511601388737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98387599162628341067592491 147581398743942511601388737)
          ·
            refine ⟨110686049057956883701041553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147581398743942511601388737 110686049057956883701041553)
            ·
              refine ⟨83014536793467662775781165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110686049057956883701041553 83014536793467662775781165)
              ·
                refine ⟨31130451297550373540917937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83014536793467662775781165 31130451297550373540917937)
                ·
                  refine ⟨23347838473162780155688453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31130451297550373540917937 23347838473162780155688453)
                  ·
                    refine ⟨4377719713718021279191585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23347838473162780155688453 4377719713718021279191585)
                    ·
                      refine ⟨3283289785288515959393689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4377719713718021279191585 3283289785288515959393689)
                      ·
                        rfl

theorem cell23_6394184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_6394184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394184 prefixEnd_6394184 := by exact prefixLift 6394184
  have htrace : WordTrace (prefixWord ++ tailWord_6394184) baseStart_6394184 baseEnd_6394184 := by
    simpa [prefixWord, tailWord_6394184, baseEnd_6394184] using wordTrace_append hprefix tailTrace_6394184
  have hstable : (prefixWord ++ tailWord_6394184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394184).length < 2 ^ (prefixWord ++ tailWord_6394184).sum := by decide
  have hdescent : baseEnd_6394184 < baseStart_6394184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394187 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 3]
def baseStart_6394187 : Nat := 118140960795 + 6394187 * 2 ^ 59
def prefixEnd_6394187 : Nat := 4983230072969 + 3 ^ 40 * 6394187 * 2
def baseEnd_6394187 : Nat := 3283291325730479447656175

theorem tailTrace_6394187 : CollatzResearch.WordTrace tailWord_6394187 prefixEnd_6394187 3283291325730479447656175 := by
  unfold tailWord_6394187
  simp only [CollatzResearch.WordTrace]
  refine ⟨233215159285960014042948815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155476772857306676028632543 233215159285960014042948815)
  ·
    refine ⟨349822738928940021064423223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233215159285960014042948815 349822738928940021064423223)
    ·
      refine ⟨524734108393410031596634835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349822738928940021064423223 524734108393410031596634835)
      ·
        refine ⟨787101162590115047394952253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524734108393410031596634835 787101162590115047394952253)
        ·
          refine ⟨295162935971293142773107095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 787101162590115047394952253 295162935971293142773107095)
          ·
            refine ⟨442744403956939714159660643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295162935971293142773107095 442744403956939714159660643)
            ·
              refine ⟨664116605935409571239490965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442744403956939714159660643 664116605935409571239490965)
              ·
                refine ⟨31130465903222323651851139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 664116605935409571239490965 31130465903222323651851139)
                ·
                  refine ⟨46695698854833485477776709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31130465903222323651851139 46695698854833485477776709)
                  ·
                    refine ⟨8755443535281278527083133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46695698854833485477776709 8755443535281278527083133)
                    ·
                      refine ⟨3283291325730479447656175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8755443535281278527083133 3283291325730479447656175)
                      ·
                        rfl

theorem cell23_6394187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 3].length) (baseStart_6394187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394187 prefixEnd_6394187 := by exact prefixLift 6394187
  have htrace : WordTrace (prefixWord ++ tailWord_6394187) baseStart_6394187 baseEnd_6394187 := by
    simpa [prefixWord, tailWord_6394187, baseEnd_6394187] using wordTrace_append hprefix tailTrace_6394187
  have hstable : (prefixWord ++ tailWord_6394187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394187).length < 2 ^ (prefixWord ++ tailWord_6394187).sum := by decide
  have hdescent : baseEnd_6394187 < baseStart_6394187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394194 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 3, 4]
def baseStart_6394194 : Nat := 118140960795 + 6394194 * 2 ^ 59
def prefixEnd_6394194 : Nat := 4983230072969 + 3 ^ 40 * 6394194 * 2
def baseEnd_6394194 : Nat := 1094431640031686973422881

theorem tailTrace_6394194 : CollatzResearch.WordTrace tailWord_6394194 prefixEnd_6394194 1094431640031686973422881 := by
  unfold tailWord_6394194
  simp only [CollatzResearch.WordTrace]
  refine ⟨58303853649233663559613409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155476943064623102825635757 58303853649233663559613409)
  ·
    refine ⟨43727890236925247669710057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58303853649233663559613409 43727890236925247669710057)
    ·
      refine ⟨32795917677693935752282543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43727890236925247669710057 32795917677693935752282543)
      ·
        refine ⟨49193876516540903628423815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32795917677693935752282543 49193876516540903628423815)
        ·
          refine ⟨73790814774811355442635723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49193876516540903628423815 73790814774811355442635723)
          ·
            refine ⟨110686222162217033163953585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73790814774811355442635723 110686222162217033163953585)
            ·
              refine ⟨83014666621662774872965189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110686222162217033163953585 83014666621662774872965189)
              ·
                refine ⟨15565249991561770288680973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83014666621662774872965189 15565249991561770288680973)
                ·
                  refine ⟨5836968746835663858255365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15565249991561770288680973 5836968746835663858255365)
                  ·
                    refine ⟨1094431640031686973422881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5836968746835663858255365 1094431640031686973422881)
                    ·
                      rfl

theorem cell23_6394194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_6394194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394194 prefixEnd_6394194 := by exact prefixLift 6394194
  have htrace : WordTrace (prefixWord ++ tailWord_6394194) baseStart_6394194 baseEnd_6394194 := by
    simpa [prefixWord, tailWord_6394194, baseEnd_6394194] using wordTrace_append hprefix tailTrace_6394194
  have hstable : (prefixWord ++ tailWord_6394194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394194).length < 2 ^ (prefixWord ++ tailWord_6394194).sum := by decide
  have hdescent : baseEnd_6394194 < baseStart_6394194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394211 : List Nat := [1, 1, 1, 5, 2, 1, 2, 5, 1, 4]
def baseStart_6394211 : Nat := 118140960795 + 6394211 * 2 ^ 59
def prefixEnd_6394211 : Nat := 4983230072969 + 3 ^ 40 * 6394211 * 2
def baseEnd_6394211 : Nat := 1094434549755395784585355

theorem tailTrace_6394211 : CollatzResearch.WordTrace tailWord_6394211 prefixEnd_6394211 1094434549755395784585355 := by
  unfold tailWord_6394211
  simp only [CollatzResearch.WordTrace]
  refine ⟨233216034637873066141822487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155477356425248710761214991 233216034637873066141822487)
  ·
    refine ⟨349824051956809599212733731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233216034637873066141822487 349824051956809599212733731)
    ·
      refine ⟨524736077935214398819100597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349824051956809599212733731 524736077935214398819100597)
      ·
        refine ⟨49194007306426349889290681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 524736077935214398819100597 49194007306426349889290681)
        ·
          refine ⟨36895505479819762416968011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49194007306426349889290681 36895505479819762416968011)
          ·
            refine ⟨55343258219729643625452017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36895505479819762416968011 55343258219729643625452017)
            ·
              refine ⟨41507443664797232719089013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55343258219729643625452017 41507443664797232719089013)
              ·
                refine ⟨3891322843574740567414595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41507443664797232719089013 3891322843574740567414595)
                ·
                  refine ⟨5836984265362110851121893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3891322843574740567414595 5836984265362110851121893)
                  ·
                    refine ⟨1094434549755395784585355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5836984265362110851121893 1094434549755395784585355)
                    ·
                      rfl

theorem cell23_6394211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 1, 4].length) (baseStart_6394211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394211 prefixEnd_6394211 := by exact prefixLift 6394211
  have htrace : WordTrace (prefixWord ++ tailWord_6394211) baseStart_6394211 baseEnd_6394211 := by
    simpa [prefixWord, tailWord_6394211, baseEnd_6394211] using wordTrace_append hprefix tailTrace_6394211
  have hstable : (prefixWord ++ tailWord_6394211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394211).length < 2 ^ (prefixWord ++ tailWord_6394211).sum := by decide
  have hdescent : baseEnd_6394211 < baseStart_6394211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394224 : List Nat := [2, 1, 1, 1, 4, 4, 2, 2, 6]
def baseStart_6394224 : Nat := 118140960795 + 6394224 * 2 ^ 59
def prefixEnd_6394224 : Nat := 4983230072969 + 3 ^ 40 * 6394224 * 2
def baseEnd_6394224 : Nat := 364812258279410644765945

theorem tailTrace_6394224 : CollatzResearch.WordTrace tailWord_6394224 prefixEnd_6394224 364812258279410644765945 := by
  unfold tailWord_6394224
  simp only [CollatzResearch.WordTrace]
  refine ⟨116608254393412984681022863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155477672524550646241363817 116608254393412984681022863)
  ·
    refine ⟨174912381590119477021534295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116608254393412984681022863 174912381590119477021534295)
    ·
      refine ⟨262368572385179215532301443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174912381590119477021534295 262368572385179215532301443)
      ·
        refine ⟨393552858577768823298452165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262368572385179215532301443 393552858577768823298452165)
        ·
          refine ⟨73791160983331654368459781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 393552858577768823298452165 73791160983331654368459781)
          ·
            refine ⟨13835842684374685194086209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73791160983331654368459781 13835842684374685194086209)
            ·
              refine ⟨10376882013281013895564657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13835842684374685194086209 10376882013281013895564657)
              ·
                refine ⟨7782661509960760421673493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10376882013281013895564657 7782661509960760421673493)
                ·
                  refine ⟨364812258279410644765945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7782661509960760421673493 364812258279410644765945)
                  ·
                    rfl

theorem cell23_6394224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 6].length) (baseStart_6394224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394224 prefixEnd_6394224 := by exact prefixLift 6394224
  have htrace : WordTrace (prefixWord ++ tailWord_6394224) baseStart_6394224 baseEnd_6394224 := by
    simpa [prefixWord, tailWord_6394224, baseEnd_6394224] using wordTrace_append hprefix tailTrace_6394224
  have hstable : (prefixWord ++ tailWord_6394224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394224).length < 2 ^ (prefixWord ++ tailWord_6394224).sum := by decide
  have hdescent : baseEnd_6394224 < baseStart_6394224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394247 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_6394247 : Nat := 118140960795 + 6394247 * 2 ^ 59
def prefixEnd_6394247 : Nat := 4983230072969 + 3 ^ 40 * 6394247 * 2
def baseEnd_6394247 : Nat := 3283322134569749212905899

theorem tailTrace_6394247 : CollatzResearch.WordTrace tailWord_6394247 prefixEnd_6394247 3283322134569749212905899 := by
  unfold tailWord_6394247
  simp only [CollatzResearch.WordTrace]
  refine ⟨233217347665742644290132995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155478231777161762860088663 233217347665742644290132995)
  ·
    refine ⟨349826021498613966435199493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233217347665742644290132995 349826021498613966435199493)
    ·
      refine ⟨65592379030990118706599905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349826021498613966435199493 65592379030990118706599905)
      ·
        refine ⟨49194284273242589029949929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65592379030990118706599905 49194284273242589029949929)
        ·
          refine ⟨36895713204931941772462447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49194284273242589029949929 36895713204931941772462447)
          ·
            refine ⟨55343569807397912658693671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36895713204931941772462447 55343569807397912658693671)
            ·
              refine ⟨83015354711096868988040507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55343569807397912658693671 83015354711096868988040507)
              ·
                refine ⟨124523032066645303482060761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83015354711096868988040507 124523032066645303482060761)
                ·
                  refine ⟨93392274049983977611545571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124523032066645303482060761 93392274049983977611545571)
                  ·
                    refine ⟨140088411074975966417318357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93392274049983977611545571 140088411074975966417318357)
                    ·
                      refine ⟨3283322134569749212905899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140088411074975966417318357 3283322134569749212905899)
                      ·
                        rfl

theorem cell23_6394247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_6394247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394247 prefixEnd_6394247 := by exact prefixLift 6394247
  have htrace : WordTrace (prefixWord ++ tailWord_6394247) baseStart_6394247 baseEnd_6394247 := by
    simpa [prefixWord, tailWord_6394247, baseEnd_6394247] using wordTrace_append hprefix tailTrace_6394247
  have hstable : (prefixWord ++ tailWord_6394247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394247).length < 2 ^ (prefixWord ++ tailWord_6394247).sum := by decide
  have hdescent : baseEnd_6394247 < baseStart_6394247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394251 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 3, 1, 3]
def baseStart_6394251 : Nat := 118140960795 + 6394251 * 2 ^ 59
def prefixEnd_6394251 : Nat := 4983230072969 + 3 ^ 40 * 6394251 * 2
def baseEnd_6394251 : Nat := 3283324188492367197255881

theorem tailTrace_6394251 : CollatzResearch.WordTrace tailWord_6394251 prefixEnd_6394251 3283324188492367197255881 := by
  unfold tailWord_6394251
  simp only [CollatzResearch.WordTrace]
  refine ⟨233217493557728152973278607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155478329038485435315519071 233217493557728152973278607)
  ·
    refine ⟨349826240336592229459917911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233217493557728152973278607 349826240336592229459917911)
    ·
      refine ⟨524739360504888344189876867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349826240336592229459917911 524739360504888344189876867)
      ·
        refine ⟨787109040757332516284815301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524739360504888344189876867 787109040757332516284815301)
        ·
          refine ⟨147582945141999846803402869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 787109040757332516284815301 147582945141999846803402869)
          ·
            refine ⟨13835901107062485637819019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147582945141999846803402869 13835901107062485637819019)
            ·
              refine ⟨20753851660593728456728529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13835901107062485637819019 20753851660593728456728529)
              ·
                refine ⟨15565388745445296342546397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20753851660593728456728529 15565388745445296342546397)
                ·
                  refine ⟨5837020779541986128454899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15565388745445296342546397 5837020779541986128454899)
                  ·
                    refine ⟨8755531169312979192682349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5837020779541986128454899 8755531169312979192682349)
                    ·
                      refine ⟨3283324188492367197255881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8755531169312979192682349 3283324188492367197255881)
                      ·
                        rfl

theorem cell23_6394251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 1, 3].length) (baseStart_6394251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394251 prefixEnd_6394251 := by exact prefixLift 6394251
  have htrace : WordTrace (prefixWord ++ tailWord_6394251) baseStart_6394251 baseEnd_6394251 := by
    simpa [prefixWord, tailWord_6394251, baseEnd_6394251] using wordTrace_append hprefix tailTrace_6394251
  have hstable : (prefixWord ++ tailWord_6394251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394251).length < 2 ^ (prefixWord ++ tailWord_6394251).sum := by decide
  have hdescent : baseEnd_6394251 < baseStart_6394251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394285 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_6394285 : Nat := 118140960795 + 6394285 * 2 ^ 59
def prefixEnd_6394285 : Nat := 4983230072969 + 3 ^ 40 * 6394285 * 2
def baseEnd_6394285 : Nat := 3283341646834620064230725

theorem tailTrace_6394285 : CollatzResearch.WordTrace tailWord_6394285 prefixEnd_6394285 3283341646834620064230725 := by
  unfold tailWord_6394285
  simp only [CollatzResearch.WordTrace]
  refine ⟨233218733639604976780016309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155479155759736651186677539 233218733639604976780016309)
  ·
    refine ⟨21864256278712966573126529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 233218733639604976780016309 21864256278712966573126529)
    ·
      refine ⟨16398192209034724929844897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21864256278712966573126529 16398192209034724929844897)
      ·
        refine ⟨12298644156776043697383673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16398192209034724929844897 12298644156776043697383673)
        ·
          refine ⟨9223983117582032773037755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12298644156776043697383673 9223983117582032773037755)
          ·
            refine ⟨13835974676373049159556633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9223983117582032773037755 13835974676373049159556633)
            ·
              refine ⟨10376981007279786869667475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13835974676373049159556633 10376981007279786869667475)
              ·
                refine ⟨15565471510919680304501213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10376981007279786869667475 15565471510919680304501213)
                ·
                  refine ⟨5837051816594880114187955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15565471510919680304501213 5837051816594880114187955)
                  ·
                    refine ⟨8755577724892320171281933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5837051816594880114187955 8755577724892320171281933)
                    ·
                      refine ⟨3283341646834620064230725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8755577724892320171281933 3283341646834620064230725)
                      ·
                        rfl

theorem cell23_6394285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_6394285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394285 prefixEnd_6394285 := by exact prefixLift 6394285
  have htrace : WordTrace (prefixWord ++ tailWord_6394285) baseStart_6394285 baseEnd_6394285 := by
    simpa [prefixWord, tailWord_6394285, baseEnd_6394285] using wordTrace_append hprefix tailTrace_6394285
  have hstable : (prefixWord ++ tailWord_6394285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394285).length < 2 ^ (prefixWord ++ tailWord_6394285).sum := by decide
  have hdescent : baseEnd_6394285 < baseStart_6394285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394287 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 4]
def baseStart_6394287 : Nat := 118140960795 + 6394287 * 2 ^ 59
def prefixEnd_6394287 : Nat := 4983230072969 + 3 ^ 40 * 6394287 * 2
def baseEnd_6394287 : Nat := 3283342673795929056405715

theorem tailTrace_6394287 : CollatzResearch.WordTrace tailWord_6394287 prefixEnd_6394287 3283342673795929056405715 := by
  unfold tailWord_6394287
  simp only [CollatzResearch.WordTrace]
  refine ⟨233218806585597731121589115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155479204390398487414392743 233218806585597731121589115)
  ·
    refine ⟨349828209878396596682383673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233218806585597731121589115 349828209878396596682383673)
    ·
      refine ⟨262371157408797447511787755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349828209878396596682383673 262371157408797447511787755)
      ·
        refine ⟨393556736113196171267681633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262371157408797447511787755 393556736113196171267681633)
        ·
          refine ⟨295167552084897128450761225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393556736113196171267681633 295167552084897128450761225)
          ·
            refine ⟨221375664063672846338070919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295167552084897128450761225 221375664063672846338070919)
            ·
              refine ⟨332063496095509269507106379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221375664063672846338070919 332063496095509269507106379)
              ·
                refine ⟨498095244143263904260659569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332063496095509269507106379 498095244143263904260659569)
                ·
                  refine ⟨373571433107447928195494677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498095244143263904260659569 373571433107447928195494677)
                  ·
                    refine ⟨17511160926911621634163813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 373571433107447928195494677 17511160926911621634163813)
                    ·
                      refine ⟨3283342673795929056405715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17511160926911621634163813 3283342673795929056405715)
                      ·
                        rfl

theorem cell23_6394287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_6394287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394287 prefixEnd_6394287 := by exact prefixLift 6394287
  have htrace : WordTrace (prefixWord ++ tailWord_6394287) baseStart_6394287 baseEnd_6394287 := by
    simpa [prefixWord, tailWord_6394287, baseEnd_6394287] using wordTrace_append hprefix tailTrace_6394287
  have hstable : (prefixWord ++ tailWord_6394287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394287).length < 2 ^ (prefixWord ++ tailWord_6394287).sum := by decide
  have hdescent : baseEnd_6394287 < baseStart_6394287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394301 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 1, 6]
def baseStart_6394301 : Nat := 118140960795 + 6394301 * 2 ^ 59
def prefixEnd_6394301 : Nat := 4983230072969 + 3 ^ 40 * 6394301 * 2
def baseEnd_6394301 : Nat := 1094449954175030667210217

theorem tailTrace_6394301 : CollatzResearch.WordTrace tailWord_6394301 prefixEnd_6394301 1094449954175030667210217 := by
  unfold tailWord_6394301
  simp only [CollatzResearch.WordTrace]
  refine ⟨233219317207547011512598757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155479544805031341008399171 233219317207547011512598757)
  ·
    refine ⟨43728621976415064658612267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233219317207547011512598757 43728621976415064658612267)
    ·
      refine ⟨65592932964622596987918401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43728621976415064658612267 65592932964622596987918401)
      ·
        refine ⟨49194699723466947740938801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65592932964622596987918401 49194699723466947740938801)
        ·
          refine ⟨36896024792600210805704101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49194699723466947740938801 36896024792600210805704101)
          ·
            refine ⟨6918004648612539526069519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36896024792600210805704101 6918004648612539526069519)
            ·
              refine ⟨10377006972918809289104279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6918004648612539526069519 10377006972918809289104279)
              ·
                refine ⟨15565510459378213933656419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10377006972918809289104279 15565510459378213933656419)
                ·
                  refine ⟨23348265689067320900484629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15565510459378213933656419 23348265689067320900484629)
                  ·
                    refine ⟨1094449954175030667210217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23348265689067320900484629 1094449954175030667210217)
                    ·
                      rfl

theorem cell23_6394301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_6394301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394301 prefixEnd_6394301 := by exact prefixLift 6394301
  have htrace : WordTrace (prefixWord ++ tailWord_6394301) baseStart_6394301 baseEnd_6394301 := by
    simpa [prefixWord, tailWord_6394301, baseEnd_6394301] using wordTrace_append hprefix tailTrace_6394301
  have hstable : (prefixWord ++ tailWord_6394301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394301).length < 2 ^ (prefixWord ++ tailWord_6394301).sum := by decide
  have hdescent : baseEnd_6394301 < baseStart_6394301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394311 : List Nat := [1, 1, 4, 1, 1, 4, 1, 4, 1, 2, 3]
def baseStart_6394311 : Nat := 118140960795 + 6394311 * 2 ^ 59
def prefixEnd_6394311 : Nat := 4983230072969 + 3 ^ 40 * 6394311 * 2
def baseEnd_6394311 : Nat := 3283354997331636962505605

theorem tailTrace_6394311 : CollatzResearch.WordTrace tailWord_6394311 prefixEnd_6394311 3283354997331636962505605 := by
  unfold tailWord_6394311
  simp only [CollatzResearch.WordTrace]
  refine ⟨233219681937510783220462787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155479787958340522146975191 233219681937510783220462787)
  ·
    refine ⟨349829522906266174830694181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233219681937510783220462787 349829522906266174830694181)
    ·
      refine ⟨65593035544924907780755159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349829522906266174830694181 65593035544924907780755159)
      ·
        refine ⟨98389553317387361671132739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65593035544924907780755159 98389553317387361671132739)
        ·
          refine ⟨147584329976081042506699109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98389553317387361671132739 147584329976081042506699109)
          ·
            refine ⟨27672061870515195470006083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147584329976081042506699109 27672061870515195470006083)
            ·
              refine ⟨41508092805772793205009125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27672061870515195470006083 41508092805772793205009125)
              ·
                refine ⟨7782767401082398725939211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41508092805772793205009125 7782767401082398725939211)
                ·
                  refine ⟨11674151101623598088908817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7782767401082398725939211 11674151101623598088908817)
                  ·
                    refine ⟨8755613326217698566681613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11674151101623598088908817 8755613326217698566681613)
                    ·
                      refine ⟨3283354997331636962505605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8755613326217698566681613 3283354997331636962505605)
                      ·
                        rfl

theorem cell23_6394311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_6394311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394311 prefixEnd_6394311 := by exact prefixLift 6394311
  have htrace : WordTrace (prefixWord ++ tailWord_6394311) baseStart_6394311 baseEnd_6394311 := by
    simpa [prefixWord, tailWord_6394311, baseEnd_6394311] using wordTrace_append hprefix tailTrace_6394311
  have hstable : (prefixWord ++ tailWord_6394311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394311).length < 2 ^ (prefixWord ++ tailWord_6394311).sum := by decide
  have hdescent : baseEnd_6394311 < baseStart_6394311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394327 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 3, 9]
def baseStart_6394327 : Nat := 118140960795 + 6394327 * 2 ^ 59
def prefixEnd_6394327 : Nat := 4983230072969 + 3 ^ 40 * 6394327 * 2
def baseEnd_6394327 : Nat := 1094454404340702966635177

theorem tailTrace_6394327 : CollatzResearch.WordTrace tailWord_6394327 prefixEnd_6394327 1094454404340702966635177 := by
  unfold tailWord_6394327
  simp only [CollatzResearch.WordTrace]
  refine ⟨233220265505452817953045235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155480177003635211968696823 233220265505452817953045235)
  ·
    refine ⟨349830398258179226929567853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233220265505452817953045235 349830398258179226929567853)
    ·
      refine ⟨131186399346817210098587945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349830398258179226929567853 131186399346817210098587945)
      ·
        refine ⟨98389799510112907573940959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131186399346817210098587945 98389799510112907573940959)
        ·
          refine ⟨147584699265169361360911439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98389799510112907573940959 147584699265169361360911439)
          ·
            refine ⟨221377048897754042041367159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147584699265169361360911439 221377048897754042041367159)
            ·
              refine ⟨332065573346631063062050739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221377048897754042041367159 332065573346631063062050739)
              ·
                refine ⟨498098360019946594593076109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332065573346631063062050739 498098360019946594593076109)
                ·
                  refine ⟨186786885007479972972403541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498098360019946594593076109 186786885007479972972403541)
                  ·
                    refine ⟨1094454404340702966635177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 186786885007479972972403541 1094454404340702966635177)
                    ·
                      rfl

theorem cell23_6394327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_6394327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394327 prefixEnd_6394327 := by exact prefixLift 6394327
  have htrace : WordTrace (prefixWord ++ tailWord_6394327) baseStart_6394327 baseEnd_6394327 := by
    simpa [prefixWord, tailWord_6394327, baseEnd_6394327] using wordTrace_append hprefix tailTrace_6394327
  have hstable : (prefixWord ++ tailWord_6394327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394327).length < 2 ^ (prefixWord ++ tailWord_6394327).sum := by decide
  have hdescent : baseEnd_6394327 < baseStart_6394327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394351 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 3, 3, 2]
def baseStart_6394351 : Nat := 118140960795 + 6394351 * 2 ^ 59
def prefixEnd_6394351 : Nat := 4983230072969 + 3 ^ 40 * 6394351 * 2
def baseEnd_6394351 : Nat := 3283375536557816806005421

theorem tailTrace_6394351 : CollatzResearch.WordTrace tailWord_6394351 prefixEnd_6394351 3283375536557816806005421 := by
  unfold tailWord_6394351
  simp only [CollatzResearch.WordTrace]
  refine ⟨233221140857365870051918907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155480760571577246701279271 233221140857365870051918907)
  ·
    refine ⟨349831711286048805077878361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233221140857365870051918907 349831711286048805077878361)
    ·
      refine ⟨262373783464536603808408771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349831711286048805077878361 262373783464536603808408771)
      ·
        refine ⟨393560675196804905712613157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262373783464536603808408771 393560675196804905712613157)
        ·
          refine ⟨73792626599400919821114967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 393560675196804905712613157 73792626599400919821114967)
          ·
            refine ⟨110688939899101379731672451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73792626599400919821114967 110688939899101379731672451)
            ·
              refine ⟨166033409848652069597508677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110688939899101379731672451 166033409848652069597508677)
              ·
                refine ⟨31131264346622263049532877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166033409848652069597508677 31131264346622263049532877)
                ·
                  refine ⟨11674224129983348643574829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31131264346622263049532877 11674224129983348643574829)
                  ·
                    refine ⟨4377834048743755741340561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11674224129983348643574829 4377834048743755741340561)
                    ·
                      refine ⟨3283375536557816806005421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4377834048743755741340561 3283375536557816806005421)
                      ·
                        rfl

theorem cell23_6394351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 3, 2].length) (baseStart_6394351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394351 prefixEnd_6394351 := by exact prefixLift 6394351
  have htrace : WordTrace (prefixWord ++ tailWord_6394351) baseStart_6394351 baseEnd_6394351 := by
    simpa [prefixWord, tailWord_6394351, baseEnd_6394351] using wordTrace_append hprefix tailTrace_6394351
  have hstable : (prefixWord ++ tailWord_6394351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394351).length < 2 ^ (prefixWord ++ tailWord_6394351).sum := by decide
  have hdescent : baseEnd_6394351 < baseStart_6394351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394466 : List Nat := [3, 3, 2, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_6394466 : Nat := 118140960795 + 6394466 * 2 ^ 59
def prefixEnd_6394466 : Nat := 4983230072969 + 3 ^ 40 * 6394466 * 2
def baseEnd_6394466 : Nat := 3283434586833083856067393

theorem tailTrace_6394466 : CollatzResearch.WordTrace tailWord_6394466 prefixEnd_6394466 3283434586833083856067393 := by
  unfold tailWord_6394466
  simp only [CollatzResearch.WordTrace]
  refine ⟨58306333812987311173088813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155483556834632829794903501 58306333812987311173088813)
  ·
    refine ⟨21864875179870241689908305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58306333812987311173088813 21864875179870241689908305)
    ·
      refine ⟨16398656384902681267431229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21864875179870241689908305 16398656384902681267431229)
      ·
        refine ⟨6149496144338505475286711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16398656384902681267431229 6149496144338505475286711)
        ·
          refine ⟨9224244216507758212930067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6149496144338505475286711 9224244216507758212930067)
          ·
            refine ⟨13836366324761637319395101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9224244216507758212930067 13836366324761637319395101)
            ·
              refine ⟨5188637371785613994773163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13836366324761637319395101 5188637371785613994773163)
              ·
                refine ⟨7782956057678420992159745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5188637371785613994773163 7782956057678420992159745)
                ·
                  refine ⟨5837217043258815744119809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7782956057678420992159745 5837217043258815744119809)
                  ·
                    refine ⟨4377912782444111808089857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5837217043258815744119809 4377912782444111808089857)
                    ·
                      refine ⟨3283434586833083856067393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4377912782444111808089857 3283434586833083856067393)
                      ·
                        rfl

theorem cell23_6394466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_6394466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394466 prefixEnd_6394466 := by exact prefixLift 6394466
  have htrace : WordTrace (prefixWord ++ tailWord_6394466) baseStart_6394466 baseEnd_6394466 := by
    simpa [prefixWord, tailWord_6394466, baseEnd_6394466] using wordTrace_append hprefix tailTrace_6394466
  have hstable : (prefixWord ++ tailWord_6394466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394466).length < 2 ^ (prefixWord ++ tailWord_6394466).sum := by decide
  have hdescent : baseEnd_6394466 < baseStart_6394466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394528 : List Nat := [2, 1, 1, 4, 4, 1, 1, 3, 6]
def baseStart_6394528 : Nat := 118140960795 + 6394528 * 2 ^ 59
def prefixEnd_6394528 : Nat := 4983230072969 + 3 ^ 40 * 6394528 * 2
def baseEnd_6394528 : Nat := 364829602514851401499123

theorem tailTrace_6394528 : CollatzResearch.WordTrace tailWord_6394528 prefixEnd_6394528 364829602514851401499123 := by
  unfold tailWord_6394528
  simp only [CollatzResearch.WordTrace]
  refine ⟨116613798288862314640556119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155485064385149752854074825 116613798288862314640556119)
  ·
    refine ⟨174920697433293471960834179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116613798288862314640556119 174920697433293471960834179)
    ·
      refine ⟨262381046149940207941251269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174920697433293471960834179 262381046149940207941251269)
      ·
        refine ⟨49196446153113788988984613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262381046149940207941251269 49196446153113788988984613)
        ·
          refine ⟨9224333653708835435434615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49196446153113788988984613 9224333653708835435434615)
          ·
            refine ⟨13836500480563253153151923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9224333653708835435434615 13836500480563253153151923)
            ·
              refine ⟨20754750720844879729727885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13836500480563253153151923 20754750720844879729727885)
              ·
                refine ⟨7783031520316829898647957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20754750720844879729727885 7783031520316829898647957)
                ·
                  refine ⟨364829602514851401499123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7783031520316829898647957 364829602514851401499123)
                  ·
                    rfl

theorem cell23_6394528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 6].length) (baseStart_6394528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394528 prefixEnd_6394528 := by exact prefixLift 6394528
  have htrace : WordTrace (prefixWord ++ tailWord_6394528) baseStart_6394528 baseEnd_6394528 := by
    simpa [prefixWord, tailWord_6394528, baseEnd_6394528] using wordTrace_append hprefix tailTrace_6394528
  have hstable : (prefixWord ++ tailWord_6394528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394528).length < 2 ^ (prefixWord ++ tailWord_6394528).sum := by decide
  have hdescent : baseEnd_6394528 < baseStart_6394528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394542 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_6394542 : Nat := 118140960795 + 6394542 * 2 ^ 59
def prefixEnd_6394542 : Nat := 4983230072969 + 3 ^ 40 * 6394542 * 2
def baseEnd_6394542 : Nat := 3283473611362825558717043

theorem tailTrace_6394542 : CollatzResearch.WordTrace tailWord_6394542 prefixEnd_6394542 3283473611362825558717043 := by
  unfold tailWord_6394542
  simp only [CollatzResearch.WordTrace]
  refine ⟨29153513399959238709015235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155485404799782606448081253 29153513399959238709015235)
  ·
    refine ⟨43730270099938858063522853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29153513399959238709015235 43730270099938858063522853)
    ·
      refine ⟨8199425643738535886910535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43730270099938858063522853 8199425643738535886910535)
      ·
        refine ⟨12299138465607803830365803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8199425643738535886910535 12299138465607803830365803)
        ·
          refine ⟨18448707698411705745548705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12299138465607803830365803 18448707698411705745548705)
          ·
            refine ⟨13836530773808779309161529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18448707698411705745548705 13836530773808779309161529)
            ·
              refine ⟨10377398080356584481871147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13836530773808779309161529 10377398080356584481871147)
              ·
                refine ⟨15566097120534876722806721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10377398080356584481871147 15566097120534876722806721)
                ·
                  refine ⟨11674572840401157542105041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15566097120534876722806721 11674572840401157542105041)
                  ·
                    refine ⟨8755929630300868156578781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11674572840401157542105041 8755929630300868156578781)
                    ·
                      refine ⟨3283473611362825558717043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8755929630300868156578781 3283473611362825558717043)
                      ·
                        rfl

theorem cell23_6394542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_6394542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394542 prefixEnd_6394542 := by exact prefixLift 6394542
  have htrace : WordTrace (prefixWord ++ tailWord_6394542) baseStart_6394542 baseEnd_6394542 := by
    simpa [prefixWord, tailWord_6394542, baseEnd_6394542] using wordTrace_append hprefix tailTrace_6394542
  have hstable : (prefixWord ++ tailWord_6394542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394542).length < 2 ^ (prefixWord ++ tailWord_6394542).sum := by decide
  have hdescent : baseEnd_6394542 < baseStart_6394542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394566 : List Nat := [6, 1, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_6394566 : Nat := 118140960795 + 6394566 * 2 ^ 59
def prefixEnd_6394566 : Nat := 4983230072969 + 3 ^ 40 * 6394566 * 2
def baseEnd_6394566 : Nat := 1094495311632844488272311

theorem tailTrace_6394566 : CollatzResearch.WordTrace tailWord_6394566 prefixEnd_6394566 1094495311632844488272311 := by
  unfold tailWord_6394566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7288405704737092555343611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 155485988367724641180663701 7288405704737092555343611)
  ·
    refine ⟨10932608557105638833015417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7288405704737092555343611 10932608557105638833015417)
    ·
      refine ⟨8199456417829229124761563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10932608557105638833015417 8199456417829229124761563)
      ·
        refine ⟨12299184626743843687142345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8199456417829229124761563 12299184626743843687142345)
        ·
          refine ⟨9224388470057882765356759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12299184626743843687142345 9224388470057882765356759)
          ·
            refine ⟨13836582705086824148035139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9224388470057882765356759 13836582705086824148035139)
            ·
              refine ⟨20754874057630236222052709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13836582705086824148035139 20754874057630236222052709)
              ·
                refine ⟨3891538885805669291634883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20754874057630236222052709 3891538885805669291634883)
                ·
                  refine ⟨5837308328708503937452325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3891538885805669291634883 5837308328708503937452325)
                  ·
                    refine ⟨1094495311632844488272311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5837308328708503937452325 1094495311632844488272311)
                    ·
                      rfl

theorem cell23_6394566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_6394566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394566 prefixEnd_6394566 := by exact prefixLift 6394566
  have htrace : WordTrace (prefixWord ++ tailWord_6394566) baseStart_6394566 baseEnd_6394566 := by
    simpa [prefixWord, tailWord_6394566, baseEnd_6394566] using wordTrace_append hprefix tailTrace_6394566
  have hstable : (prefixWord ++ tailWord_6394566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394566).length < 2 ^ (prefixWord ++ tailWord_6394566).sum := by decide
  have hdescent : baseEnd_6394566 < baseStart_6394566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394622 : List Nat := [4, 2, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_6394622 : Nat := 118140960795 + 6394622 * 2 ^ 59
def prefixEnd_6394622 : Nat := 4983230072969 + 3 ^ 40 * 6394622 * 2
def baseEnd_6394622 : Nat := 1094504896605061748572225

theorem tailTrace_6394622 : CollatzResearch.WordTrace tailWord_6394622 prefixEnd_6394622 1094504896605061748572225 := by
  unfold tailWord_6394622
  simp only [CollatzResearch.WordTrace]
  refine ⟨29153878129923010416879265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155487350026256055556689413 29153878129923010416879265)
  ·
    refine ⟨21865408597442257812659449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29153878129923010416879265 21865408597442257812659449)
    ·
      refine ⟨16399056448081693359494587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21865408597442257812659449 16399056448081693359494587)
      ·
        refine ⟨24598584672122540039241881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16399056448081693359494587 24598584672122540039241881)
        ·
          refine ⟨18448938504091905029431411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24598584672122540039241881 18448938504091905029431411)
          ·
            refine ⟨27673407756137857544147117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18448938504091905029431411 27673407756137857544147117)
            ·
              refine ⟨10377527908551696579055169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27673407756137857544147117 10377527908551696579055169)
              ·
                refine ⟨7783145931413772434291377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10377527908551696579055169 7783145931413772434291377)
                ·
                  refine ⟨5837359448560329325718533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7783145931413772434291377 5837359448560329325718533)
                  ·
                    refine ⟨1094504896605061748572225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5837359448560329325718533 1094504896605061748572225)
                    ·
                      rfl

theorem cell23_6394622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_6394622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394622 prefixEnd_6394622 := by exact prefixLift 6394622
  have htrace : WordTrace (prefixWord ++ tailWord_6394622) baseStart_6394622 baseEnd_6394622 := by
    simpa [prefixWord, tailWord_6394622, baseEnd_6394622] using wordTrace_append hprefix tailTrace_6394622
  have hstable : (prefixWord ++ tailWord_6394622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394622).length < 2 ^ (prefixWord ++ tailWord_6394622).sum := by decide
  have hdescent : baseEnd_6394622 < baseStart_6394622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394658 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_6394658 : Nat := 118140960795 + 6394658 * 2 ^ 59
def prefixEnd_6394658 : Nat := 4983230072969 + 3 ^ 40 * 6394658 * 2
def baseEnd_6394658 : Nat := 3283533175118747104866509

theorem tailTrace_6394658 : CollatzResearch.WordTrace tailWord_6394658 prefixEnd_6394658 3283533175118747104866509 := by
  unfold tailWord_6394658
  simp only [CollatzResearch.WordTrace]
  refine ⟨58308084516813415370836157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155488225378169107655563085 58308084516813415370836157)
  ·
    refine ⟨21865531693805030764063559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58308084516813415370836157 21865531693805030764063559)
    ·
      refine ⟨32798297540707546146095339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21865531693805030764063559 32798297540707546146095339)
      ·
        refine ⟨49197446311061319219143009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32798297540707546146095339 49197446311061319219143009)
        ·
          refine ⟨36898084733295989414357257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49197446311061319219143009 36898084733295989414357257)
          ·
            refine ⟨27673563549971992060767943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36898084733295989414357257 27673563549971992060767943)
            ·
              refine ⟨41510345324957988091151915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27673563549971992060767943 41510345324957988091151915)
              ·
                refine ⟨62265517987436982136727873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41510345324957988091151915 62265517987436982136727873)
                ·
                  refine ⟨46699138490577736602545905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62265517987436982136727873 46699138490577736602545905)
                  ·
                    refine ⟨35024353867933302451909429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46699138490577736602545905 35024353867933302451909429)
                    ·
                      refine ⟨3283533175118747104866509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35024353867933302451909429 3283533175118747104866509)
                      ·
                        rfl

theorem cell23_6394658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_6394658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394658 prefixEnd_6394658 := by exact prefixLift 6394658
  have htrace : WordTrace (prefixWord ++ tailWord_6394658) baseStart_6394658 baseEnd_6394658 := by
    simpa [prefixWord, tailWord_6394658, baseEnd_6394658] using wordTrace_append hprefix tailTrace_6394658
  have hstable : (prefixWord ++ tailWord_6394658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394658).length < 2 ^ (prefixWord ++ tailWord_6394658).sum := by decide
  have hdescent : baseEnd_6394658 < baseStart_6394658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394745 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 2, 5, 2]
def baseStart_6394745 : Nat := 118140960795 + 6394745 * 2 ^ 59
def prefixEnd_6394745 : Nat := 4983230072969 + 3 ^ 40 * 6394745 * 2
def baseEnd_6394745 : Nat := 3283577847935688264478609

theorem tailTrace_6394745 : CollatzResearch.WordTrace tailWord_6394745 prefixEnd_6394745 3283577847935688264478609 := by
  unfold tailWord_6394745
  simp only [CollatzResearch.WordTrace]
  refine ⟨233235511217938475341761689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155490340811958983561174459 233235511217938475341761689)
  ·
    refine ⟨174926633413453856506321267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233235511217938475341761689 174926633413453856506321267)
    ·
      refine ⟨262389950120180784759481901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174926633413453856506321267 262389950120180784759481901)
      ·
        refine ⟨98396231295067794284805713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262389950120180784759481901 98396231295067794284805713)
        ·
          refine ⟨73797173471300845713604285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98396231295067794284805713 73797173471300845713604285)
          ·
            refine ⟨27673940051737817142601607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73797173471300845713604285 27673940051737817142601607)
            ·
              refine ⟨41510910077606725713902411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27673940051737817142601607 41510910077606725713902411)
              ·
                refine ⟨62266365116410088570853617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41510910077606725713902411 62266365116410088570853617)
                ·
                  refine ⟨46699773837307566428140213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62266365116410088570853617 46699773837307566428140213)
                  ·
                    refine ⟨4378103797247584352638145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46699773837307566428140213 4378103797247584352638145)
                    ·
                      refine ⟨3283577847935688264478609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4378103797247584352638145 3283577847935688264478609)
                      ·
                        rfl

theorem cell23_6394745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_6394745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394745 prefixEnd_6394745 := by exact prefixLift 6394745
  have htrace : WordTrace (prefixWord ++ tailWord_6394745) baseStart_6394745 baseEnd_6394745 := by
    simpa [prefixWord, tailWord_6394745, baseEnd_6394745] using wordTrace_append hprefix tailTrace_6394745
  have hstable : (prefixWord ++ tailWord_6394745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394745).length < 2 ^ (prefixWord ++ tailWord_6394745).sum := by decide
  have hdescent : baseEnd_6394745 < baseStart_6394745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394775 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 1, 6, 2]
def baseStart_6394775 : Nat := 118140960795 + 6394775 * 2 ^ 59
def prefixEnd_6394775 : Nat := 4983230072969 + 3 ^ 40 * 6394775 * 2
def baseEnd_6394775 : Nat := 3283593252355323147103471

theorem tailTrace_6394775 : CollatzResearch.WordTrace tailWord_6394775 prefixEnd_6394775 3283593252355323147103471 := by
  unfold tailWord_6394775
  simp only [CollatzResearch.WordTrace]
  refine ⟨233236605407829790465353779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155491070271886526976902519 233236605407829790465353779)
  ·
    refine ⟨349854908111744685698030669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233236605407829790465353779 349854908111744685698030669)
    ·
      refine ⟨131195590541904257136761501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349854908111744685698030669 131195590541904257136761501)
      ·
        refine ⟨49198346453214096426285563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131195590541904257136761501 49198346453214096426285563)
        ·
          refine ⟨73797519679821144639428345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49198346453214096426285563 73797519679821144639428345)
          ·
            refine ⟨55348139759865858479571259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73797519679821144639428345 55348139759865858479571259)
            ·
              refine ⟨83022209639798787719356889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55348139759865858479571259 83022209639798787719356889)
              ·
                refine ⟨62266657229849090789517667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83022209639798787719356889 62266657229849090789517667)
                ·
                  refine ⟨93399985844773636184276501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62266657229849090789517667 93399985844773636184276501)
                  ·
                    refine ⟨4378124336473764196137961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93399985844773636184276501 4378124336473764196137961)
                    ·
                      refine ⟨3283593252355323147103471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4378124336473764196137961 3283593252355323147103471)
                      ·
                        rfl

theorem cell23_6394775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_6394775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394775 prefixEnd_6394775 := by exact prefixLift 6394775
  have htrace : WordTrace (prefixWord ++ tailWord_6394775) baseStart_6394775 baseEnd_6394775 := by
    simpa [prefixWord, tailWord_6394775, baseEnd_6394775] using wordTrace_append hprefix tailTrace_6394775
  have hstable : (prefixWord ++ tailWord_6394775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394775).length < 2 ^ (prefixWord ++ tailWord_6394775).sum := by decide
  have hdescent : baseEnd_6394775 < baseStart_6394775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394788 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_6394788 : Nat := 118140960795 + 6394788 * 2 ^ 59
def prefixEnd_6394788 : Nat := 4983230072969 + 3 ^ 40 * 6394788 * 2
def baseEnd_6394788 : Nat := 3283599927603831596240911

theorem tailTrace_6394788 : CollatzResearch.WordTrace tailWord_6394788 prefixEnd_6394788 3283599927603831596240911 := by
  unfold tailWord_6394788
  simp only [CollatzResearch.WordTrace]
  refine ⟨116618539778391346842788509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155491386371188462457051345 116618539778391346842788509)
  ·
    refine ⟨43731952416896755066045691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116618539778391346842788509 43731952416896755066045691)
    ·
      refine ⟨65597928625345132599068537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43731952416896755066045691 65597928625345132599068537)
      ·
        refine ⟨49198446469008849449301403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65597928625345132599068537 49198446469008849449301403)
        ·
          refine ⟨73797669703513274173952105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49198446469008849449301403 73797669703513274173952105)
          ·
            refine ⟨55348252277634955630464079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73797669703513274173952105 55348252277634955630464079)
            ·
              refine ⟨83022378416452433445696119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55348252277634955630464079 83022378416452433445696119)
              ·
                refine ⟨124533567624678650168544179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83022378416452433445696119 124533567624678650168544179)
                ·
                  refine ⟨186800351437017975252816269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124533567624678650168544179 186800351437017975252816269)
                  ·
                    refine ⟨70050131788881740719806101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 186800351437017975252816269 70050131788881740719806101)
                    ·
                      refine ⟨3283599927603831596240911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70050131788881740719806101 3283599927603831596240911)
                      ·
                        rfl

theorem cell23_6394788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_6394788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394788 prefixEnd_6394788 := by exact prefixLift 6394788
  have htrace : WordTrace (prefixWord ++ tailWord_6394788) baseStart_6394788 baseEnd_6394788 := by
    simpa [prefixWord, tailWord_6394788, baseEnd_6394788] using wordTrace_append hprefix tailTrace_6394788
  have hstable : (prefixWord ++ tailWord_6394788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394788).length < 2 ^ (prefixWord ++ tailWord_6394788).sum := by decide
  have hdescent : baseEnd_6394788 < baseStart_6394788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394836 : List Nat := [2, 4, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_6394836 : Nat := 118140960795 + 6394836 * 2 ^ 59
def prefixEnd_6394836 : Nat := 4983230072969 + 3 ^ 40 * 6394836 * 2
def baseEnd_6394836 : Nat := 1094541524891749136146897

theorem tailTrace_6394836 : CollatzResearch.WordTrace tailWord_6394836 prefixEnd_6394836 1094541524891749136146897 := by
  unfold tailWord_6394836
  simp only [CollatzResearch.WordTrace]
  refine ⟨116619415130304398941662181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155492553507072531922216241 116619415130304398941662181)
  ·
    refine ⟨21866140336932074801561659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116619415130304398941662181 21866140336932074801561659)
    ·
      refine ⟨32799210505398112202342489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21866140336932074801561659 32799210505398112202342489)
      ·
        refine ⟨24599407879048584151756867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32799210505398112202342489 24599407879048584151756867)
        ·
          refine ⟨36899111818572876227635301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24599407879048584151756867 36899111818572876227635301)
          ·
            refine ⟨6918583465982414292681619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36899111818572876227635301 6918583465982414292681619)
            ·
              refine ⟨10377875198973621439022429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6918583465982414292681619 10377875198973621439022429)
              ·
                refine ⟨3891703199615108039633411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10377875198973621439022429 3891703199615108039633411)
                ·
                  refine ⟨5837554799422662059450117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3891703199615108039633411 5837554799422662059450117)
                  ·
                    refine ⟨1094541524891749136146897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5837554799422662059450117 1094541524891749136146897)
                    ·
                      rfl

theorem cell23_6394836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_6394836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394836 prefixEnd_6394836 := by exact prefixLift 6394836
  have htrace : WordTrace (prefixWord ++ tailWord_6394836) baseStart_6394836 baseEnd_6394836 := by
    simpa [prefixWord, tailWord_6394836, baseEnd_6394836] using wordTrace_append hprefix tailTrace_6394836
  have hstable : (prefixWord ++ tailWord_6394836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394836).length < 2 ^ (prefixWord ++ tailWord_6394836).sum := by decide
  have hdescent : baseEnd_6394836 < baseStart_6394836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394853 : List Nat := [1, 3, 1, 6, 1, 1, 3, 2, 1, 4]
def baseStart_6394853 : Nat := 118140960795 + 6394853 * 2 ^ 59
def prefixEnd_6394853 : Nat := 4983230072969 + 3 ^ 40 * 6394853 * 2
def baseEnd_6394853 : Nat := 1094544434615457947309371

theorem tailTrace_6394853 : CollatzResearch.WordTrace tailWord_6394853 prefixEnd_6394853 1094544434615457947309371 := by
  unfold tailWord_6394853
  simp only [CollatzResearch.WordTrace]
  refine ⟨233239450301547209786693213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155492966867698139857795475 233239450301547209786693213)
  ·
    refine ⟨87464793863080203670009955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233239450301547209786693213 87464793863080203670009955)
    ·
      refine ⟨131197190794620305505014933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87464793863080203670009955 131197190794620305505014933)
      ·
        refine ⟨6149868318497826820547575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 131197190794620305505014933 6149868318497826820547575)
        ·
          refine ⟨9224802477746740230821363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6149868318497826820547575 9224802477746740230821363)
          ·
            refine ⟨13837203716620110346232045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9224802477746740230821363 13837203716620110346232045)
            ·
              refine ⟨5188951393732541379837017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13837203716620110346232045 5188951393732541379837017)
              ·
                refine ⟨3891713545299406034877763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5188951393732541379837017 3891713545299406034877763)
                ·
                  refine ⟨5837570317949109052316645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3891713545299406034877763 5837570317949109052316645)
                  ·
                    refine ⟨1094544434615457947309371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5837570317949109052316645 1094544434615457947309371)
                    ·
                      rfl

theorem cell23_6394853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 1, 4].length) (baseStart_6394853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394853 prefixEnd_6394853 := by exact prefixLift 6394853
  have htrace : WordTrace (prefixWord ++ tailWord_6394853) baseStart_6394853 baseEnd_6394853 := by
    simpa [prefixWord, tailWord_6394853, baseEnd_6394853] using wordTrace_append hprefix tailTrace_6394853
  have hstable : (prefixWord ++ tailWord_6394853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394853).length < 2 ^ (prefixWord ++ tailWord_6394853).sum := by decide
  have hdescent : baseEnd_6394853 < baseStart_6394853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394866 : List Nat := [3, 2, 1, 5, 1, 2, 2, 1, 6]
def baseStart_6394866 : Nat := 118140960795 + 6394866 * 2 ^ 59
def prefixEnd_6394866 : Nat := 4983230072969 + 3 ^ 40 * 6394866 * 2
def baseEnd_6394866 : Nat := 364848886566098032340617

theorem tailTrace_6394866 : CollatzResearch.WordTrace tailWord_6394866 prefixEnd_6394866 364848886566098032340617 := by
  unfold tailWord_6394866
  simp only [CollatzResearch.WordTrace]
  refine ⟨58309981112625028251729113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155493282967000075337944301 58309981112625028251729113)
  ·
    refine ⟨43732485834468771188796835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58309981112625028251729113 43732485834468771188796835)
    ·
      refine ⟨65598728751703156783195253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43732485834468771188796835 65598728751703156783195253)
      ·
        refine ⟨6149880820472170948424555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65598728751703156783195253 6149880820472170948424555)
        ·
          refine ⟨9224821230708256422636833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6149880820472170948424555 9224821230708256422636833)
          ·
            refine ⟨6918615923031192316977625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9224821230708256422636833 6918615923031192316977625)
            ·
              refine ⟨5188961942273394237733219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6918615923031192316977625 5188961942273394237733219)
              ·
                refine ⟨7783442913410091356599829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5188961942273394237733219 7783442913410091356599829)
                ·
                  refine ⟨364848886566098032340617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7783442913410091356599829 364848886566098032340617)
                  ·
                    rfl

theorem cell23_6394866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_6394866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394866 prefixEnd_6394866 := by exact prefixLift 6394866
  have htrace : WordTrace (prefixWord ++ tailWord_6394866) baseStart_6394866 baseEnd_6394866 := by
    simpa [prefixWord, tailWord_6394866, baseEnd_6394866] using wordTrace_append hprefix tailTrace_6394866
  have hstable : (prefixWord ++ tailWord_6394866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394866).length < 2 ^ (prefixWord ++ tailWord_6394866).sum := by decide
  have hdescent : baseEnd_6394866 < baseStart_6394866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394919 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_6394919 : Nat := 118140960795 + 6394919 * 2 ^ 59
def prefixEnd_6394919 : Nat := 4983230072969 + 3 ^ 40 * 6394919 * 2
def baseEnd_6394919 : Nat := 3283667193569570583702809

theorem tailTrace_6394919 : CollatzResearch.WordTrace tailWord_6394919 prefixEnd_6394919 3283667193569570583702809 := by
  unfold tailWord_6394919
  simp only [CollatzResearch.WordTrace]
  refine ⟨233241857519308103058595811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155494571679538735372397207 233241857519308103058595811)
  ·
    refine ⟨349862786278962154587893717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233241857519308103058595811 349862786278962154587893717)
    ·
      refine ⟨8199909053413175498153759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 349862786278962154587893717 8199909053413175498153759)
      ·
        refine ⟨12299863580119763247230639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8199909053413175498153759 12299863580119763247230639)
        ·
          refine ⟨18449795370179644870845959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12299863580119763247230639 18449795370179644870845959)
          ·
            refine ⟨27674693055269467306268939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18449795370179644870845959 27674693055269467306268939)
            ·
              refine ⟨41512039582904200959403409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27674693055269467306268939 41512039582904200959403409)
              ·
                refine ⟨31134029687178150719552557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41512039582904200959403409 31134029687178150719552557)
                ·
                  refine ⟨11675261132691806519832209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31134029687178150719552557 11675261132691806519832209)
                  ·
                    refine ⟨8756445849518854889874157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11675261132691806519832209 8756445849518854889874157)
                    ·
                      refine ⟨3283667193569570583702809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8756445849518854889874157 3283667193569570583702809)
                      ·
                        rfl

theorem cell23_6394919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_6394919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394919 prefixEnd_6394919 := by exact prefixLift 6394919
  have htrace : WordTrace (prefixWord ++ tailWord_6394919) baseStart_6394919 baseEnd_6394919 := by
    simpa [prefixWord, tailWord_6394919, baseEnd_6394919] using wordTrace_append hprefix tailTrace_6394919
  have hstable : (prefixWord ++ tailWord_6394919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394919).length < 2 ^ (prefixWord ++ tailWord_6394919).sum := by decide
  have hdescent : baseEnd_6394919 < baseStart_6394919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394950 : List Nat := [6, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_6394950 : Nat := 118140960795 + 6394950 * 2 ^ 59
def prefixEnd_6394950 : Nat := 4983230072969 + 3 ^ 40 * 6394950 * 2
def baseEnd_6394950 : Nat := 3283683111469859962415167

theorem tailTrace_6394950 : CollatzResearch.WordTrace tailWord_6394950 prefixEnd_6394950 3283683111469859962415167 := by
  unfold tailWord_6394950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7288843380693618604780447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 155495325454797196901982869 7288843380693618604780447)
  ·
    refine ⟨10933265071040427907170671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7288843380693618604780447 10933265071040427907170671)
    ·
      refine ⟨16399897606560641860756007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10933265071040427907170671 16399897606560641860756007)
      ·
        refine ⟨24599846409840962791134011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16399897606560641860756007 24599846409840962791134011)
        ·
          refine ⟨36899769614761444186701017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24599846409840962791134011 36899769614761444186701017)
          ·
            refine ⟨27674827211071083140025763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36899769614761444186701017 27674827211071083140025763)
            ·
              refine ⟨41512240816606624710038645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27674827211071083140025763 41512240816606624710038645)
              ·
                refine ⟨3891772576556871066566123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41512240816606624710038645 3891772576556871066566123)
                ·
                  refine ⟨5837658864835306599849185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3891772576556871066566123 5837658864835306599849185)
                  ·
                    refine ⟨4378244148626479949886889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5837658864835306599849185 4378244148626479949886889)
                    ·
                      refine ⟨3283683111469859962415167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4378244148626479949886889 3283683111469859962415167)
                      ·
                        rfl

theorem cell23_6394950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_6394950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394950 prefixEnd_6394950 := by exact prefixLift 6394950
  have htrace : WordTrace (prefixWord ++ tailWord_6394950) baseStart_6394950 baseEnd_6394950 := by
    simpa [prefixWord, tailWord_6394950, baseEnd_6394950] using wordTrace_append hprefix tailTrace_6394950
  have hstable : (prefixWord ++ tailWord_6394950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394950).length < 2 ^ (prefixWord ++ tailWord_6394950).sum := by decide
  have hdescent : baseEnd_6394950 < baseStart_6394950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6394965 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 4, 6]
def baseStart_6394965 : Nat := 118140960795 + 6394965 * 2 ^ 59
def prefixEnd_6394965 : Nat := 4983230072969 + 3 ^ 40 * 6394965 * 2
def baseEnd_6394965 : Nat := 1094563604559892467909199

theorem tailTrace_6394965 : CollatzResearch.WordTrace tailWord_6394965 prefixEnd_6394965 1094563604559892467909199 := by
  unfold tailWord_6394965
  simp only [CollatzResearch.WordTrace]
  refine ⟨233243535277141452914770349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155495690184760968609846899 233243535277141452914770349)
  ·
    refine ⟨87466325728928044843038881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233243535277141452914770349 87466325728928044843038881)
    ·
      refine ⟨65599744296696033632279161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87466325728928044843038881 65599744296696033632279161)
      ·
        refine ⟨49199808222522025224209371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65599744296696033632279161 49199808222522025224209371)
        ·
          refine ⟨73799712333783037836314057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49199808222522025224209371 73799712333783037836314057)
          ·
            refine ⟨55349784250337278377235543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73799712333783037836314057 55349784250337278377235543)
            ·
              refine ⟨83024676375505917565853315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55349784250337278377235543 83024676375505917565853315)
              ·
                refine ⟨124537014563258876348779973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83024676375505917565853315 124537014563258876348779973)
                ·
                  refine ⟨23350690230611039315396245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124537014563258876348779973 23350690230611039315396245)
                  ·
                    refine ⟨1094563604559892467909199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23350690230611039315396245 1094563604559892467909199)
                    ·
                      rfl

theorem cell23_6394965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_6394965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6394965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6394965 prefixEnd_6394965 := by exact prefixLift 6394965
  have htrace : WordTrace (prefixWord ++ tailWord_6394965) baseStart_6394965 baseEnd_6394965 := by
    simpa [prefixWord, tailWord_6394965, baseEnd_6394965] using wordTrace_append hprefix tailTrace_6394965
  have hstable : (prefixWord ++ tailWord_6394965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6394965).length < 2 ^ (prefixWord ++ tailWord_6394965).sum := by decide
  have hdescent : baseEnd_6394965 < baseStart_6394965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6394965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395055 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 2, 8]
def baseStart_6395055 : Nat := 118140960795 + 6395055 * 2 ^ 59
def prefixEnd_6395055 : Nat := 4983230072969 + 3 ^ 40 * 6395055 * 2
def baseEnd_6395055 : Nat := 1094579008979527350534061

theorem tailTrace_6395055 : CollatzResearch.WordTrace tailWord_6395055 prefixEnd_6395055 1094579008979527350534061 := by
  unfold tailWord_6395055
  simp only [CollatzResearch.WordTrace]
  refine ⟨233246817846815398285546619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155497878564543598857031079 233246817846815398285546619)
  ·
    refine ⟨349870226770223097428319929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233246817846815398285546619 349870226770223097428319929)
    ·
      refine ⟨262402670077667323071239947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349870226770223097428319929 262402670077667323071239947)
      ·
        refine ⟨393604005116500984606859921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262402670077667323071239947 393604005116500984606859921)
        ·
          refine ⟨295203003837375738455144941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393604005116500984606859921 295203003837375738455144941)
          ·
            refine ⟨110701126439015901920679353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295203003837375738455144941 110701126439015901920679353)
            ·
              refine ⟨83025844829261926440509515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110701126439015901920679353 83025844829261926440509515)
              ·
                refine ⟨124538767243892889660764273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83025844829261926440509515 124538767243892889660764273)
                ·
                  refine ⟨93404075432919667245573205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124538767243892889660764273 93404075432919667245573205)
                  ·
                    refine ⟨1094579008979527350534061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93404075432919667245573205 1094579008979527350534061)
                    ·
                      rfl

theorem cell23_6395055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 8].length) (baseStart_6395055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395055 prefixEnd_6395055 := by exact prefixLift 6395055
  have htrace : WordTrace (prefixWord ++ tailWord_6395055) baseStart_6395055 baseEnd_6395055 := by
    simpa [prefixWord, tailWord_6395055, baseEnd_6395055] using wordTrace_append hprefix tailTrace_6395055
  have hstable : (prefixWord ++ tailWord_6395055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395055).length < 2 ^ (prefixWord ++ tailWord_6395055).sum := by decide
  have hdescent : baseEnd_6395055 < baseStart_6395055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395096 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 2, 4, 2]
def baseStart_6395096 : Nat := 118140960795 + 6395096 * 2 ^ 59
def prefixEnd_6395096 : Nat := 4983230072969 + 3 ^ 40 * 6395096 * 2
def baseEnd_6395096 : Nat := 3283758079645416391189495

theorem tailTrace_6395096 : CollatzResearch.WordTrace tailWord_6395096 prefixEnd_6395096 3283758079645416391189495 := by
  unfold tailWord_6395096
  simp only [CollatzResearch.WordTrace]
  refine ⟨116624156619833431143894571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155498875493111241525192761 116624156619833431143894571)
  ·
    refine ⟨174936234929750146715841857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116624156619833431143894571 174936234929750146715841857)
    ·
      refine ⟨131202176197312610036881393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174936234929750146715841857 131202176197312610036881393)
      ·
        refine ⟨98401632147984457527661045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131202176197312610036881393 98401632147984457527661045)
        ·
          refine ⟨9225153013873542893218223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98401632147984457527661045 9225153013873542893218223)
          ·
            refine ⟨13837729520810314339827335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9225153013873542893218223 13837729520810314339827335)
            ·
              refine ⟨20756594281215471509741003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13837729520810314339827335 20756594281215471509741003)
              ·
                refine ⟨31134891421823207264611505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20756594281215471509741003 31134891421823207264611505)
                ·
                  refine ⟨23351168566367405448458629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31134891421823207264611505 23351168566367405448458629)
                  ·
                    refine ⟨4378344106193888521585993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23351168566367405448458629 4378344106193888521585993)
                    ·
                      refine ⟨3283758079645416391189495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4378344106193888521585993 3283758079645416391189495)
                      ·
                        rfl

theorem cell23_6395096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_6395096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395096 prefixEnd_6395096 := by exact prefixLift 6395096
  have htrace : WordTrace (prefixWord ++ tailWord_6395096) baseStart_6395096 baseEnd_6395096 := by
    simpa [prefixWord, tailWord_6395096, baseEnd_6395096] using wordTrace_append hprefix tailTrace_6395096
  have hstable : (prefixWord ++ tailWord_6395096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395096).length < 2 ^ (prefixWord ++ tailWord_6395096).sum := by decide
  have hdescent : baseEnd_6395096 < baseStart_6395096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395116 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 3]
def baseStart_6395116 : Nat := 118140960795 + 6395116 * 2 ^ 59
def prefixEnd_6395116 : Nat := 4983230072969 + 3 ^ 40 * 6395116 * 2
def baseEnd_6395116 : Nat := 3283768349258506312939403

theorem tailTrace_6395116 : CollatzResearch.WordTrace tailWord_6395116 prefixEnd_6395116 3283768349258506312939403 := by
  unfold tailWord_6395116
  simp only [CollatzResearch.WordTrace]
  refine ⟨116624521349797202851758601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155499361799729603802344801 116624521349797202851758601)
  ·
    refine ⟨87468391012347902138818951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116624521349797202851758601 87468391012347902138818951)
    ·
      refine ⟨131202586518521853208228427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87468391012347902138818951 131202586518521853208228427)
      ·
        refine ⟨196803879777782779812342641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131202586518521853208228427 196803879777782779812342641)
        ·
          refine ⟨147602909833337084859256981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196803879777782779812342641 147602909833337084859256981)
          ·
            refine ⟨6918886398437675852777671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 147602909833337084859256981 6918886398437675852777671)
            ·
              refine ⟨10378329597656513779166507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6918886398437675852777671 10378329597656513779166507)
              ·
                refine ⟨15567494396484770668749761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10378329597656513779166507 15567494396484770668749761)
                ·
                  refine ⟨11675620797363578001562321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15567494396484770668749761 11675620797363578001562321)
                  ·
                    refine ⟨8756715598022683501171741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11675620797363578001562321 8756715598022683501171741)
                    ·
                      refine ⟨3283768349258506312939403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8756715598022683501171741 3283768349258506312939403)
                      ·
                        rfl

theorem cell23_6395116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_6395116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395116 prefixEnd_6395116 := by exact prefixLift 6395116
  have htrace : WordTrace (prefixWord ++ tailWord_6395116) baseStart_6395116 baseEnd_6395116 := by
    simpa [prefixWord, tailWord_6395116, baseEnd_6395116] using wordTrace_append hprefix tailTrace_6395116
  have hstable : (prefixWord ++ tailWord_6395116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395116).length < 2 ^ (prefixWord ++ tailWord_6395116).sum := by decide
  have hdescent : baseEnd_6395116 < baseStart_6395116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395129 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 5, 1, 3]
def baseStart_6395129 : Nat := 118140960795 + 6395129 * 2 ^ 59
def prefixEnd_6395129 : Nat := 4983230072969 + 3 ^ 40 * 6395129 * 2
def baseEnd_6395129 : Nat := 3283775024507014762076843

theorem tailTrace_6395129 : CollatzResearch.WordTrace tailWord_6395129 prefixEnd_6395129 3283775024507014762076843 := by
  unfold tailWord_6395129
  simp only [CollatzResearch.WordTrace]
  refine ⟨233249516848547308923740441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155499677899031539282493627 233249516848547308923740441)
  ·
    refine ⟨174937137636410481692805331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233249516848547308923740441 174937137636410481692805331)
    ·
      refine ⟨262405706454615722539207997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174937137636410481692805331 262405706454615722539207997)
      ·
        refine ⟨98402139920480895952202999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262405706454615722539207997 98402139920480895952202999)
        ·
          refine ⟨147603209880721343928304499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98402139920480895952202999 147603209880721343928304499)
          ·
            refine ⟨221404814821082015892456749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147603209880721343928304499 221404814821082015892456749)
            ·
              refine ⟨83026805557905755959671281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221404814821082015892456749 83026805557905755959671281)
              ·
                refine ⟨62270104168429316969753461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83026805557905755959671281 62270104168429316969753461)
                ·
                  refine ⟨5837822265790248465914387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62270104168429316969753461 5837822265790248465914387)
                  ·
                    refine ⟨8756733398685372698871581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5837822265790248465914387 8756733398685372698871581)
                    ·
                      refine ⟨3283775024507014762076843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8756733398685372698871581 3283775024507014762076843)
                      ·
                        rfl

theorem cell23_6395129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_6395129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395129 prefixEnd_6395129 := by exact prefixLift 6395129
  have htrace : WordTrace (prefixWord ++ tailWord_6395129) baseStart_6395129 baseEnd_6395129 := by
    simpa [prefixWord, tailWord_6395129, baseEnd_6395129] using wordTrace_append hprefix tailTrace_6395129
  have hstable : (prefixWord ++ tailWord_6395129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395129).length < 2 ^ (prefixWord ++ tailWord_6395129).sum := by decide
  have hdescent : baseEnd_6395129 < baseStart_6395129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395169 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 1, 8, 2]
def baseStart_6395169 : Nat := 118140960795 + 6395169 * 2 ^ 59
def prefixEnd_6395169 : Nat := 4983230072969 + 3 ^ 40 * 6395169 * 2
def baseEnd_6395169 : Nat := 3283795563733194605576659

theorem tailTrace_6395169 : CollatzResearch.WordTrace tailWord_6395169 prefixEnd_6395169 3283795563733194605576659 := by
  unfold tailWord_6395169
  simp only [CollatzResearch.WordTrace]
  refine ⟨233250975768402395755196561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155500650512268263836797707 233250975768402395755196561)
  ·
    refine ⟨174938231826301796816397421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233250975768402395755196561 174938231826301796816397421)
    ·
      refine ⟨65601836934863173806149033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174938231826301796816397421 65601836934863173806149033)
      ·
        refine ⟨49201377701147380354611775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65601836934863173806149033 49201377701147380354611775)
        ·
          refine ⟨73802066551721070531917663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49201377701147380354611775 73802066551721070531917663)
          ·
            refine ⟨110703099827581605797876495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73802066551721070531917663 110703099827581605797876495)
            ·
              refine ⟨166054649741372408696814743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110703099827581605797876495 166054649741372408696814743)
              ·
                refine ⟨249081974612058613045222115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166054649741372408696814743 249081974612058613045222115)
                ·
                  refine ⟨373622961918087919567833173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249081974612058613045222115 373622961918087919567833173)
                  ·
                    refine ⟨4378394084977592807435545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 373622961918087919567833173 4378394084977592807435545)
                    ·
                      refine ⟨3283795563733194605576659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4378394084977592807435545 3283795563733194605576659)
                      ·
                        rfl

theorem cell23_6395169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_6395169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395169 prefixEnd_6395169 := by exact prefixLift 6395169
  have htrace : WordTrace (prefixWord ++ tailWord_6395169) baseStart_6395169 baseEnd_6395169 := by
    simpa [prefixWord, tailWord_6395169, baseEnd_6395169] using wordTrace_append hprefix tailTrace_6395169
  have hstable : (prefixWord ++ tailWord_6395169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395169).length < 2 ^ (prefixWord ++ tailWord_6395169).sum := by decide
  have hdescent : baseEnd_6395169 < baseStart_6395169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395186 : List Nat := [3, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4]
def baseStart_6395186 : Nat := 118140960795 + 6395186 * 2 ^ 59
def prefixEnd_6395186 : Nat := 4983230072969 + 3 ^ 40 * 6395186 * 2
def baseEnd_6395186 : Nat := 3283804292904321039064081

theorem tailTrace_6395186 : CollatzResearch.WordTrace tailWord_6395186 prefixEnd_6395186 3283804292904321039064081 := by
  unfold tailWord_6395186
  simp only [CollatzResearch.WordTrace]
  refine ⟨58312898952335201914641353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155501063872893871772376941 58312898952335201914641353)
  ·
    refine ⟨43734674214251401435981015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58312898952335201914641353 43734674214251401435981015)
    ·
      refine ⟨65602011321377102153971523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43734674214251401435981015 65602011321377102153971523)
      ·
        refine ⟨98403016982065653230957285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65602011321377102153971523 98403016982065653230957285)
        ·
          refine ⟨18450565684137309980804491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98403016982065653230957285 18450565684137309980804491)
          ·
            refine ⟨27675848526205964971206737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18450565684137309980804491 27675848526205964971206737)
            ·
              refine ⟨20756886394654473728405053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27675848526205964971206737 20756886394654473728405053)
              ·
                refine ⟨7783832397995427648151895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20756886394654473728405053 7783832397995427648151895)
                ·
                  refine ⟨11675748596993141472227843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7783832397995427648151895 11675748596993141472227843)
                  ·
                    refine ⟨17513622895489712208341765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11675748596993141472227843 17513622895489712208341765)
                    ·
                      refine ⟨3283804292904321039064081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17513622895489712208341765 3283804292904321039064081)
                      ·
                        rfl

theorem cell23_6395186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_6395186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395186 prefixEnd_6395186 := by exact prefixLift 6395186
  have htrace : WordTrace (prefixWord ++ tailWord_6395186) baseStart_6395186 baseEnd_6395186 := by
    simpa [prefixWord, tailWord_6395186, baseEnd_6395186] using wordTrace_append hprefix tailTrace_6395186
  have hstable : (prefixWord ++ tailWord_6395186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395186).length < 2 ^ (prefixWord ++ tailWord_6395186).sum := by decide
  have hdescent : baseEnd_6395186 < baseStart_6395186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395189 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_6395189 : Nat := 118140960795 + 6395189 * 2 ^ 59
def prefixEnd_6395189 : Nat := 4983230072969 + 3 ^ 40 * 6395189 * 2
def baseEnd_6395189 : Nat := 3283805833346284527326567

theorem tailTrace_6395189 : CollatzResearch.WordTrace tailWord_6395189 prefixEnd_6395189 3283805833346284527326567 := by
  unfold tailWord_6395189
  simp only [CollatzResearch.WordTrace]
  refine ⟨233251705228329939170924621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155501136818886626113949747 233251705228329939170924621)
  ·
    refine ⟨87469389460623727189096733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233251705228329939170924621 87469389460623727189096733)
    ·
      refine ⟨32801021047733897695911275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87469389460623727189096733 32801021047733897695911275)
      ·
        refine ⟨49201531571600846543866913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32801021047733897695911275 49201531571600846543866913)
        ·
          refine ⟨36901148678700634907900185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49201531571600846543866913 36901148678700634907900185)
          ·
            refine ⟨27675861509025476180925139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36901148678700634907900185 27675861509025476180925139)
            ·
              refine ⟨41513792263538214271387709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27675861509025476180925139 41513792263538214271387709)
              ·
                refine ⟨15567672098826830351770391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41513792263538214271387709 15567672098826830351770391)
                ·
                  refine ⟨23351508148240245527655587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15567672098826830351770391 23351508148240245527655587)
                  ·
                    refine ⟨35027262222360368291483381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23351508148240245527655587 35027262222360368291483381)
                    ·
                      refine ⟨3283805833346284527326567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35027262222360368291483381 3283805833346284527326567)
                      ·
                        rfl

theorem cell23_6395189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_6395189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395189 prefixEnd_6395189 := by exact prefixLift 6395189
  have htrace : WordTrace (prefixWord ++ tailWord_6395189) baseStart_6395189 baseEnd_6395189 := by
    simpa [prefixWord, tailWord_6395189, baseEnd_6395189] using wordTrace_append hprefix tailTrace_6395189
  have hstable : (prefixWord ++ tailWord_6395189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395189).length < 2 ^ (prefixWord ++ tailWord_6395189).sum := by decide
  have hdescent : baseEnd_6395189 < baseStart_6395189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395197 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 3, 1, 3]
def baseStart_6395197 : Nat := 118140960795 + 6395197 * 2 ^ 59
def prefixEnd_6395197 : Nat := 4983230072969 + 3 ^ 40 * 6395197 * 2
def baseEnd_6395197 : Nat := 3283809941191520496026531

theorem tailTrace_6395197 : CollatzResearch.WordTrace tailWord_6395197 prefixEnd_6395197 3283809941191520496026531 := by
  unfold tailWord_6395197
  simp only [CollatzResearch.WordTrace]
  refine ⟨233251997012300956537215845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155501331341533971024810563 233251997012300956537215845)
  ·
    refine ⟨43734749439806429350727971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233251997012300956537215845 43734749439806429350727971)
    ·
      refine ⟨65602124159709644026091957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43734749439806429350727971 65602124159709644026091957)
      ·
        refine ⟨6150199139972779127446121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65602124159709644026091957 6150199139972779127446121)
        ·
          refine ⟨4612649354979584345584591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6150199139972779127446121 4612649354979584345584591)
          ·
            refine ⟨6918974032469376518376887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4612649354979584345584591 6918974032469376518376887)
            ·
              refine ⟨10378461048704064777565331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6918974032469376518376887 10378461048704064777565331)
              ·
                refine ⟨15567691573056097166347997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10378461048704064777565331 15567691573056097166347997)
                ·
                  refine ⟨5837884339896036437380499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15567691573056097166347997 5837884339896036437380499)
                  ·
                    refine ⟨8756826509844054656070749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5837884339896036437380499 8756826509844054656070749)
                    ·
                      refine ⟨3283809941191520496026531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8756826509844054656070749 3283809941191520496026531)
                      ·
                        rfl

theorem cell23_6395197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_6395197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395197 prefixEnd_6395197 := by exact prefixLift 6395197
  have htrace : WordTrace (prefixWord ++ tailWord_6395197) baseStart_6395197 baseEnd_6395197 := by
    simpa [prefixWord, tailWord_6395197, baseEnd_6395197] using wordTrace_append hprefix tailTrace_6395197
  have hstable : (prefixWord ++ tailWord_6395197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395197).length < 2 ^ (prefixWord ++ tailWord_6395197).sum := by decide
  have hdescent : baseEnd_6395197 < baseStart_6395197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395219 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 3]
def baseStart_6395219 : Nat := 118140960795 + 6395219 * 2 ^ 59
def prefixEnd_6395219 : Nat := 4983230072969 + 3 ^ 40 * 6395219 * 2
def baseEnd_6395219 : Nat := 3283821237765919409951429

theorem tailTrace_6395219 : CollatzResearch.WordTrace tailWord_6395219 prefixEnd_6395219 3283821237765919409951429 := by
  unfold tailWord_6395219
  simp only [CollatzResearch.WordTrace]
  refine ⟨233252799418221254294516711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155501866278814169529677807 233252799418221254294516711)
  ·
    refine ⟨349879199127331881441775067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233252799418221254294516711 349879199127331881441775067)
    ·
      refine ⟨524818798690997822162662601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349879199127331881441775067 524818798690997822162662601)
      ·
        refine ⟨393614099018248366621996951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524818798690997822162662601 393614099018248366621996951)
        ·
          refine ⟨590421148527372549932995427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393614099018248366621996951 590421148527372549932995427)
          ·
            refine ⟨885631722791058824899493141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590421148527372549932995427 885631722791058824899493141)
            ·
              refine ⟨41513987005830882417163741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 885631722791058824899493141 41513987005830882417163741)
              ·
                refine ⟨15567745127186580906436403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41513987005830882417163741 15567745127186580906436403)
                ·
                  refine ⟨23351617690779871359654605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15567745127186580906436403 23351617690779871359654605)
                  ·
                    refine ⟨8756856634042451759870477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23351617690779871359654605 8756856634042451759870477)
                    ·
                      refine ⟨3283821237765919409951429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8756856634042451759870477 3283821237765919409951429)
                      ·
                        rfl

theorem cell23_6395219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 3].length) (baseStart_6395219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395219 prefixEnd_6395219 := by exact prefixLift 6395219
  have htrace : WordTrace (prefixWord ++ tailWord_6395219) baseStart_6395219 baseEnd_6395219 := by
    simpa [prefixWord, tailWord_6395219, baseEnd_6395219] using wordTrace_append hprefix tailTrace_6395219
  have hstable : (prefixWord ++ tailWord_6395219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395219).length < 2 ^ (prefixWord ++ tailWord_6395219).sum := by decide
  have hdescent : baseEnd_6395219 < baseStart_6395219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395223 : List Nat := [1, 1, 3, 2, 3, 4, 1, 2, 1, 2, 3]
def baseStart_6395223 : Nat := 118140960795 + 6395223 * 2 ^ 59
def prefixEnd_6395223 : Nat := 4983230072969 + 3 ^ 40 * 6395223 * 2
def baseEnd_6395223 : Nat := 3283823291688537394301411

theorem tailTrace_6395223 : CollatzResearch.WordTrace tailWord_6395223 prefixEnd_6395223 3283823291688537394301411 := by
  unfold tailWord_6395223
  simp only [CollatzResearch.WordTrace]
  refine ⟨233252945310206762977662323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155501963540137841985108215 233252945310206762977662323)
  ·
    refine ⟨349879417965310144466493485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233252945310206762977662323 349879417965310144466493485)
    ·
      refine ⟨131204781736991304174935057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349879417965310144466493485 131204781736991304174935057)
      ·
        refine ⟨98403586302743478131201293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131204781736991304174935057 98403586302743478131201293)
        ·
          refine ⟨36901344863528804299200485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98403586302743478131201293 36901344863528804299200485)
          ·
            refine ⟨6919002161911650806100091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36901344863528804299200485 6919002161911650806100091)
            ·
              refine ⟨10378503242867476209150137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6919002161911650806100091 10378503242867476209150137)
              ·
                refine ⟨7783877432150607156862603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10378503242867476209150137 7783877432150607156862603)
                ·
                  refine ⟨11675816148225910735293905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7783877432150607156862603 11675816148225910735293905)
                  ·
                    refine ⟨8756862111169433051470429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11675816148225910735293905 8756862111169433051470429)
                    ·
                      refine ⟨3283823291688537394301411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8756862111169433051470429 3283823291688537394301411)
                      ·
                        rfl

theorem cell23_6395223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_6395223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395223 prefixEnd_6395223 := by exact prefixLift 6395223
  have htrace : WordTrace (prefixWord ++ tailWord_6395223) baseStart_6395223 baseEnd_6395223 := by
    simpa [prefixWord, tailWord_6395223, baseEnd_6395223] using wordTrace_append hprefix tailTrace_6395223
  have hstable : (prefixWord ++ tailWord_6395223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395223).length < 2 ^ (prefixWord ++ tailWord_6395223).sum := by decide
  have hdescent : baseEnd_6395223 < baseStart_6395223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395236 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 1, 3, 3]
def baseStart_6395236 : Nat := 118140960795 + 6395236 * 2 ^ 59
def prefixEnd_6395236 : Nat := 4983230072969 + 3 ^ 40 * 6395236 * 2
def baseEnd_6395236 : Nat := 3283829966937045843438851

theorem tailTrace_6395236 : CollatzResearch.WordTrace tailWord_6395236 prefixEnd_6395236 3283829966937045843438851 := by
  unfold tailWord_6395236
  simp only [CollatzResearch.WordTrace]
  refine ⟨116626709729579833098942781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155502279639439777465257041 116626709729579833098942781)
  ·
    refine ⟨43735016148592437412103543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116626709729579833098942781 43735016148592437412103543)
    ·
      refine ⟨65602524222888656118155315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43735016148592437412103543 65602524222888656118155315)
      ·
        refine ⟨98403786334332984177232973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65602524222888656118155315 98403786334332984177232973)
        ·
          refine ⟨36901419875374869066462365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98403786334332984177232973 36901419875374869066462365)
          ·
            refine ⟨13838032453265575899923387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36901419875374869066462365 13838032453265575899923387)
            ·
              refine ⟨20757048679898363849885081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13838032453265575899923387 20757048679898363849885081)
              ·
                refine ⟨15567786509923772887413811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20757048679898363849885081 15567786509923772887413811)
                ·
                  refine ⟨23351679764885659331120717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15567786509923772887413811 23351679764885659331120717)
                  ·
                    refine ⟨8756879911832122249170269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23351679764885659331120717 8756879911832122249170269)
                    ·
                      refine ⟨3283829966937045843438851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8756879911832122249170269 3283829966937045843438851)
                      ·
                        rfl

theorem cell23_6395236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_6395236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395236 prefixEnd_6395236 := by exact prefixLift 6395236
  have htrace : WordTrace (prefixWord ++ tailWord_6395236) baseStart_6395236 baseEnd_6395236 := by
    simpa [prefixWord, tailWord_6395236, baseEnd_6395236] using wordTrace_append hprefix tailTrace_6395236
  have hstable : (prefixWord ++ tailWord_6395236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395236).length < 2 ^ (prefixWord ++ tailWord_6395236).sum := by decide
  have hdescent : baseEnd_6395236 < baseStart_6395236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395240 : List Nat := [2, 1, 4, 2, 3, 1, 3, 1, 1, 2, 3]
def baseStart_6395240 : Nat := 118140960795 + 6395240 * 2 ^ 59
def prefixEnd_6395240 : Nat := 4983230072969 + 3 ^ 40 * 6395240 * 2
def baseEnd_6395240 : Nat := 3283832020859663827788833

theorem tailTrace_6395240 : CollatzResearch.WordTrace tailWord_6395240 prefixEnd_6395240 3283832020859663827788833 := by
  unfold tailWord_6395240
  simp only [CollatzResearch.WordTrace]
  refine ⟨116626782675572587440515587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155502376900763449920687449 116626782675572587440515587)
  ·
    refine ⟨174940174013358881160773381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116626782675572587440515587 174940174013358881160773381)
    ·
      refine ⟨32801282627504790217645009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174940174013358881160773381 32801282627504790217645009)
      ·
        refine ⟨24600961970628592663233757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32801282627504790217645009 24600961970628592663233757)
        ·
          refine ⟨9225360738985722248712659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24600961970628592663233757 9225360738985722248712659)
          ·
            refine ⟨13838041108478583373068989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9225360738985722248712659 13838041108478583373068989)
            ·
              refine ⟨5189265415679468764900871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13838041108478583373068989 5189265415679468764900871)
              ·
                refine ⟨7783898123519203147351307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5189265415679468764900871 7783898123519203147351307)
                ·
                  refine ⟨11675847185278804721026961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7783898123519203147351307 11675847185278804721026961)
                  ·
                    refine ⟨8756885388959103540770221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11675847185278804721026961 8756885388959103540770221)
                    ·
                      refine ⟨3283832020859663827788833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8756885388959103540770221 3283832020859663827788833)
                      ·
                        rfl

theorem cell23_6395240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_6395240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395240 prefixEnd_6395240 := by exact prefixLift 6395240
  have htrace : WordTrace (prefixWord ++ tailWord_6395240) baseStart_6395240 baseEnd_6395240 := by
    simpa [prefixWord, tailWord_6395240, baseEnd_6395240] using wordTrace_append hprefix tailTrace_6395240
  have hstable : (prefixWord ++ tailWord_6395240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395240).length < 2 ^ (prefixWord ++ tailWord_6395240).sum := by decide
  have hdescent : baseEnd_6395240 < baseStart_6395240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395293 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 1, 4, 2]
def baseStart_6395293 : Nat := 118140960795 + 6395293 * 2 ^ 59
def prefixEnd_6395293 : Nat := 4983230072969 + 3 ^ 40 * 6395293 * 2
def baseEnd_6395293 : Nat := 3283859235334352120426089

theorem tailTrace_6395293 : CollatzResearch.WordTrace tailWord_6395293 prefixEnd_6395293 3283859235334352120426089 := by
  unfold tailWord_6395293
  simp only [CollatzResearch.WordTrace]
  refine ⟨233255498419953164932710533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155503665613302109955140355 233255498419953164932710533)
  ·
    refine ⟨43735405953741218424883225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233255498419953164932710533 43735405953741218424883225)
    ·
      refine ⟨32801554465305913818662419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43735405953741218424883225 32801554465305913818662419)
      ·
        refine ⟨49202331697958870727993629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32801554465305913818662419 49202331697958870727993629)
        ·
          refine ⟨18450874386734576522997611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49202331697958870727993629 18450874386734576522997611)
          ·
            refine ⟨27676311580101864784496417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18450874386734576522997611 27676311580101864784496417)
            ·
              refine ⟨20757233685076398588372313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27676311580101864784496417 20757233685076398588372313)
              ·
                refine ⟨15567925263807298941279235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20757233685076398588372313 15567925263807298941279235)
                ·
                  refine ⟨23351887895710948411918853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15567925263807298941279235 23351887895710948411918853)
                  ·
                    refine ⟨4378478980445802827234785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23351887895710948411918853 4378478980445802827234785)
                    ·
                      refine ⟨3283859235334352120426089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4378478980445802827234785 3283859235334352120426089)
                      ·
                        rfl

theorem cell23_6395293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_6395293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395293 prefixEnd_6395293 := by exact prefixLift 6395293
  have htrace : WordTrace (prefixWord ++ tailWord_6395293) baseStart_6395293 baseEnd_6395293 := by
    simpa [prefixWord, tailWord_6395293, baseEnd_6395293] using wordTrace_append hprefix tailTrace_6395293
  have hstable : (prefixWord ++ tailWord_6395293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395293).length < 2 ^ (prefixWord ++ tailWord_6395293).sum := by decide
  have hdescent : baseEnd_6395293 < baseStart_6395293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395304 : List Nat := [2, 1, 6, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_6395304 : Nat := 118140960795 + 6395304 * 2 ^ 59
def prefixEnd_6395304 : Nat := 4983230072969 + 3 ^ 40 * 6395304 * 2
def baseEnd_6395304 : Nat := 3283864883621551577388539

theorem tailTrace_6395304 : CollatzResearch.WordTrace tailWord_6395304 prefixEnd_6395304 3283864883621551577388539 := by
  unfold tailWord_6395304
  simp only [CollatzResearch.WordTrace]
  refine ⟨116627949811456656905680483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155503933081942209207573977 116627949811456656905680483)
  ·
    refine ⟨174941924717184985358520725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116627949811456656905680483 174941924717184985358520725)
    ·
      refine ⟨8200402721118046188680659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 174941924717184985358520725 8200402721118046188680659)
      ·
        refine ⟨12300604081677069283020989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8200402721118046188680659 12300604081677069283020989)
        ·
          refine ⟨4612726530628900981132871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12300604081677069283020989 4612726530628900981132871)
          ·
            refine ⟨6919089795943351471699307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4612726530628900981132871 6919089795943351471699307)
            ·
              refine ⟨10378634693915027207548961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6919089795943351471699307 10378634693915027207548961)
              ·
                refine ⟨7783976020436270405661721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10378634693915027207548961 7783976020436270405661721)
                ·
                  refine ⟨5837982015327202804246291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7783976020436270405661721 5837982015327202804246291)
                  ·
                    refine ⟨8756973022990804206369437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5837982015327202804246291 8756973022990804206369437)
                    ·
                      refine ⟨3283864883621551577388539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8756973022990804206369437 3283864883621551577388539)
                      ·
                        rfl

theorem cell23_6395304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_6395304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395304 prefixEnd_6395304 := by exact prefixLift 6395304
  have htrace : WordTrace (prefixWord ++ tailWord_6395304) baseStart_6395304 baseEnd_6395304 := by
    simpa [prefixWord, tailWord_6395304, baseEnd_6395304] using wordTrace_append hprefix tailTrace_6395304
  have hstable : (prefixWord ++ tailWord_6395304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395304).length < 2 ^ (prefixWord ++ tailWord_6395304).sum := by decide
  have hdescent : baseEnd_6395304 < baseStart_6395304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395350 : List Nat := [5, 2, 1, 1, 1, 2, 3, 3, 5]
def baseStart_6395350 : Nat := 118140960795 + 6395350 * 2 ^ 59
def prefixEnd_6395350 : Nat := 4983230072969 + 3 ^ 40 * 6395350 * 2
def baseEnd_6395350 : Nat := 364876500414628710823703

theorem tailTrace_6395350 : CollatzResearch.WordTrace tailWord_6395350 prefixEnd_6395350 364876500414628710823703 := by
  unfold tailWord_6395350
  simp only [CollatzResearch.WordTrace]
  refine ⟨14578598586296666479220969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155505051587164442445023669 14578598586296666479220969)
  ·
    refine ⟨10933948939722499859415727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14578598586296666479220969 10933948939722499859415727)
    ·
      refine ⟨16400923409583749789123591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10933948939722499859415727 16400923409583749789123591)
      ·
        refine ⟨24601385114375624683685387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16400923409583749789123591 24601385114375624683685387)
        ·
          refine ⟨36902077671563437025528081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24601385114375624683685387 36902077671563437025528081)
          ·
            refine ⟨27676558253672577769146061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36902077671563437025528081 27676558253672577769146061)
            ·
              refine ⟨10378709345127216663429773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27676558253672577769146061 10378709345127216663429773)
              ·
                refine ⟨3892016004422706248786165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10378709345127216663429773 3892016004422706248786165)
                ·
                  refine ⟨364876500414628710823703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3892016004422706248786165 364876500414628710823703)
                  ·
                    rfl

theorem cell23_6395350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_6395350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395350 prefixEnd_6395350 := by exact prefixLift 6395350
  have htrace : WordTrace (prefixWord ++ tailWord_6395350) baseStart_6395350 baseEnd_6395350 := by
    simpa [prefixWord, tailWord_6395350, baseEnd_6395350] using wordTrace_append hprefix tailTrace_6395350
  have hstable : (prefixWord ++ tailWord_6395350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395350).length < 2 ^ (prefixWord ++ tailWord_6395350).sum := by decide
  have hdescent : baseEnd_6395350 < baseStart_6395350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395373 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_6395373 : Nat := 118140960795 + 6395373 * 2 ^ 59
def prefixEnd_6395373 : Nat := 4983230072969 + 3 ^ 40 * 6395373 * 2
def baseEnd_6395373 : Nat := 3283900313786711807425721

theorem tailTrace_6395373 : CollatzResearch.WordTrace tailWord_6395373 prefixEnd_6395373 3283900313786711807425721 := by
  unfold tailWord_6395373
  simp only [CollatzResearch.WordTrace]
  refine ⟨233258416259663338595622773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155505610839775559063748515 233258416259663338595622773)
  ·
    refine ⟨21867976524343437993339635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 233258416259663338595622773 21867976524343437993339635)
    ·
      refine ⟨32801964786515156990009453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21867976524343437993339635 32801964786515156990009453)
      ·
        refine ⟨12300736794943183871253545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32801964786515156990009453 12300736794943183871253545)
        ·
          refine ⟨9225552596207387903440159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12300736794943183871253545 9225552596207387903440159)
          ·
            refine ⟨13838328894311081855160239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9225552596207387903440159 13838328894311081855160239)
            ·
              refine ⟨20757493341466622782740359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13838328894311081855160239 20757493341466622782740359)
              ·
                refine ⟨31136240012199934174110539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20757493341466622782740359 31136240012199934174110539)
                ·
                  refine ⟨46704360018299901261165809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31136240012199934174110539 46704360018299901261165809)
                  ·
                    refine ⟨35028270013724925945874357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46704360018299901261165809 35028270013724925945874357)
                    ·
                      refine ⟨3283900313786711807425721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35028270013724925945874357 3283900313786711807425721)
                      ·
                        rfl

theorem cell23_6395373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_6395373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395373 prefixEnd_6395373 := by exact prefixLift 6395373
  have htrace : WordTrace (prefixWord ++ tailWord_6395373) baseStart_6395373 baseEnd_6395373 := by
    simpa [prefixWord, tailWord_6395373, baseEnd_6395373] using wordTrace_append hprefix tailTrace_6395373
  have hstable : (prefixWord ++ tailWord_6395373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395373).length < 2 ^ (prefixWord ++ tailWord_6395373).sum := by decide
  have hdescent : baseEnd_6395373 < baseStart_6395373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395379 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4]
def baseStart_6395379 : Nat := 118140960795 + 6395379 * 2 ^ 59
def prefixEnd_6395379 : Nat := 4983230072969 + 3 ^ 40 * 6395379 * 2
def baseEnd_6395379 : Nat := 3283903394670638783950693

theorem tailTrace_6395379 : CollatzResearch.WordTrace tailWord_6395379 prefixEnd_6395379 3283903394670638783950693 := by
  unfold tailWord_6395379
  simp only [CollatzResearch.WordTrace]
  refine ⟨233258635097641601620341191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155505756731761067746894127 233258635097641601620341191)
  ·
    refine ⟨349887952646462402430511787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233258635097641601620341191 349887952646462402430511787)
    ·
      refine ⟨524831928969693603645767681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349887952646462402430511787 524831928969693603645767681)
      ·
        refine ⟨393623946727270202734325761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524831928969693603645767681 393623946727270202734325761)
        ·
          refine ⟨295217960045452652050744321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393623946727270202734325761 295217960045452652050744321)
          ·
            refine ⟨221413470034089489038058241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295217960045452652050744321 221413470034089489038058241)
            ·
              refine ⟨166060102525567116778543681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221413470034089489038058241 166060102525567116778543681)
              ·
                refine ⟨124545076894175337583907761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166060102525567116778543681 124545076894175337583907761)
                ·
                  refine ⟨93408807670631503187930821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124545076894175337583907761 93408807670631503187930821)
                  ·
                    refine ⟨17514151438243406847737029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93408807670631503187930821 17514151438243406847737029)
                    ·
                      refine ⟨3283903394670638783950693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17514151438243406847737029 3283903394670638783950693)
                      ·
                        rfl

theorem cell23_6395379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_6395379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395379 prefixEnd_6395379 := by exact prefixLift 6395379
  have htrace : WordTrace (prefixWord ++ tailWord_6395379) baseStart_6395379 baseEnd_6395379 := by
    simpa [prefixWord, tailWord_6395379, baseEnd_6395379] using wordTrace_append hprefix tailTrace_6395379
  have hstable : (prefixWord ++ tailWord_6395379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395379).length < 2 ^ (prefixWord ++ tailWord_6395379).sum := by decide
  have hdescent : baseEnd_6395379 < baseStart_6395379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395386 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3]
def baseStart_6395386 : Nat := 118140960795 + 6395386 * 2 ^ 59
def prefixEnd_6395386 : Nat := 4983230072969 + 3 ^ 40 * 6395386 * 2
def baseEnd_6395386 : Nat := 3283906989035220256563161

theorem tailTrace_6395386 : CollatzResearch.WordTrace tailWord_6395386 prefixEnd_6395386 3283906989035220256563161 := by
  unfold tailWord_6395386
  simp only [CollatzResearch.WordTrace]
  refine ⟨58314722602154060453961503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155505926939077494543897341 58314722602154060453961503)
  ·
    refine ⟨87472083903231090680942255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58314722602154060453961503 87472083903231090680942255)
    ·
      refine ⟨131208125854846636021413383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87472083903231090680942255 131208125854846636021413383)
      ·
        refine ⟨196812188782269954032120075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131208125854846636021413383 196812188782269954032120075)
        ·
          refine ⟨295218283173404931048180113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196812188782269954032120075 295218283173404931048180113)
          ·
            refine ⟨221413712380053698286135085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295218283173404931048180113 221413712380053698286135085)
            ·
              refine ⟨83030142142520136857300657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221413712380053698286135085 83030142142520136857300657)
              ·
                refine ⟨62272606606890102642975493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83030142142520136857300657 62272606606890102642975493)
                ·
                  refine ⟨11676113738791894245557905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62272606606890102642975493 11676113738791894245557905)
                  ·
                    refine ⟨8757085304093920684168429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11676113738791894245557905 8757085304093920684168429)
                    ·
                      refine ⟨3283906989035220256563161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8757085304093920684168429 3283906989035220256563161)
                      ·
                        rfl

theorem cell23_6395386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_6395386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395386 prefixEnd_6395386 := by exact prefixLift 6395386
  have htrace : WordTrace (prefixWord ++ tailWord_6395386) baseStart_6395386 baseEnd_6395386 := by
    simpa [prefixWord, tailWord_6395386, baseEnd_6395386] using wordTrace_append hprefix tailTrace_6395386
  have hstable : (prefixWord ++ tailWord_6395386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395386).length < 2 ^ (prefixWord ++ tailWord_6395386).sum := by decide
  have hdescent : baseEnd_6395386 < baseStart_6395386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395466 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 1, 6]
def baseStart_6395466 : Nat := 118140960795 + 6395466 * 2 ^ 59
def prefixEnd_6395466 : Nat := 4983230072969 + 3 ^ 40 * 6395466 * 2
def baseEnd_6395466 : Nat := 1094649355829193314520931

theorem tailTrace_6395466 : CollatzResearch.WordTrace tailWord_6395466 prefixEnd_6395466 1094649355829193314520931 := by
  unfold tailWord_6395466
  simp only [CollatzResearch.WordTrace]
  refine ⟨58315452062081603869689563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155507872165550943652505501 58315452062081603869689563)
  ·
    refine ⟨87473178093122405804534345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58315452062081603869689563 87473178093122405804534345)
    ·
      refine ⟨65604883569841804353400759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87473178093122405804534345 65604883569841804353400759)
      ·
        refine ⟨98407325354762706530101139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65604883569841804353400759 98407325354762706530101139)
        ·
          refine ⟨147610988032144059795151709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98407325354762706530101139 147610988032144059795151709)
          ·
            refine ⟨55354120512054022423181891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147610988032144059795151709 55354120512054022423181891)
            ·
              refine ⟨83031180768081033634772837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55354120512054022423181891 83031180768081033634772837)
              ·
                refine ⟨15568346394015193806519907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83031180768081033634772837 15568346394015193806519907)
                ·
                  refine ⟨23352519591022790709779861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15568346394015193806519907 23352519591022790709779861)
                  ·
                    refine ⟨1094649355829193314520931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23352519591022790709779861 1094649355829193314520931)
                    ·
                      rfl

theorem cell23_6395466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_6395466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395466 prefixEnd_6395466 := by exact prefixLift 6395466
  have htrace : WordTrace (prefixWord ++ tailWord_6395466) baseStart_6395466 baseEnd_6395466 := by
    simpa [prefixWord, tailWord_6395466, baseEnd_6395466] using wordTrace_append hprefix tailTrace_6395466
  have hstable : (prefixWord ++ tailWord_6395466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395466).length < 2 ^ (prefixWord ++ tailWord_6395466).sum := by decide
  have hdescent : baseEnd_6395466 < baseStart_6395466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395473 : List Nat := [1, 2, 2, 1, 3, 2, 3, 3, 1, 1, 4]
def baseStart_6395473 : Nat := 118140960795 + 6395473 * 2 ^ 59
def prefixEnd_6395473 : Nat := 4983230072969 + 3 ^ 40 * 6395473 * 2
def baseEnd_6395473 : Nat := 3283951661852161416175261

theorem tailTrace_6395473 : CollatzResearch.WordTrace tailWord_6395473 prefixEnd_6395473 3283951661852161416175261 := by
  unfold tailWord_6395473
  simp only [CollatzResearch.WordTrace]
  refine ⟨233262063559301055674263073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155508042372867370449508715 233262063559301055674263073)
  ·
    refine ⟨174946547669475791755697305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233262063559301055674263073 174946547669475791755697305)
    ·
      refine ⟨131209910752106843816772979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174946547669475791755697305 131209910752106843816772979)
      ·
        refine ⟨196814866128160265725159469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131209910752106843816772979 196814866128160265725159469)
        ·
          refine ⟨73805574798060099646934801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196814866128160265725159469 73805574798060099646934801)
          ·
            refine ⟨55354181098545074735201101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73805574798060099646934801 55354181098545074735201101)
            ·
              refine ⟨20757817911954403025700413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55354181098545074735201101 20757817911954403025700413)
              ·
                refine ⟨7784181716982901134637655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20757817911954403025700413 7784181716982901134637655)
                ·
                  refine ⟨11676272575474351701956483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7784181716982901134637655 11676272575474351701956483)
                  ·
                    refine ⟨17514408863211527552934725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11676272575474351701956483 17514408863211527552934725)
                    ·
                      refine ⟨3283951661852161416175261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17514408863211527552934725 3283951661852161416175261)
                      ·
                        rfl

theorem cell23_6395473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_6395473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395473 prefixEnd_6395473 := by exact prefixLift 6395473
  have htrace : WordTrace (prefixWord ++ tailWord_6395473) baseStart_6395473 baseEnd_6395473 := by
    simpa [prefixWord, tailWord_6395473, baseEnd_6395473] using wordTrace_append hprefix tailTrace_6395473
  have hstable : (prefixWord ++ tailWord_6395473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395473).length < 2 ^ (prefixWord ++ tailWord_6395473).sum := by decide
  have hdescent : baseEnd_6395473 < baseStart_6395473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395493 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 1, 1, 5]
def baseStart_6395493 : Nat := 118140960795 + 6395493 * 2 ^ 59
def prefixEnd_6395493 : Nat := 4983230072969 + 3 ^ 40 * 6395493 * 2
def baseEnd_6395493 : Nat := 3283961931465251337925169

theorem tailTrace_6395493 : CollatzResearch.WordTrace tailWord_6395493 prefixEnd_6395493 3283961931465251337925169 := by
  unfold tailWord_6395493
  simp only [CollatzResearch.WordTrace]
  refine ⟨233262793019228599089991133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155508528679485732726660755 233262793019228599089991133)
  ·
    refine ⟨87473547382210724658746675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233262793019228599089991133 87473547382210724658746675)
    ·
      refine ⟨131210321073316086988120013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87473547382210724658746675 131210321073316086988120013)
      ·
        refine ⟨49203870402493532620545005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131210321073316086988120013 49203870402493532620545005)
        ·
          refine ⟨18451451400935074732704377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49203870402493532620545005 18451451400935074732704377)
          ·
            refine ⟨13838588550701306049528283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18451451400935074732704377 13838588550701306049528283)
            ·
              refine ⟨20757882826051959074292425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13838588550701306049528283 20757882826051959074292425)
              ·
                refine ⟨15568412119538969305719319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20757882826051959074292425 15568412119538969305719319)
                ·
                  refine ⟨23352618179308453958578979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15568412119538969305719319 23352618179308453958578979)
                  ·
                    refine ⟨35028927268962680937868469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23352618179308453958578979 35028927268962680937868469)
                    ·
                      refine ⟨3283961931465251337925169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35028927268962680937868469 3283961931465251337925169)
                      ·
                        rfl

theorem cell23_6395493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_6395493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395493 prefixEnd_6395493 := by exact prefixLift 6395493
  have htrace : WordTrace (prefixWord ++ tailWord_6395493) baseStart_6395493 baseEnd_6395493 := by
    simpa [prefixWord, tailWord_6395493, baseEnd_6395493] using wordTrace_append hprefix tailTrace_6395493
  have hstable : (prefixWord ++ tailWord_6395493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395493).length < 2 ^ (prefixWord ++ tailWord_6395493).sum := by decide
  have hdescent : baseEnd_6395493 < baseStart_6395493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395551 : List Nat := [1, 1, 2, 7, 2, 1, 2, 1, 2, 4]
def baseStart_6395551 : Nat := 118140960795 + 6395551 * 2 ^ 59
def prefixEnd_6395551 : Nat := 4983230072969 + 3 ^ 40 * 6395551 * 2
def baseEnd_6395551 : Nat := 1094663904447737370333301

theorem tailTrace_6395551 : CollatzResearch.WordTrace tailWord_6395551 prefixEnd_6395551 1094663904447737370333301 := by
  unfold tailWord_6395551
  simp only [CollatzResearch.WordTrace]
  refine ⟨233264908453018474995602507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155509938968678983330401671 233264908453018474995602507)
  ·
    refine ⟨349897362679527712493403761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233264908453018474995602507 349897362679527712493403761)
    ·
      refine ⟨262423022009645784370052821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349897362679527712493403761 262423022009645784370052821)
      ·
        refine ⟨6150539578351073071173113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 262423022009645784370052821 6150539578351073071173113)
        ·
          refine ⟨4612904683763304803379835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6150539578351073071173113 4612904683763304803379835)
          ·
            refine ⟨6919357025644957205069753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4612904683763304803379835 6919357025644957205069753)
            ·
              refine ⟨5189517769233717903802315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6919357025644957205069753 5189517769233717903802315)
              ·
                refine ⟨7784276653850576855703473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5189517769233717903802315 7784276653850576855703473)
                ·
                  refine ⟨5838207490387932641777605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7784276653850576855703473 5838207490387932641777605)
                  ·
                    refine ⟨1094663904447737370333301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5838207490387932641777605 1094663904447737370333301)
                    ·
                      rfl

theorem cell23_6395551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 2, 4].length) (baseStart_6395551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395551 prefixEnd_6395551 := by exact prefixLift 6395551
  have htrace : WordTrace (prefixWord ++ tailWord_6395551) baseStart_6395551 baseEnd_6395551 := by
    simpa [prefixWord, tailWord_6395551, baseEnd_6395551] using wordTrace_append hprefix tailTrace_6395551
  have hstable : (prefixWord ++ tailWord_6395551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395551).length < 2 ^ (prefixWord ++ tailWord_6395551).sum := by decide
  have hdescent : baseEnd_6395551 < baseStart_6395551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395557 : List Nat := [1, 3, 1, 2, 1, 2, 6, 1, 2, 1, 3]
def baseStart_6395557 : Nat := 118140960795 + 6395557 * 2 ^ 59
def prefixEnd_6395557 : Nat := 4983230072969 + 3 ^ 40 * 6395557 * 2
def baseEnd_6395557 : Nat := 3283994794227139087524875

theorem tailTrace_6395557 : CollatzResearch.WordTrace tailWord_6395557 prefixEnd_6395557 3283994794227139087524875 := by
  unfold tailWord_6395557
  simp only [CollatzResearch.WordTrace]
  refine ⟨233265127290996738020320925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155510084860664492013547283 233265127290996738020320925)
  ·
    refine ⟨87474422734123776757620347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233265127290996738020320925 87474422734123776757620347)
    ·
      refine ⟨131211634101185665136430521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87474422734123776757620347 131211634101185665136430521)
      ·
        refine ⟨98408725575889248852322891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131211634101185665136430521 98408725575889248852322891)
        ·
          refine ⟨147613088363833873278484337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98408725575889248852322891 147613088363833873278484337)
          ·
            refine ⟨110709816272875404958863253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147613088363833873278484337 110709816272875404958863253)
            ·
              refine ⟨5189522637791034607446715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110709816272875404958863253 5189522637791034607446715)
              ·
                refine ⟨7784283956686551911170073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5189522637791034607446715 7784283956686551911170073)
                ·
                  refine ⟨5838212967514913933377555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7784283956686551911170073 5838212967514913933377555)
                  ·
                    refine ⟨8757319451272370900066333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5838212967514913933377555 8757319451272370900066333)
                    ·
                      refine ⟨3283994794227139087524875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8757319451272370900066333 3283994794227139087524875)
                      ·
                        rfl

theorem cell23_6395557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_6395557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395557 prefixEnd_6395557 := by exact prefixLift 6395557
  have htrace : WordTrace (prefixWord ++ tailWord_6395557) baseStart_6395557 baseEnd_6395557 := by
    simpa [prefixWord, tailWord_6395557, baseEnd_6395557] using wordTrace_append hprefix tailTrace_6395557
  have hstable : (prefixWord ++ tailWord_6395557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395557).length < 2 ^ (prefixWord ++ tailWord_6395557).sum := by decide
  have hdescent : baseEnd_6395557 < baseStart_6395557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395580 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 3, 4, 2]
def baseStart_6395580 : Nat := 118140960795 + 6395580 * 2 ^ 59
def prefixEnd_6395580 : Nat := 4983230072969 + 3 ^ 40 * 6395580 * 2
def baseEnd_6395580 : Nat := 3284006604282192497537269

theorem tailTrace_6395580 : CollatzResearch.WordTrace tailWord_6395580 prefixEnd_6395580 3284006604282192497537269 := by
  unfold tailWord_6395580
  simp only [CollatzResearch.WordTrace]
  refine ⟨116632983084956706474204097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155510644113275608632272129 116632983084956706474204097)
  ·
    refine ⟨87474737313717529855653073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116632983084956706474204097 87474737313717529855653073)
    ·
      refine ⟨65606052985288147391739805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87474737313717529855653073 65606052985288147391739805)
      ·
        refine ⟨24602269869483055271902427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65606052985288147391739805 24602269869483055271902427)
        ·
          refine ⟨36903404804224582907853641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24602269869483055271902427 36903404804224582907853641)
          ·
            refine ⟨27677553603168437180890231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36903404804224582907853641 27677553603168437180890231)
            ·
              refine ⟨41516330404752655771335347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27677553603168437180890231 41516330404752655771335347)
              ·
                refine ⟨62274495607128983657003021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41516330404752655771335347 62274495607128983657003021)
                ·
                  refine ⟨23352935852673368871376133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62274495607128983657003021 23352935852673368871376133)
                  ·
                    refine ⟨4378675472376256663383025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23352935852673368871376133 4378675472376256663383025)
                    ·
                      refine ⟨3284006604282192497537269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4378675472376256663383025 3284006604282192497537269)
                      ·
                        rfl

theorem cell23_6395580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_6395580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395580 prefixEnd_6395580 := by exact prefixLift 6395580
  have htrace : WordTrace (prefixWord ++ tailWord_6395580) baseStart_6395580 baseEnd_6395580 := by
    simpa [prefixWord, tailWord_6395580, baseEnd_6395580] using wordTrace_append hprefix tailTrace_6395580
  have hstable : (prefixWord ++ tailWord_6395580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395580).length < 2 ^ (prefixWord ++ tailWord_6395580).sum := by decide
  have hdescent : baseEnd_6395580 < baseStart_6395580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395633 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 1, 7]
def baseStart_6395633 : Nat := 118140960795 + 6395633 * 2 ^ 59
def prefixEnd_6395633 : Nat := 4983230072969 + 3 ^ 40 * 6395633 * 2
def baseEnd_6395633 : Nat := 1094677939585626930058175

theorem tailTrace_6395633 : CollatzResearch.WordTrace tailWord_6395633 prefixEnd_6395633 1094677939585626930058175 := by
  unfold tailWord_6395633
  simp only [CollatzResearch.WordTrace]
  refine ⟨233267899238721403000087553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155511932825814268666725035 233267899238721403000087553)
  ·
    refine ⟨174950924429041052250065665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233267899238721403000087553 174950924429041052250065665)
    ·
      refine ⟨131213193321780789187549249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174950924429041052250065665 131213193321780789187549249)
      ·
        refine ⟨98409894991335591890661937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131213193321780789187549249 98409894991335591890661937)
        ·
          refine ⟨73807421243501693917996453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98409894991335591890661937 73807421243501693917996453)
          ·
            refine ⟨13838891483156567609624335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73807421243501693917996453 13838891483156567609624335)
            ·
              refine ⟨20758337224734851414436503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13838891483156567609624335 20758337224734851414436503)
              ·
                refine ⟨31137505837102277121654755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20758337224734851414436503 31137505837102277121654755)
                ·
                  refine ⟨46706258755653415682482133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31137505837102277121654755 46706258755653415682482133)
                  ·
                    refine ⟨1094677939585626930058175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46706258755653415682482133 1094677939585626930058175)
                    ·
                      rfl

theorem cell23_6395633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_6395633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395633 prefixEnd_6395633 := by exact prefixLift 6395633
  have htrace : WordTrace (prefixWord ++ tailWord_6395633) baseStart_6395633 baseEnd_6395633 := by
    simpa [prefixWord, tailWord_6395633, baseEnd_6395633] using wordTrace_append hprefix tailTrace_6395633
  have hstable : (prefixWord ++ tailWord_6395633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395633).length < 2 ^ (prefixWord ++ tailWord_6395633).sum := by decide
  have hdescent : baseEnd_6395633 < baseStart_6395633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395650 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_6395650 : Nat := 118140960795 + 6395650 * 2 ^ 59
def prefixEnd_6395650 : Nat := 4983230072969 + 3 ^ 40 * 6395650 * 2
def baseEnd_6395650 : Nat := 1094680849309335741220649

theorem tailTrace_6395650 : CollatzResearch.WordTrace tailWord_6395650 prefixEnd_6395650 1094680849309335741220649 := by
  unfold tailWord_6395650
  simp only [CollatzResearch.WordTrace]
  refine ⟨58317129819914953725864101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155512346186439876602304269 58317129819914953725864101)
  ·
    refine ⟨10934461841234053823599519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58317129819914953725864101 10934461841234053823599519)
    ·
      refine ⟨16401692761851080735399279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10934461841234053823599519 16401692761851080735399279)
      ·
        refine ⟨24602539142776621103098919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16401692761851080735399279 24602539142776621103098919)
        ·
          refine ⟨36903808714164931654648379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24602539142776621103098919 36903808714164931654648379)
          ·
            refine ⟨55355713071247397481972569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36903808714164931654648379 55355713071247397481972569)
            ·
              refine ⟨41516784803435548111479427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55355713071247397481972569 41516784803435548111479427)
              ·
                refine ⟨62275177205153322167219141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41516784803435548111479427 62275177205153322167219141)
                ·
                  refine ⟨11676595725966247906353589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62275177205153322167219141 11676595725966247906353589)
                  ·
                    refine ⟨1094680849309335741220649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11676595725966247906353589 1094680849309335741220649)
                    ·
                      rfl

theorem cell23_6395650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_6395650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395650 prefixEnd_6395650 := by exact prefixLift 6395650
  have htrace : WordTrace (prefixWord ++ tailWord_6395650) baseStart_6395650 baseEnd_6395650 := by
    simpa [prefixWord, tailWord_6395650, baseEnd_6395650] using wordTrace_append hprefix tailTrace_6395650
  have hstable : (prefixWord ++ tailWord_6395650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395650).length < 2 ^ (prefixWord ++ tailWord_6395650).sum := by decide
  have hdescent : baseEnd_6395650 < baseStart_6395650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395680 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 3, 4]
def baseStart_6395680 : Nat := 118140960795 + 6395680 * 2 ^ 59
def prefixEnd_6395680 : Nat := 4983230072969 + 3 ^ 40 * 6395680 * 2
def baseEnd_6395680 : Nat := 1094685984115880702095603

theorem tailTrace_6395680 : CollatzResearch.WordTrace tailWord_6395680 prefixEnd_6395680 1094685984115880702095603 := by
  unfold tailWord_6395680
  simp only [CollatzResearch.WordTrace]
  refine ⟨116634806734775565013524247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155513075646367420018032329 116634806734775565013524247)
  ·
    refine ⟨174952210102163347520286371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116634806734775565013524247 174952210102163347520286371)
    ·
      refine ⟨262428315153245021280429557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174952210102163347520286371 262428315153245021280429557)
      ·
        refine ⟨24602654545616720745040271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 262428315153245021280429557 24602654545616720745040271)
        ·
          refine ⟨36903981818425081117560407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24602654545616720745040271 36903981818425081117560407)
          ·
            refine ⟨55355972727637621676340611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36903981818425081117560407 55355972727637621676340611)
            ·
              refine ⟨83033959091456432514510917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55355972727637621676340611 83033959091456432514510917)
              ·
                refine ⟨15568867329648081096470797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83033959091456432514510917 15568867329648081096470797)
                ·
                  refine ⟨5838325248618030411176549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15568867329648081096470797 5838325248618030411176549)
                  ·
                    refine ⟨1094685984115880702095603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5838325248618030411176549 1094685984115880702095603)
                    ·
                      rfl

theorem cell23_6395680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 3, 4].length) (baseStart_6395680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395680 prefixEnd_6395680 := by exact prefixLift 6395680
  have htrace : WordTrace (prefixWord ++ tailWord_6395680) baseStart_6395680 baseEnd_6395680 := by
    simpa [prefixWord, tailWord_6395680, baseEnd_6395680] using wordTrace_append hprefix tailTrace_6395680
  have hstable : (prefixWord ++ tailWord_6395680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395680).length < 2 ^ (prefixWord ++ tailWord_6395680).sum := by decide
  have hdescent : baseEnd_6395680 < baseStart_6395680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395710 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 8]
def baseStart_6395710 : Nat := 118140960795 + 6395710 * 2 ^ 59
def prefixEnd_6395710 : Nat := 4983230072969 + 3 ^ 40 * 6395710 * 2
def baseEnd_6395710 : Nat := 364897039640808554323519

theorem tailTrace_6395710 : CollatzResearch.WordTrace tailWord_6395710 prefixEnd_6395710 364897039640808554323519 := by
  unfold tailWord_6395710
  simp only [CollatzResearch.WordTrace]
  refine ⟨29158838457430305643830073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155513805106294963433760389 29158838457430305643830073)
  ·
    refine ⟨21869128843072729232872555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29158838457430305643830073 21869128843072729232872555)
    ·
      refine ⟨32803693264609093849308833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21869128843072729232872555 32803693264609093849308833)
      ·
        refine ⟨24602769948456820386981625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32803693264609093849308833 24602769948456820386981625)
        ·
          refine ⟨18452077461342615290236219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24602769948456820386981625 18452077461342615290236219)
          ·
            refine ⟨27678116192013922935354329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18452077461342615290236219 27678116192013922935354329)
            ·
              refine ⟨20758587144010442201515747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27678116192013922935354329 20758587144010442201515747)
              ·
                refine ⟨31137880716015663302273621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20758587144010442201515747 31137880716015663302273621)
                ·
                  refine ⟨364897039640808554323519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31137880716015663302273621 364897039640808554323519)
                  ·
                    rfl

theorem cell23_6395710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_6395710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395710 prefixEnd_6395710 := by exact prefixLift 6395710
  have htrace : WordTrace (prefixWord ++ tailWord_6395710) baseStart_6395710 baseEnd_6395710 := by
    simpa [prefixWord, tailWord_6395710, baseEnd_6395710] using wordTrace_append hprefix tailTrace_6395710
  have hstable : (prefixWord ++ tailWord_6395710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395710).length < 2 ^ (prefixWord ++ tailWord_6395710).sum := by decide
  have hdescent : baseEnd_6395710 < baseStart_6395710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395770 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 4, 4]
def baseStart_6395770 : Nat := 118140960795 + 6395770 * 2 ^ 59
def prefixEnd_6395770 : Nat := 4983230072969 + 3 ^ 40 * 6395770 * 2
def baseEnd_6395770 : Nat := 1094701388535515584720465

theorem tailTrace_6395770 : CollatzResearch.WordTrace tailWord_6395770 prefixEnd_6395770 1094701388535515584720465 := by
  unfold tailWord_6395770
  simp only [CollatzResearch.WordTrace]
  refine ⟨58318224009806268849456191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155515264026150050265216509 58318224009806268849456191)
  ·
    refine ⟨87477336014709403274184287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58318224009806268849456191 87477336014709403274184287)
    ·
      refine ⟨131216004022064104911276431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87477336014709403274184287 131216004022064104911276431)
      ·
        refine ⟨196824006033096157366914647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131216004022064104911276431 196824006033096157366914647)
        ·
          refine ⟨295236009049644236050371971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196824006033096157366914647 295236009049644236050371971)
          ·
            refine ⟨442854013574466354075557957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295236009049644236050371971 442854013574466354075557957)
            ·
              refine ⟨83035127545212441389167117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 442854013574466354075557957 83035127545212441389167117)
              ·
                refine ⟨31138172829454665520937669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83035127545212441389167117 31138172829454665520937669)
                ·
                  refine ⟨5838407405522749785175813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31138172829454665520937669 5838407405522749785175813)
                  ·
                    refine ⟨1094701388535515584720465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5838407405522749785175813 1094701388535515584720465)
                    ·
                      rfl

theorem cell23_6395770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_6395770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395770 prefixEnd_6395770 := by exact prefixLift 6395770
  have htrace : WordTrace (prefixWord ++ tailWord_6395770) baseStart_6395770 baseEnd_6395770 := by
    simpa [prefixWord, tailWord_6395770, baseEnd_6395770] using wordTrace_append hprefix tailTrace_6395770
  have hstable : (prefixWord ++ tailWord_6395770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395770).length < 2 ^ (prefixWord ++ tailWord_6395770).sum := by decide
  have hdescent : baseEnd_6395770 < baseStart_6395770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395780 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_6395780 : Nat := 118140960795 + 6395780 * 2 ^ 59
def prefixEnd_6395780 : Nat := 4983230072969 + 3 ^ 40 * 6395780 * 2
def baseEnd_6395780 : Nat := 3284109300413091715036349

theorem tailTrace_6395780 : CollatzResearch.WordTrace tailWord_6395780 prefixEnd_6395780 3284109300413091715036349 := by
  unfold tailWord_6395780
  simp only [CollatzResearch.WordTrace]
  refine ⟨116636630384594423552844397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155515507179459231403792529 116636630384594423552844397)
  ·
    refine ⟨43738736394222908832316649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116636630384594423552844397 43738736394222908832316649)
    ·
      refine ⟨32804052295667181624237487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43738736394222908832316649 32804052295667181624237487)
      ·
        refine ⟨49206078443500772436356231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32804052295667181624237487 49206078443500772436356231)
        ·
          refine ⟨73809117665251158654534347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49206078443500772436356231 73809117665251158654534347)
          ·
            refine ⟨110713676497876737981801521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73809117665251158654534347 110713676497876737981801521)
            ·
              refine ⟨83035257373407553486351141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110713676497876737981801521 83035257373407553486351141)
              ·
                refine ⟨15569110757513916278690839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83035257373407553486351141 15569110757513916278690839)
                ·
                  refine ⟨23353666136270874418036259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15569110757513916278690839 23353666136270874418036259)
                  ·
                    refine ⟨35030499204406311627054389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23353666136270874418036259 35030499204406311627054389)
                    ·
                      refine ⟨3284109300413091715036349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35030499204406311627054389 3284109300413091715036349)
                      ·
                        rfl

theorem cell23_6395780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_6395780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395780 prefixEnd_6395780 := by exact prefixLift 6395780
  have htrace : WordTrace (prefixWord ++ tailWord_6395780) baseStart_6395780 baseEnd_6395780 := by
    simpa [prefixWord, tailWord_6395780, baseEnd_6395780] using wordTrace_append hprefix tailTrace_6395780
  have hstable : (prefixWord ++ tailWord_6395780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395780).length < 2 ^ (prefixWord ++ tailWord_6395780).sum := by decide
  have hdescent : baseEnd_6395780 < baseStart_6395780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395797 : List Nat := [1, 3, 2, 1, 1, 3, 2, 4, 1, 2, 3]
def baseStart_6395797 : Nat := 118140960795 + 6395797 * 2 ^ 59
def prefixEnd_6395797 : Nat := 4983230072969 + 3 ^ 40 * 6395797 * 2
def baseEnd_6395797 : Nat := 3284118029584218148523771

theorem tailTrace_6395797 : CollatzResearch.WordTrace tailWord_6395797 prefixEnd_6395797 3284118029584218148523771 := by
  unfold tailWord_6395797
  simp only [CollatzResearch.WordTrace]
  refine ⟨233273880810127259009057645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155515920540084839339371763 233273880810127259009057645)
  ·
    refine ⟨87477705303797722128396617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233273880810127259009057645 87477705303797722128396617)
    ·
      refine ⟨65608278977848291596297463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87477705303797722128396617 65608278977848291596297463)
      ·
        refine ⟨98412418466772437394446195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65608278977848291596297463 98412418466772437394446195)
        ·
          refine ⟨147618627700158656091669293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98412418466772437394446195 147618627700158656091669293)
          ·
            refine ⟨55356985387559496034375985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147618627700158656091669293 55356985387559496034375985)
            ·
              refine ⟨41517739040669622025781989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55356985387559496034375985 41517739040669622025781989)
              ·
                refine ⟨7784576070125554129834123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41517739040669622025781989 7784576070125554129834123)
                ·
                  refine ⟨11676864105188331194751185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7784576070125554129834123 11676864105188331194751185)
                  ·
                    refine ⟨8757648078891248396063389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11676864105188331194751185 8757648078891248396063389)
                    ·
                      refine ⟨3284118029584218148523771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8757648078891248396063389 3284118029584218148523771)
                      ·
                        rfl

theorem cell23_6395797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_6395797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395797 prefixEnd_6395797 := by exact prefixLift 6395797
  have htrace : WordTrace (prefixWord ++ tailWord_6395797) baseStart_6395797 baseEnd_6395797 := by
    simpa [prefixWord, tailWord_6395797, baseEnd_6395797] using wordTrace_append hprefix tailTrace_6395797
  have hstable : (prefixWord ++ tailWord_6395797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395797).length < 2 ^ (prefixWord ++ tailWord_6395797).sum := by decide
  have hdescent : baseEnd_6395797 < baseStart_6395797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395798 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_6395798 : Nat := 118140960795 + 6395798 * 2 ^ 59
def prefixEnd_6395798 : Nat := 4983230072969 + 3 ^ 40 * 6395798 * 2
def baseEnd_6395798 : Nat := 3284118543064872644611267

theorem tailTrace_6395798 : CollatzResearch.WordTrace tailWord_6395798 prefixEnd_6395798 3284118543064872644611267 := by
  unfold tailWord_6395798
  simp only [CollatzResearch.WordTrace]
  refine ⟨14579619830195227261240253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155515944855415757453229365 14579619830195227261240253)
  ·
    refine ⟨5467357436323210222965095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14579619830195227261240253 5467357436323210222965095)
    ·
      refine ⟨8201036154484815334447643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5467357436323210222965095 8201036154484815334447643)
      ·
        refine ⟨12301554231727223001671465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8201036154484815334447643 12301554231727223001671465)
        ·
          refine ⟨9226165673795417251253599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12301554231727223001671465 9226165673795417251253599)
          ·
            refine ⟨13839248510693125876880399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9226165673795417251253599 13839248510693125876880399)
            ·
              refine ⟨20758872766039688815320599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13839248510693125876880399 20758872766039688815320599)
              ·
                refine ⟨31138309149059533222980899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20758872766039688815320599 31138309149059533222980899)
                ·
                  refine ⟨46707463723589299834471349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31138309149059533222980899 46707463723589299834471349)
                  ·
                    refine ⟨4378824724086496859481689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46707463723589299834471349 4378824724086496859481689)
                    ·
                      refine ⟨3284118543064872644611267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4378824724086496859481689 3284118543064872644611267)
                      ·
                        rfl

theorem cell23_6395798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_6395798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395798 prefixEnd_6395798 := by exact prefixLift 6395798
  have htrace : WordTrace (prefixWord ++ tailWord_6395798) baseStart_6395798 baseEnd_6395798 := by
    simpa [prefixWord, tailWord_6395798, baseEnd_6395798] using wordTrace_append hprefix tailTrace_6395798
  have hstable : (prefixWord ++ tailWord_6395798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395798).length < 2 ^ (prefixWord ++ tailWord_6395798).sum := by decide
  have hdescent : baseEnd_6395798 < baseStart_6395798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395827 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 4, 1, 3]
def baseStart_6395827 : Nat := 118140960795 + 6395827 * 2 ^ 59
def prefixEnd_6395827 : Nat := 4983230072969 + 3 ^ 40 * 6395827 * 2
def baseEnd_6395827 : Nat := 3284133434003853031148633

theorem tailTrace_6395827 : CollatzResearch.WordTrace tailWord_6395827 prefixEnd_6395827 3284133434003853031148633 := by
  unfold tailWord_6395827
  simp only [CollatzResearch.WordTrace]
  refine ⟨233274975000018574132649735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155516650000012382755099823 233274975000018574132649735)
  ·
    refine ⟨349912462500027861198974603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233274975000018574132649735 349912462500027861198974603)
    ·
      refine ⟨524868693750041791798461905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349912462500027861198974603 524868693750041791798461905)
      ·
        refine ⟨393651520312531343848846429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524868693750041791798461905 393651520312531343848846429)
        ·
          refine ⟨147619320117199253943317411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 393651520312531343848846429 147619320117199253943317411)
          ·
            refine ⟨221428980175798880914976117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147619320117199253943317411 221428980175798880914976117)
            ·
              refine ⟨20758966891481145085779011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221428980175798880914976117 20758966891481145085779011)
              ·
                refine ⟨31138450337221717628668517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20758966891481145085779011 31138450337221717628668517)
                ·
                  refine ⟨5838459438229072055375347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31138450337221717628668517 5838459438229072055375347)
                  ·
                    refine ⟨8757689157343608083063021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5838459438229072055375347 8757689157343608083063021)
                    ·
                      refine ⟨3284133434003853031148633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8757689157343608083063021 3284133434003853031148633)
                      ·
                        rfl

theorem cell23_6395827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 1, 3].length) (baseStart_6395827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395827 prefixEnd_6395827 := by exact prefixLift 6395827
  have htrace : WordTrace (prefixWord ++ tailWord_6395827) baseStart_6395827 baseEnd_6395827 := by
    simpa [prefixWord, tailWord_6395827, baseEnd_6395827] using wordTrace_append hprefix tailTrace_6395827
  have hstable : (prefixWord ++ tailWord_6395827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395827).length < 2 ^ (prefixWord ++ tailWord_6395827).sum := by decide
  have hdescent : baseEnd_6395827 < baseStart_6395827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395850 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_6395850 : Nat := 118140960795 + 6395850 * 2 ^ 59
def prefixEnd_6395850 : Nat := 4983230072969 + 3 ^ 40 * 6395850 * 2
def baseEnd_6395850 : Nat := 3284145244058906441161027

theorem tailTrace_6395850 : CollatzResearch.WordTrace tailWord_6395850 prefixEnd_6395850 3284145244058906441161027 := by
  unfold tailWord_6395850
  simp only [CollatzResearch.WordTrace]
  refine ⟨58318953469733812265184251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155517209252623499373824669 58318953469733812265184251)
  ·
    refine ⟨87478430204600718397776377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58318953469733812265184251 87478430204600718397776377)
    ·
      refine ⟨65608822653450538798332283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87478430204600718397776377 65608822653450538798332283)
      ·
        refine ⟨98413233980175808197498425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65608822653450538798332283 98413233980175808197498425)
        ·
          refine ⟨73809925485131856148123819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98413233980175808197498425 73809925485131856148123819)
          ·
            refine ⟨110714888227697784222185729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73809925485131856148123819 110714888227697784222185729)
            ·
              refine ⟨83036166170773338166639297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110714888227697784222185729 83036166170773338166639297)
              ·
                refine ⟨62277124628080003624979473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83036166170773338166639297 62277124628080003624979473)
                ·
                  refine ⟨46707843471060002718734605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62277124628080003624979473 46707843471060002718734605)
                  ·
                    refine ⟨17515441301647501019525477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46707843471060002718734605 17515441301647501019525477)
                    ·
                      refine ⟨3284145244058906441161027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17515441301647501019525477 3284145244058906441161027)
                      ·
                        rfl

theorem cell23_6395850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_6395850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395850 prefixEnd_6395850 := by exact prefixLift 6395850
  have htrace : WordTrace (prefixWord ++ tailWord_6395850) baseStart_6395850 baseEnd_6395850 := by
    simpa [prefixWord, tailWord_6395850, baseEnd_6395850] using wordTrace_append hprefix tailTrace_6395850
  have hstable : (prefixWord ++ tailWord_6395850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395850).length < 2 ^ (prefixWord ++ tailWord_6395850).sum := by decide
  have hdescent : baseEnd_6395850 < baseStart_6395850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395862 : List Nat := [5, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_6395862 : Nat := 118140960795 + 6395862 * 2 ^ 59
def prefixEnd_6395862 : Nat := 4983230072969 + 3 ^ 40 * 6395862 * 2
def baseEnd_6395862 : Nat := 3284151405826760394210973

theorem tailTrace_6395862 : CollatzResearch.WordTrace tailWord_6395862 prefixEnd_6395862 3284151405826760394210973 := by
  unfold tailWord_6395862
  simp only [CollatzResearch.WordTrace]
  refine ⟨14579765722180735944385865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155517501036594516740115893 14579765722180735944385865)
  ·
    refine ⟨10934824291635551958289399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14579765722180735944385865 10934824291635551958289399)
    ·
      refine ⟨16402236437453327937434099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10934824291635551958289399 16402236437453327937434099)
      ·
        refine ⟨24603354656179991906151149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16402236437453327937434099 24603354656179991906151149)
        ·
          refine ⟨9226257996067496964806681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24603354656179991906151149 9226257996067496964806681)
          ·
            refine ⟨6919693497050622723605011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9226257996067496964806681 6919693497050622723605011)
            ·
              refine ⟨10379540245575934085407517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6919693497050622723605011 10379540245575934085407517)
              ·
                refine ⟨3892327592090975282027819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10379540245575934085407517 3892327592090975282027819)
                ·
                  refine ⟨5838491388136462923041729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3892327592090975282027819 5838491388136462923041729)
                  ·
                    refine ⟨4378868541102347192281297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5838491388136462923041729 4378868541102347192281297)
                    ·
                      refine ⟨3284151405826760394210973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4378868541102347192281297 3284151405826760394210973)
                      ·
                        rfl

theorem cell23_6395862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_6395862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395862 prefixEnd_6395862 := by exact prefixLift 6395862
  have htrace : WordTrace (prefixWord ++ tailWord_6395862) baseStart_6395862 baseEnd_6395862 := by
    simpa [prefixWord, tailWord_6395862, baseEnd_6395862] using wordTrace_append hprefix tailTrace_6395862
  have hstable : (prefixWord ++ tailWord_6395862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395862).length < 2 ^ (prefixWord ++ tailWord_6395862).sum := by decide
  have hdescent : baseEnd_6395862 < baseStart_6395862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395920 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 6, 5]
def baseStart_6395920 : Nat := 118140960795 + 6395920 * 2 ^ 59
def prefixEnd_6395920 : Nat := 4983230072969 + 3 ^ 40 * 6395920 * 2
def baseEnd_6395920 : Nat := 1094727062568240389095235

theorem tailTrace_6395920 : CollatzResearch.WordTrace tailWord_6395920 prefixEnd_6395920 1094727062568240389095235 := by
  unfold tailWord_6395920
  simp only [CollatzResearch.WordTrace]
  refine ⟨116639183494340825507892607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155518911325787767343856809 116639183494340825507892607)
  ·
    refine ⟨174958775241511238261838911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116639183494340825507892607 174958775241511238261838911)
    ·
      refine ⟨262438162862266857392758367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174958775241511238261838911 262438162862266857392758367)
      ·
        refine ⟨393657244293400286089137551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262438162862266857392758367 393657244293400286089137551)
        ·
          refine ⟨590485866440100429133706327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393657244293400286089137551 590485866440100429133706327)
          ·
            refine ⟨885728799660150643700559491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590485866440100429133706327 885728799660150643700559491)
            ·
              refine ⟨1328593199490225965550839237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885728799660150643700559491 1328593199490225965550839237)
              ·
                refine ⟨249111224904417368540782357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1328593199490225965550839237 249111224904417368540782357)
                ·
                  refine ⟨11677088667394564150349173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 249111224904417368540782357 11677088667394564150349173)
                  ·
                    refine ⟨1094727062568240389095235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11677088667394564150349173 1094727062568240389095235)
                    ·
                      rfl

theorem cell23_6395920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 6, 5].length) (baseStart_6395920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395920 prefixEnd_6395920 := by exact prefixLift 6395920
  have htrace : WordTrace (prefixWord ++ tailWord_6395920) baseStart_6395920 baseEnd_6395920 := by
    simpa [prefixWord, tailWord_6395920, baseEnd_6395920] using wordTrace_append hprefix tailTrace_6395920
  have hstable : (prefixWord ++ tailWord_6395920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395920).length < 2 ^ (prefixWord ++ tailWord_6395920).sum := by decide
  have hdescent : baseEnd_6395920 < baseStart_6395920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395941 : List Nat := [1, 3, 1, 2, 2, 5, 2, 2, 5]
def baseStart_6395941 : Nat := 118140960795 + 6395941 * 2 ^ 59
def prefixEnd_6395941 : Nat := 4983230072969 + 3 ^ 40 * 6395941 * 2
def baseEnd_6395941 : Nat := 364910218977607287235901

theorem tailTrace_6395941 : CollatzResearch.WordTrace tailWord_6395941 prefixEnd_6395941 364910218977607287235901 := by
  unfold tailWord_6395941
  simp only [CollatzResearch.WordTrace]
  refine ⟨233279132921605571602299677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155519421947737047734866451 233279132921605571602299677)
  ·
    refine ⟨87479674845602089350862379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233279132921605571602299677 87479674845602089350862379)
    ·
      refine ⟨131219512268403134026293569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87479674845602089350862379 131219512268403134026293569)
      ·
        refine ⟨98414634201302350519720177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131219512268403134026293569 98414634201302350519720177)
        ·
          refine ⟨73810975650976762889790133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98414634201302350519720177 73810975650976762889790133)
          ·
            refine ⟨6919778967279071520917825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73810975650976762889790133 6919778967279071520917825)
            ·
              refine ⟨5189834225459303640688369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6919778967279071520917825 5189834225459303640688369)
              ·
                refine ⟨3892375669094477730516277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5189834225459303640688369 3892375669094477730516277)
                ·
                  refine ⟨364910218977607287235901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3892375669094477730516277 364910218977607287235901)
                  ·
                    rfl

theorem cell23_6395941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 5].length) (baseStart_6395941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395941 prefixEnd_6395941 := by exact prefixLift 6395941
  have htrace : WordTrace (prefixWord ++ tailWord_6395941) baseStart_6395941 baseEnd_6395941 := by
    simpa [prefixWord, tailWord_6395941, baseEnd_6395941] using wordTrace_append hprefix tailTrace_6395941
  have hstable : (prefixWord ++ tailWord_6395941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395941).length < 2 ^ (prefixWord ++ tailWord_6395941).sum := by decide
  have hdescent : baseEnd_6395941 < baseStart_6395941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395957 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_6395957 : Nat := 118140960795 + 6395957 * 2 ^ 59
def prefixEnd_6395957 : Nat := 4983230072969 + 3 ^ 40 * 6395957 * 2
def baseEnd_6395957 : Nat := 3284200186488937522523035

theorem tailTrace_6395957 : CollatzResearch.WordTrace tailWord_6395957 prefixEnd_6395957 3284200186488937522523035 := by
  unfold tailWord_6395957
  simp only [CollatzResearch.WordTrace]
  refine ⟨233279716489547606334882125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155519810993031737556588083 233279716489547606334882125)
  ·
    refine ⟨87479893683580352375580797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233279716489547606334882125 87479893683580352375580797)
    ·
      refine ⟨32804960131342632140842799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87479893683580352375580797 32804960131342632140842799)
      ·
        refine ⟨49207440197013948211264199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32804960131342632140842799 49207440197013948211264199)
        ·
          refine ⟨73811160295520922316896299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49207440197013948211264199 73811160295520922316896299)
          ·
            refine ⟨110716740443281383475344449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73811160295520922316896299 110716740443281383475344449)
            ·
              refine ⟨83037555332461037606508337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110716740443281383475344449 83037555332461037606508337)
              ·
                refine ⟨62278166499345778204881253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83037555332461037606508337 62278166499345778204881253)
                ·
                  refine ⟨11677156218627333413415235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62278166499345778204881253 11677156218627333413415235)
                  ·
                    refine ⟨17515734327941000120122853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11677156218627333413415235 17515734327941000120122853)
                    ·
                      refine ⟨3284200186488937522523035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17515734327941000120122853 3284200186488937522523035)
                      ·
                        rfl

theorem cell23_6395957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_6395957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395957 prefixEnd_6395957 := by exact prefixLift 6395957
  have htrace : WordTrace (prefixWord ++ tailWord_6395957) baseStart_6395957 baseEnd_6395957 := by
    simpa [prefixWord, tailWord_6395957, baseEnd_6395957] using wordTrace_append hprefix tailTrace_6395957
  have hstable : (prefixWord ++ tailWord_6395957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395957).length < 2 ^ (prefixWord ++ tailWord_6395957).sum := by decide
  have hdescent : baseEnd_6395957 < baseStart_6395957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395967 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 5, 4]
def baseStart_6395967 : Nat := 118140960795 + 6395967 * 2 ^ 59
def prefixEnd_6395967 : Nat := 4983230072969 + 3 ^ 40 * 6395967 * 2
def baseEnd_6395967 : Nat := 1094735107098494161132663

theorem tailTrace_6395967 : CollatzResearch.WordTrace tailWord_6395967 prefixEnd_6395967 1094735107098494161132663 := by
  unfold tailWord_6395967
  simp only [CollatzResearch.WordTrace]
  refine ⟨233280081219511378042746155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155520054146340918695164103 233280081219511378042746155)
  ·
    refine ⟨349920121829267067064119233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233280081219511378042746155 349920121829267067064119233)
    ·
      refine ⟨262440091371950300298089425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349920121829267067064119233 262440091371950300298089425)
      ·
        refine ⟨196830068528962725223567069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262440091371950300298089425 196830068528962725223567069)
        ·
          refine ⟨73811275698361021958837651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196830068528962725223567069 73811275698361021958837651)
          ·
            refine ⟨110716913547541532938256477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73811275698361021958837651 110716913547541532938256477)
            ·
              refine ⟨41518842580328074851846179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110716913547541532938256477 41518842580328074851846179)
              ·
                refine ⟨62278263870492112277769269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41518842580328074851846179 62278263870492112277769269)
                ·
                  refine ⟨5838587237858635526040869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62278263870492112277769269 5838587237858635526040869)
                  ·
                    refine ⟨1094735107098494161132663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5838587237858635526040869 1094735107098494161132663)
                    ·
                      rfl

theorem cell23_6395967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 4].length) (baseStart_6395967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395967 prefixEnd_6395967 := by exact prefixLift 6395967
  have htrace : WordTrace (prefixWord ++ tailWord_6395967) baseStart_6395967 baseEnd_6395967 := by
    simpa [prefixWord, tailWord_6395967, baseEnd_6395967] using wordTrace_append hprefix tailTrace_6395967
  have hstable : (prefixWord ++ tailWord_6395967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395967).length < 2 ^ (prefixWord ++ tailWord_6395967).sum := by decide
  have hdescent : baseEnd_6395967 < baseStart_6395967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6395977 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 1, 4, 3]
def baseStart_6395977 : Nat := 118140960795 + 6395977 * 2 ^ 59
def prefixEnd_6395977 : Nat := 4983230072969 + 3 ^ 40 * 6395977 * 2
def baseEnd_6395977 : Nat := 3284210456102027444272943

theorem tailTrace_6395977 : CollatzResearch.WordTrace tailWord_6395977 prefixEnd_6395977 3284210456102027444272943 := by
  unfold tailWord_6395977
  simp only [CollatzResearch.WordTrace]
  refine ⟨233280445949475149750610185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155520297299650099833740123 233280445949475149750610185)
  ·
    refine ⟨174960334462106362312957639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233280445949475149750610185 174960334462106362312957639)
    ·
      refine ⟨262440501693159543469436459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174960334462106362312957639 262440501693159543469436459)
      ·
        refine ⟨393660752539739315204154689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262440501693159543469436459 393660752539739315204154689)
        ·
          refine ⟨295245564404804486403116017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393660752539739315204154689 295245564404804486403116017)
          ·
            refine ⟨221434173303603364802337013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295245564404804486403116017 221434173303603364802337013)
            ·
              refine ⟨20759453747212815450219095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221434173303603364802337013 20759453747212815450219095)
              ·
                refine ⟨31139180620819223175328643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20759453747212815450219095 31139180620819223175328643)
                ·
                  refine ⟨46708770931228834762992965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31139180620819223175328643 46708770931228834762992965)
                  ·
                    refine ⟨8757894549605406518061181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46708770931228834762992965 8757894549605406518061181)
                    ·
                      refine ⟨3284210456102027444272943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8757894549605406518061181 3284210456102027444272943)
                      ·
                        rfl

theorem cell23_6395977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 4, 3].length) (baseStart_6395977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6395977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6395977 prefixEnd_6395977 := by exact prefixLift 6395977
  have htrace : WordTrace (prefixWord ++ tailWord_6395977) baseStart_6395977 baseEnd_6395977 := by
    simpa [prefixWord, tailWord_6395977, baseEnd_6395977] using wordTrace_append hprefix tailTrace_6395977
  have hstable : (prefixWord ++ tailWord_6395977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6395977).length < 2 ^ (prefixWord ++ tailWord_6395977).sum := by decide
  have hdescent : baseEnd_6395977 < baseStart_6395977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6395977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396052 : List Nat := [2, 4, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_6396052 : Nat := 118140960795 + 6396052 * 2 ^ 59
def prefixEnd_6396052 : Nat := 4983230072969 + 3 ^ 40 * 6396052 * 2
def baseEnd_6396052 : Nat := 1094749655717038216945033

theorem tailTrace_6396052 : CollatzResearch.WordTrace tailWord_6396052 prefixEnd_6396052 1094749655717038216945033 := by
  unfold tailWord_6396052
  simp only [CollatzResearch.WordTrace]
  refine ⟨116641590712101718779795205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155522120949468958373060273 116641590712101718779795205)
  ·
    refine ⟨21870298258519072271211601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116641590712101718779795205 21870298258519072271211601)
    ·
      refine ⟨16402723693889304203408701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21870298258519072271211601 16402723693889304203408701)
      ·
        refine ⟨6151021385208489076278263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16402723693889304203408701 6151021385208489076278263)
        ·
          refine ⟨9226532077812733614417395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6151021385208489076278263 9226532077812733614417395)
          ·
            refine ⟨13839798116719100421626093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9226532077812733614417395 13839798116719100421626093)
            ·
              refine ⟨5189924293769662658109785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13839798116719100421626093 5189924293769662658109785)
              ·
                refine ⟨3892443220327246993582339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5189924293769662658109785 3892443220327246993582339)
                ·
                  refine ⟨5838664830490870490373509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3892443220327246993582339 5838664830490870490373509)
                  ·
                    refine ⟨1094749655717038216945033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5838664830490870490373509 1094749655717038216945033)
                    ·
                      rfl

theorem cell23_6396052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_6396052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396052 prefixEnd_6396052 := by exact prefixLift 6396052
  have htrace : WordTrace (prefixWord ++ tailWord_6396052) baseStart_6396052 baseEnd_6396052 := by
    simpa [prefixWord, tailWord_6396052, baseEnd_6396052] using wordTrace_append hprefix tailTrace_6396052
  have hstable : (prefixWord ++ tailWord_6396052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396052).length < 2 ^ (prefixWord ++ tailWord_6396052).sum := by decide
  have hdescent : baseEnd_6396052 < baseStart_6396052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396067 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 3]
def baseStart_6396067 : Nat := 118140960795 + 6396067 * 2 ^ 59
def prefixEnd_6396067 : Nat := 4983230072969 + 3 ^ 40 * 6396067 * 2
def baseEnd_6396067 : Nat := 3284256669360932092147529

theorem tailTrace_6396067 : CollatzResearch.WordTrace tailWord_6396067 prefixEnd_6396067 3284256669360932092147529 := by
  unfold tailWord_6396067
  simp only [CollatzResearch.WordTrace]
  refine ⟨233283728519149095121386455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155522485679432730080924303 233283728519149095121386455)
  ·
    refine ⟨349925592778723642682079683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233283728519149095121386455 349925592778723642682079683)
    ·
      refine ⟨524888389168085464023119525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349925592778723642682079683 524888389168085464023119525)
      ·
        refine ⟨98416572969016024504334911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 524888389168085464023119525 98416572969016024504334911)
        ·
          refine ⟨147624859453524036756502367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98416572969016024504334911 147624859453524036756502367)
          ·
            refine ⟨221437289180286055134753551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147624859453524036756502367 221437289180286055134753551)
            ·
              refine ⟨332155933770429082702130327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221437289180286055134753551 332155933770429082702130327)
              ·
                refine ⟨498233900655643624053195491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332155933770429082702130327 498233900655643624053195491)
                ·
                  refine ⟨747350850983465436079793237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 498233900655643624053195491 747350850983465436079793237)
                  ·
                    refine ⟨8758017784962485579060077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 747350850983465436079793237 8758017784962485579060077)
                    ·
                      refine ⟨3284256669360932092147529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8758017784962485579060077 3284256669360932092147529)
                      ·
                        rfl

theorem cell23_6396067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_6396067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396067 prefixEnd_6396067 := by exact prefixLift 6396067
  have htrace : WordTrace (prefixWord ++ tailWord_6396067) baseStart_6396067 baseEnd_6396067 := by
    simpa [prefixWord, tailWord_6396067, baseEnd_6396067] using wordTrace_append hprefix tailTrace_6396067
  have hstable : (prefixWord ++ tailWord_6396067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396067).length < 2 ^ (prefixWord ++ tailWord_6396067).sum := by decide
  have hdescent : baseEnd_6396067 < baseStart_6396067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396078 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 3, 5]
def baseStart_6396078 : Nat := 118140960795 + 6396078 * 2 ^ 59
def prefixEnd_6396078 : Nat := 4983230072969 + 3 ^ 40 * 6396078 * 2
def baseEnd_6396078 : Nat := 1094754105882710516369993

theorem tailTrace_6396078 : CollatzResearch.WordTrace tailWord_6396078 prefixEnd_6396078 1094754105882710516369993 := by
  unfold tailWord_6396078
  simp only [CollatzResearch.WordTrace]
  refine ⟨29160516215263655500004611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155522753148072829333357925 29160516215263655500004611)
  ·
    refine ⟨43740774322895483250006917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29160516215263655500004611 43740774322895483250006917)
    ·
      refine ⟨8201395185542903109376297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43740774322895483250006917 8201395185542903109376297)
      ·
        refine ⟨6151046389157177332032223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8201395185542903109376297 6151046389157177332032223)
        ·
          refine ⟨9226569583735765998048335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6151046389157177332032223 9226569583735765998048335)
          ·
            refine ⟨13839854375603648997072503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9226569583735765998048335 13839854375603648997072503)
            ·
              refine ⟨20759781563405473495608755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13839854375603648997072503 20759781563405473495608755)
              ·
                refine ⟨31139672345108210243413133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20759781563405473495608755 31139672345108210243413133)
                ·
                  refine ⟨11677377129415578841279925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31139672345108210243413133 11677377129415578841279925)
                  ·
                    refine ⟨1094754105882710516369993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11677377129415578841279925 1094754105882710516369993)
                    ·
                      rfl

theorem cell23_6396078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_6396078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396078 prefixEnd_6396078 := by exact prefixLift 6396078
  have htrace : WordTrace (prefixWord ++ tailWord_6396078) baseStart_6396078 baseEnd_6396078 := by
    simpa [prefixWord, tailWord_6396078, baseEnd_6396078] using wordTrace_append hprefix tailTrace_6396078
  have hstable : (prefixWord ++ tailWord_6396078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396078).length < 2 ^ (prefixWord ++ tailWord_6396078).sum := by decide
  have hdescent : baseEnd_6396078 < baseStart_6396078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396081 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 3, 1, 4]
def baseStart_6396081 : Nat := 118140960795 + 6396081 * 2 ^ 59
def prefixEnd_6396081 : Nat := 4983230072969 + 3 ^ 40 * 6396081 * 2
def baseEnd_6396081 : Nat := 3284263858090095037372465

theorem tailTrace_6396081 : CollatzResearch.WordTrace tailWord_6396081 prefixEnd_6396081 3284263858090095037372465 := by
  unfold tailWord_6396081
  simp only [CollatzResearch.WordTrace]
  refine ⟨233284239141098375512396097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155522826094065583674930731 233284239141098375512396097)
  ·
    refine ⟨174963179355823781634297073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233284239141098375512396097 174963179355823781634297073)
    ·
      refine ⟨131222384516867836225722805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174963179355823781634297073 131222384516867836225722805)
      ·
        refine ⟨12302098548456359646161513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131222384516867836225722805 12302098548456359646161513)
        ·
          refine ⟨9226573911342269734621135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12302098548456359646161513 9226573911342269734621135)
          ·
            refine ⟨13839860867013404601931703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9226573911342269734621135 13839860867013404601931703)
            ·
              refine ⟨20759791300520106902897555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13839860867013404601931703 20759791300520106902897555)
              ·
                refine ⟨31139686950780160354346333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20759791300520106902897555 31139686950780160354346333)
                ·
                  refine ⟨11677382606542560132879875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31139686950780160354346333 11677382606542560132879875)
                  ·
                    refine ⟨17516073909813840199319813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11677382606542560132879875 17516073909813840199319813)
                    ·
                      refine ⟨3284263858090095037372465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17516073909813840199319813 3284263858090095037372465)
                      ·
                        rfl

theorem cell23_6396081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_6396081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396081 prefixEnd_6396081 := by exact prefixLift 6396081
  have htrace : WordTrace (prefixWord ++ tailWord_6396081) baseStart_6396081 baseEnd_6396081 := by
    simpa [prefixWord, tailWord_6396081, baseEnd_6396081] using wordTrace_append hprefix tailTrace_6396081
  have hstable : (prefixWord ++ tailWord_6396081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396081).length < 2 ^ (prefixWord ++ tailWord_6396081).sum := by decide
  have hdescent : baseEnd_6396081 < baseStart_6396081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396085 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 2, 3, 2]
def baseStart_6396085 : Nat := 118140960795 + 6396085 * 2 ^ 59
def prefixEnd_6396085 : Nat := 4983230072969 + 3 ^ 40 * 6396085 * 2
def baseEnd_6396085 : Nat := 3284265912012713021722447

theorem tailTrace_6396085 : CollatzResearch.WordTrace tailWord_6396085 prefixEnd_6396085 3284265912012713021722447 := by
  unfold tailWord_6396085
  simp only [CollatzResearch.WordTrace]
  refine ⟨233284385033083884195541709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155522923355389256130361139 233284385033083884195541709)
  ·
    refine ⟨87481644387406456573328141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233284385033083884195541709 87481644387406456573328141)
    ·
      refine ⟨32805616645277421214998053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87481644387406456573328141 32805616645277421214998053)
      ·
        refine ⟨6151053120989516477812135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32805616645277421214998053 6151053120989516477812135)
        ·
          refine ⟨9226579681484274716718203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6151053120989516477812135 9226579681484274716718203)
          ·
            refine ⟨13839869522226412075077305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9226579681484274716718203 13839869522226412075077305)
            ·
              refine ⟨10379902141669809056307979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13839869522226412075077305 10379902141669809056307979)
              ·
                refine ⟨15569853212504713584461969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10379902141669809056307979 15569853212504713584461969)
                ·
                  refine ⟨11677389909378535188346477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15569853212504713584461969 11677389909378535188346477)
                  ·
                    refine ⟨4379021216016950695629929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11677389909378535188346477 4379021216016950695629929)
                    ·
                      refine ⟨3284265912012713021722447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4379021216016950695629929 3284265912012713021722447)
                      ·
                        rfl

theorem cell23_6396085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_6396085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396085 prefixEnd_6396085 := by exact prefixLift 6396085
  have htrace : WordTrace (prefixWord ++ tailWord_6396085) baseStart_6396085 baseEnd_6396085 := by
    simpa [prefixWord, tailWord_6396085, baseEnd_6396085] using wordTrace_append hprefix tailTrace_6396085
  have hstable : (prefixWord ++ tailWord_6396085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396085).length < 2 ^ (prefixWord ++ tailWord_6396085).sum := by decide
  have hdescent : baseEnd_6396085 < baseStart_6396085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396087 : List Nat := [1, 1, 3, 1, 4, 2, 2, 9]
def baseStart_6396087 : Nat := 118140960795 + 6396087 * 2 ^ 59
def prefixEnd_6396087 : Nat := 4983230072969 + 3 ^ 40 * 6396087 * 2
def baseEnd_6396087 : Nat := 121639516258297111625831

theorem tailTrace_6396087 : CollatzResearch.WordTrace tailWord_6396087 prefixEnd_6396087 121639516258297111625831 := by
  unfold tailWord_6396087
  simp only [CollatzResearch.WordTrace]
  refine ⟨233284457979076638537114515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155522971986051092358076343 233284457979076638537114515)
  ·
    refine ⟨349926686968614957805671773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233284457979076638537114515 349926686968614957805671773)
    ·
      refine ⟨131222507613230609177126915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349926686968614957805671773 131222507613230609177126915)
      ·
        refine ⟨196833761419845913765690373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131222507613230609177126915 196833761419845913765690373)
        ·
          refine ⟨36906330266221108831066945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196833761419845913765690373 36906330266221108831066945)
          ·
            refine ⟨27679747699665831623300209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36906330266221108831066945 27679747699665831623300209)
            ·
              refine ⟨20759810774749373717475157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27679747699665831623300209 20759810774749373717475157)
              ·
                refine ⟨121639516258297111625831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20759810774749373717475157 121639516258297111625831)
                ·
                  rfl

theorem cell23_6396087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 9].length) (baseStart_6396087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396087 prefixEnd_6396087 := by exact prefixLift 6396087
  have htrace : WordTrace (prefixWord ++ tailWord_6396087) baseStart_6396087 baseEnd_6396087 := by
    simpa [prefixWord, tailWord_6396087, baseEnd_6396087] using wordTrace_append hprefix tailTrace_6396087
  have hstable : (prefixWord ++ tailWord_6396087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396087).length < 2 ^ (prefixWord ++ tailWord_6396087).sum := by decide
  have hdescent : baseEnd_6396087 < baseStart_6396087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396118 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_6396118 : Nat := 118140960795 + 6396118 * 2 ^ 59
def prefixEnd_6396118 : Nat := 4983230072969 + 3 ^ 40 * 6396118 * 2
def baseEnd_6396118 : Nat := 3284282856874311392609795

theorem tailTrace_6396118 : CollatzResearch.WordTrace tailWord_6396118 prefixEnd_6396118 3284282856874311392609795 := by
  unfold tailWord_6396118
  simp only [CollatzResearch.WordTrace]
  refine ⟨14580349290122770676968313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155523725761309553887662005 14580349290122770676968313)
  ·
    refine ⟨10935261967592078007726235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14580349290122770676968313 10935261967592078007726235)
    ·
      refine ⟨16402892951388117011589353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10935261967592078007726235 16402892951388117011589353)
      ·
        refine ⟨12302169713541087758692015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16402892951388117011589353 12302169713541087758692015)
        ·
          refine ⟨18453254570311631638038023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12302169713541087758692015 18453254570311631638038023)
          ·
            refine ⟨27679881855467447457057035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18453254570311631638038023 27679881855467447457057035)
            ·
              refine ⟨41519822783201171185585553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27679881855467447457057035 41519822783201171185585553)
              ·
                refine ⟨31139867087400878389189165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41519822783201171185585553 31139867087400878389189165)
                ·
                  refine ⟨11677450157775329395945937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31139867087400878389189165 11677450157775329395945937)
                  ·
                    refine ⟨8758087618331497046959453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11677450157775329395945937 8758087618331497046959453)
                    ·
                      refine ⟨3284282856874311392609795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8758087618331497046959453 3284282856874311392609795)
                      ·
                        rfl

theorem cell23_6396118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_6396118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396118 prefixEnd_6396118 := by exact prefixLift 6396118
  have htrace : WordTrace (prefixWord ++ tailWord_6396118) baseStart_6396118 baseEnd_6396118 := by
    simpa [prefixWord, tailWord_6396118, baseEnd_6396118] using wordTrace_append hprefix tailTrace_6396118
  have hstable : (prefixWord ++ tailWord_6396118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396118).length < 2 ^ (prefixWord ++ tailWord_6396118).sum := by decide
  have hdescent : baseEnd_6396118 < baseStart_6396118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396127 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 5]
def baseStart_6396127 : Nat := 118140960795 + 6396127 * 2 ^ 59
def prefixEnd_6396127 : Nat := 4983230072969 + 3 ^ 40 * 6396127 * 2
def baseEnd_6396127 : Nat := 3284287478200201857397253

theorem tailTrace_6396127 : CollatzResearch.WordTrace tailWord_6396127 prefixEnd_6396127 3284287478200201857397253 := by
  unfold tailWord_6396127
  simp only [CollatzResearch.WordTrace]
  refine ⟨233285916898931725368570635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155523944599287816912380423 233285916898931725368570635)
  ·
    refine ⟨349928875348397588052855953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233285916898931725368570635 349928875348397588052855953)
    ·
      refine ⟨262446656511298191039641965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349928875348397588052855953 262446656511298191039641965)
      ·
        refine ⟨98417496191736821639865737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262446656511298191039641965 98417496191736821639865737)
        ·
          refine ⟨73813122143802616229899303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98417496191736821639865737 73813122143802616229899303)
          ·
            refine ⟨110719683215703924344848955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73813122143802616229899303 110719683215703924344848955)
            ·
              refine ⟨166079524823555886517273433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110719683215703924344848955 166079524823555886517273433)
              ·
                refine ⟨124559643617666914887955075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166079524823555886517273433 124559643617666914887955075)
                ·
                  refine ⟨186839465426500372331932613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124559643617666914887955075 186839465426500372331932613)
                  ·
                    refine ⟨35032399767468819812237365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 186839465426500372331932613 35032399767468819812237365)
                    ·
                      refine ⟨3284287478200201857397253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35032399767468819812237365 3284287478200201857397253)
                      ·
                        rfl

theorem cell23_6396127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_6396127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396127 prefixEnd_6396127 := by exact prefixLift 6396127
  have htrace : WordTrace (prefixWord ++ tailWord_6396127) baseStart_6396127 baseEnd_6396127 := by
    simpa [prefixWord, tailWord_6396127, baseEnd_6396127] using wordTrace_append hprefix tailTrace_6396127
  have hstable : (prefixWord ++ tailWord_6396127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396127).length < 2 ^ (prefixWord ++ tailWord_6396127).sum := by decide
  have hdescent : baseEnd_6396127 < baseStart_6396127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396147 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 1, 8]
def baseStart_6396147 : Nat := 118140960795 + 6396147 * 2 ^ 59
def prefixEnd_6396147 : Nat := 4983230072969 + 3 ^ 40 * 6396147 * 2
def baseEnd_6396147 : Nat := 1094765915937763926382387

theorem tailTrace_6396147 : CollatzResearch.WordTrace tailWord_6396147 prefixEnd_6396147 1094765915937763926382387 := by
  unfold tailWord_6396147
  simp only [CollatzResearch.WordTrace]
  refine ⟨233286646358859268784298695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155524430905906179189532463 233286646358859268784298695)
  ·
    refine ⟨349929969538288903176448043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233286646358859268784298695 349929969538288903176448043)
    ·
      refine ⟨524894954307433354764672065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349929969538288903176448043 524894954307433354764672065)
      ·
        refine ⟨393671215730575016073504049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524894954307433354764672065 393671215730575016073504049)
        ·
          refine ⟨295253411797931262055128037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393671215730575016073504049 295253411797931262055128037)
          ·
            refine ⟨55360014712112111635336507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 295253411797931262055128037 55360014712112111635336507)
            ·
              refine ⟨83040022068168167453004761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55360014712112111635336507 83040022068168167453004761)
              ·
                refine ⟨62280016551126125589753571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83040022068168167453004761 62280016551126125589753571)
                ·
                  refine ⟨93420024826689188384630357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62280016551126125589753571 93420024826689188384630357)
                  ·
                    refine ⟨1094765915937763926382387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93420024826689188384630357 1094765915937763926382387)
                    ·
                      rfl

theorem cell23_6396147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 8].length) (baseStart_6396147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396147 prefixEnd_6396147 := by exact prefixLift 6396147
  have htrace : WordTrace (prefixWord ++ tailWord_6396147) baseStart_6396147 baseEnd_6396147 := by
    simpa [prefixWord, tailWord_6396147, baseEnd_6396147] using wordTrace_append hprefix tailTrace_6396147
  have hstable : (prefixWord ++ tailWord_6396147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396147).length < 2 ^ (prefixWord ++ tailWord_6396147).sum := by decide
  have hdescent : baseEnd_6396147 < baseStart_6396147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396184 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 2, 2, 4]
def baseStart_6396184 : Nat := 118140960795 + 6396184 * 2 ^ 59
def prefixEnd_6396184 : Nat := 4983230072969 + 3 ^ 40 * 6396184 * 2
def baseEnd_6396184 : Nat := 3284316746597508134384491

theorem tailTrace_6396184 : CollatzResearch.WordTrace tailWord_6396184 prefixEnd_6396184 3284316746597508134384491 := by
  unfold tailWord_6396184
  simp only [CollatzResearch.WordTrace]
  refine ⟨116643997929862612051697803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155525330573150149402263737 116643997929862612051697803)
  ·
    refine ⟨174965996894793918077546705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116643997929862612051697803 174965996894793918077546705)
    ·
      refine ⟨131224497671095438558160029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174965996894793918077546705 131224497671095438558160029)
      ·
        refine ⟨49209186626660789459310011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131224497671095438558160029 49209186626660789459310011)
        ·
          refine ⟨73813779939991184188965017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49209186626660789459310011 73813779939991184188965017)
          ·
            refine ⟨55360334954993388141723763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73813779939991184188965017 55360334954993388141723763)
            ·
              refine ⟨83040502432490082212585645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55360334954993388141723763 83040502432490082212585645)
              ·
                refine ⟨31140188412183780829719617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83040502432490082212585645 31140188412183780829719617)
                ·
                  refine ⟨23355141309137835622289713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31140188412183780829719617 23355141309137835622289713)
                  ·
                    refine ⟨17516355981853376716717285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23355141309137835622289713 17516355981853376716717285)
                    ·
                      refine ⟨3284316746597508134384491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17516355981853376716717285 3284316746597508134384491)
                      ·
                        rfl

theorem cell23_6396184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_6396184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396184 prefixEnd_6396184 := by exact prefixLift 6396184
  have htrace : WordTrace (prefixWord ++ tailWord_6396184) baseStart_6396184 baseEnd_6396184 := by
    simpa [prefixWord, tailWord_6396184, baseEnd_6396184] using wordTrace_append hprefix tailTrace_6396184
  have hstable : (prefixWord ++ tailWord_6396184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396184).length < 2 ^ (prefixWord ++ tailWord_6396184).sum := by decide
  have hdescent : baseEnd_6396184 < baseStart_6396184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396204 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 3]
def baseStart_6396204 : Nat := 118140960795 + 6396204 * 2 ^ 59
def prefixEnd_6396204 : Nat := 4983230072969 + 3 ^ 40 * 6396204 * 2
def baseEnd_6396204 : Nat := 3284327016210598056134399

theorem tailTrace_6396204 : CollatzResearch.WordTrace tailWord_6396204 prefixEnd_6396204 3284327016210598056134399 := by
  unfold tailWord_6396204
  simp only [CollatzResearch.WordTrace]
  refine ⟨116644362659826383759561833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155525816879768511679415777 116644362659826383759561833)
  ·
    refine ⟨87483271994869787819671375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116644362659826383759561833 87483271994869787819671375)
    ·
      refine ⟨131224907992304681729507063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87483271994869787819671375 131224907992304681729507063)
      ·
        refine ⟨196837361988457022594260595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131224907992304681729507063 196837361988457022594260595)
        ·
          refine ⟨295256042982685533891390893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196837361988457022594260595 295256042982685533891390893)
          ·
            refine ⟨110721016118507075209271585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295256042982685533891390893 110721016118507075209271585)
            ·
              refine ⟨83040762088880306406953689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110721016118507075209271585 83040762088880306406953689)
              ·
                refine ⟨62280571566660229805215267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83040762088880306406953689 62280571566660229805215267)
                ·
                  refine ⟨93420857349990344707822901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62280571566660229805215267 93420857349990344707822901)
                  ·
                    refine ⟨8758205376561594816358397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93420857349990344707822901 8758205376561594816358397)
                    ·
                      refine ⟨3284327016210598056134399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8758205376561594816358397 3284327016210598056134399)
                      ·
                        rfl

theorem cell23_6396204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_6396204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396204 prefixEnd_6396204 := by exact prefixLift 6396204
  have htrace : WordTrace (prefixWord ++ tailWord_6396204) baseStart_6396204 baseEnd_6396204 := by
    simpa [prefixWord, tailWord_6396204, baseEnd_6396204] using wordTrace_append hprefix tailTrace_6396204
  have hstable : (prefixWord ++ tailWord_6396204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396204).length < 2 ^ (prefixWord ++ tailWord_6396204).sum := by decide
  have hdescent : baseEnd_6396204 < baseStart_6396204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396231 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 2, 5, 2]
def baseStart_6396231 : Nat := 118140960795 + 6396231 * 2 ^ 59
def prefixEnd_6396231 : Nat := 4983230072969 + 3 ^ 40 * 6396231 * 2
def baseEnd_6396231 : Nat := 3284340880188269450496775

theorem tailTrace_6396231 : CollatzResearch.WordTrace tailWord_6396231 prefixEnd_6396231 3284340880188269450496775 := by
  unfold tailWord_6396231
  simp only [CollatzResearch.WordTrace]
  refine ⟨233289710090554951130356547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155526473393703300753571031 233289710090554951130356547)
  ·
    refine ⟨349934565135832426695534821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233289710090554951130356547 349934565135832426695534821)
    ·
      refine ⟨65612730962968580005412779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349934565135832426695534821 65612730962968580005412779)
      ·
        refine ⟨98419096444452870008119169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65612730962968580005412779 98419096444452870008119169)
        ·
          refine ⟨73814322333339652506089377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98419096444452870008119169 73814322333339652506089377)
          ·
            refine ⟨55360741750004739379567033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73814322333339652506089377 55360741750004739379567033)
            ·
              refine ⟨41520556312503554534675275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55360741750004739379567033 41520556312503554534675275)
              ·
                refine ⟨62280834468755331802012913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41520556312503554534675275 62280834468755331802012913)
                ·
                  refine ⟨46710625851566498851509685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62280834468755331802012913 46710625851566498851509685)
                  ·
                    refine ⟨4379121173584359267329033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46710625851566498851509685 4379121173584359267329033)
                    ·
                      refine ⟨3284340880188269450496775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4379121173584359267329033 3284340880188269450496775)
                      ·
                        rfl

theorem cell23_6396231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_6396231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396231 prefixEnd_6396231 := by exact prefixLift 6396231
  have htrace : WordTrace (prefixWord ++ tailWord_6396231) baseStart_6396231 baseEnd_6396231 := by
    simpa [prefixWord, tailWord_6396231, baseEnd_6396231] using wordTrace_append hprefix tailTrace_6396231
  have hstable : (prefixWord ++ tailWord_6396231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396231).length < 2 ^ (prefixWord ++ tailWord_6396231).sum := by decide
  have hdescent : baseEnd_6396231 < baseStart_6396231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396258 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_6396258 : Nat := 118140960795 + 6396258 * 2 ^ 59
def prefixEnd_6396258 : Nat := 4983230072969 + 3 ^ 40 * 6396258 * 2
def baseEnd_6396258 : Nat := 1094784914721980281619717

theorem tailTrace_6396258 : CollatzResearch.WordTrace tailWord_6396258 prefixEnd_6396258 1094784914721980281619717 := by
  unfold tailWord_6396258
  simp only [CollatzResearch.WordTrace]
  refine ⟨58322673715364283685397357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155527129907638089827726285 58322673715364283685397357)
  ·
    refine ⟨21871002643261606382024009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58322673715364283685397357 21871002643261606382024009)
    ·
      refine ⟨16403251982446204786518007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21871002643261606382024009 16403251982446204786518007)
      ·
        refine ⟨24604877973669307179777011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16403251982446204786518007 24604877973669307179777011)
        ·
          refine ⟨36907316960503960769665517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24604877973669307179777011 36907316960503960769665517)
          ·
            refine ⟨13840243860188985288624569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36907316960503960769665517 13840243860188985288624569)
            ·
              refine ⟨10380182895141738966468427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13840243860188985288624569 10380182895141738966468427)
              ·
                refine ⟨15570274342712608449702641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10380182895141738966468427 15570274342712608449702641)
                ·
                  refine ⟨11677705757034456337276981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15570274342712608449702641 11677705757034456337276981)
                  ·
                    refine ⟨1094784914721980281619717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11677705757034456337276981 1094784914721980281619717)
                    ·
                      rfl

theorem cell23_6396258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_6396258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396258 prefixEnd_6396258 := by exact prefixLift 6396258
  have htrace : WordTrace (prefixWord ++ tailWord_6396258) baseStart_6396258 baseEnd_6396258 := by
    simpa [prefixWord, tailWord_6396258, baseEnd_6396258] using wordTrace_append hprefix tailTrace_6396258
  have hstable : (prefixWord ++ tailWord_6396258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396258).length < 2 ^ (prefixWord ++ tailWord_6396258).sum := by decide
  have hdescent : baseEnd_6396258 < baseStart_6396258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396261 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 2, 1, 4]
def baseStart_6396261 : Nat := 118140960795 + 6396261 * 2 ^ 59
def prefixEnd_6396261 : Nat := 4983230072969 + 3 ^ 40 * 6396261 * 2
def baseEnd_6396261 : Nat := 3284356284607904333121637

theorem tailTrace_6396261 : CollatzResearch.WordTrace tailWord_6396261 prefixEnd_6396261 3284356284607904333121637 := by
  unfold tailWord_6396261
  simp only [CollatzResearch.WordTrace]
  refine ⟨233290804280446266253948637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155527202853630844169299091 233290804280446266253948637)
  ·
    refine ⟨87484051605167349845230739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233290804280446266253948637 87484051605167349845230739)
    ·
      refine ⟨131226077407751024767846109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87484051605167349845230739 131226077407751024767846109)
      ·
        refine ⟨49209779027906634287942291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131226077407751024767846109 49209779027906634287942291)
        ·
          refine ⟨73814668541859951431913437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49209779027906634287942291 73814668541859951431913437)
          ·
            refine ⟨27680500703197481786967539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73814668541859951431913437 27680500703197481786967539)
            ·
              refine ⟨41520751054796222680451309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27680500703197481786967539 41520751054796222680451309)
              ·
                refine ⟨15570281645548583505169241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41520751054796222680451309 15570281645548583505169241)
                ·
                  refine ⟨11677711234161437628876931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15570281645548583505169241 11677711234161437628876931)
                  ·
                    refine ⟨17516566851242156443315397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11677711234161437628876931 17516566851242156443315397)
                    ·
                      refine ⟨3284356284607904333121637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17516566851242156443315397 3284356284607904333121637)
                      ·
                        rfl

theorem cell23_6396261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_6396261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396261 prefixEnd_6396261 := by exact prefixLift 6396261
  have htrace : WordTrace (prefixWord ++ tailWord_6396261) baseStart_6396261 baseEnd_6396261 := by
    simpa [prefixWord, tailWord_6396261, baseEnd_6396261] using wordTrace_append hprefix tailTrace_6396261
  have hstable : (prefixWord ++ tailWord_6396261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396261).length < 2 ^ (prefixWord ++ tailWord_6396261).sum := by decide
  have hdescent : baseEnd_6396261 < baseStart_6396261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396338 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2]
def baseStart_6396338 : Nat := 118140960795 + 6396338 * 2 ^ 59
def prefixEnd_6396338 : Nat := 4983230072969 + 3 ^ 40 * 6396338 * 2
def baseEnd_6396338 : Nat := 3284395822618300531858783

theorem tailTrace_6396338 : CollatzResearch.WordTrace tailWord_6396338 prefixEnd_6396338 3284395822618300531858783 := by
  unfold tailWord_6396338
  simp only [CollatzResearch.WordTrace]
  refine ⟨58323403175291827101125417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155529075134111538936334445 58323403175291827101125417)
  ·
    refine ⟨43742552381468870325844063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58323403175291827101125417 43742552381468870325844063)
    ·
      refine ⟨65613828572203305488766095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43742552381468870325844063 65613828572203305488766095)
      ·
        refine ⟨98420742858304958233149143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65613828572203305488766095 98420742858304958233149143)
        ·
          refine ⟨147631114287457437349723715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98420742858304958233149143 147631114287457437349723715)
          ·
            refine ⟨221446671431186156024585573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147631114287457437349723715 221446671431186156024585573)
            ·
              refine ⟨41521250893347404254609795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 221446671431186156024585573 41521250893347404254609795)
              ·
                refine ⟨62281876340021106381914693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41521250893347404254609795 62281876340021106381914693)
                ·
                  refine ⟨11677851813753957446609005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62281876340021106381914693 11677851813753957446609005)
                  ·
                    refine ⟨4379194430157734042478377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11677851813753957446609005 4379194430157734042478377)
                    ·
                      refine ⟨3284395822618300531858783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4379194430157734042478377 3284395822618300531858783)
                      ·
                        rfl

theorem cell23_6396338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_6396338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396338 prefixEnd_6396338 := by exact prefixLift 6396338
  have htrace : WordTrace (prefixWord ++ tailWord_6396338) baseStart_6396338 baseEnd_6396338 := by
    simpa [prefixWord, tailWord_6396338, baseEnd_6396338] using wordTrace_append hprefix tailTrace_6396338
  have hstable : (prefixWord ++ tailWord_6396338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396338).length < 2 ^ (prefixWord ++ tailWord_6396338).sum := by decide
  have hdescent : baseEnd_6396338 < baseStart_6396338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396345 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 3, 1, 3]
def baseStart_6396345 : Nat := 118140960795 + 6396345 * 2 ^ 59
def prefixEnd_6396345 : Nat := 4983230072969 + 3 ^ 40 * 6396345 * 2
def baseEnd_6396345 : Nat := 3284399416982882004471251

theorem tailTrace_6396345 : CollatzResearch.WordTrace tailWord_6396345 prefixEnd_6396345 3284399416982882004471251 := by
  unfold tailWord_6396345
  simp only [CollatzResearch.WordTrace]
  refine ⟨233293868012141948600006489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155529245341427965733337659 233293868012141948600006489)
  ·
    refine ⟨174970401009106461450004867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233293868012141948600006489 174970401009106461450004867)
    ·
      refine ⟨262455601513659692175007301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174970401009106461450004867 262455601513659692175007301)
      ·
        refine ⟨49210425283811192282813869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262455601513659692175007301 49210425283811192282813869)
        ·
          refine ⟨18453909481429197106055201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49210425283811192282813869 18453909481429197106055201)
          ·
            refine ⟨13840432111071897829541401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18453909481429197106055201 13840432111071897829541401)
            ·
              refine ⟨10380324083303923372156051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13840432111071897829541401 10380324083303923372156051)
              ·
                refine ⟨15570486124955885058234077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10380324083303923372156051 15570486124955885058234077)
                ·
                  refine ⟨5838932296858456896837779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15570486124955885058234077 5838932296858456896837779)
                  ·
                    refine ⟨8758398445287685345256669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5838932296858456896837779 8758398445287685345256669)
                    ·
                      refine ⟨3284399416982882004471251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8758398445287685345256669 3284399416982882004471251)
                      ·
                        rfl

theorem cell23_6396345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_6396345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396345 prefixEnd_6396345 := by exact prefixLift 6396345
  have htrace : WordTrace (prefixWord ++ tailWord_6396345) baseStart_6396345 baseEnd_6396345 := by
    simpa [prefixWord, tailWord_6396345, baseEnd_6396345] using wordTrace_append hprefix tailTrace_6396345
  have hstable : (prefixWord ++ tailWord_6396345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396345).length < 2 ^ (prefixWord ++ tailWord_6396345).sum := by decide
  have hdescent : baseEnd_6396345 < baseStart_6396345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396361 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 1, 6]
def baseStart_6396361 : Nat := 118140960795 + 6396361 * 2 ^ 59
def prefixEnd_6396361 : Nat := 4983230072969 + 3 ^ 40 * 6396361 * 2
def baseEnd_6396361 : Nat := 1094802544224451313957059

theorem tailTrace_6396361 : CollatzResearch.WordTrace tailWord_6396361 prefixEnd_6396361 1094802544224451313957059 := by
  unfold tailWord_6396361
  simp only [CollatzResearch.WordTrace]
  refine ⟨233294451580083983332588937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155529634386722655555059291 233294451580083983332588937)
  ·
    refine ⟨174970838685062987499441703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233294451580083983332588937 174970838685062987499441703)
    ·
      refine ⟨262456258027594481249162555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174970838685062987499441703 262456258027594481249162555)
      ·
        refine ⟨393684387041391721873743833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262456258027594481249162555 393684387041391721873743833)
        ·
          refine ⟨295263290281043791405307875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393684387041391721873743833 295263290281043791405307875)
          ·
            refine ⟨442894935421565687107961813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295263290281043791405307875 442894935421565687107961813)
            ·
              refine ⟨10380350048942945791592855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 442894935421565687107961813 10380350048942945791592855)
              ·
                refine ⟨15570525073414418687389283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10380350048942945791592855 15570525073414418687389283)
                ·
                  refine ⟨23355787610121628031083925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15570525073414418687389283 23355787610121628031083925)
                  ·
                    refine ⟨1094802544224451313957059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23355787610121628031083925 1094802544224451313957059)
                    ·
                      rfl

theorem cell23_6396361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 6].length) (baseStart_6396361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396361 prefixEnd_6396361 := by exact prefixLift 6396361
  have htrace : WordTrace (prefixWord ++ tailWord_6396361) baseStart_6396361 baseEnd_6396361 := by
    simpa [prefixWord, tailWord_6396361, baseEnd_6396361] using wordTrace_append hprefix tailTrace_6396361
  have hstable : (prefixWord ++ tailWord_6396361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396361).length < 2 ^ (prefixWord ++ tailWord_6396361).sum := by decide
  have hdescent : baseEnd_6396361 < baseStart_6396361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396371 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 3]
def baseStart_6396371 : Nat := 118140960795 + 6396371 * 2 ^ 59
def prefixEnd_6396371 : Nat := 4983230072969 + 3 ^ 40 * 6396371 * 2
def baseEnd_6396371 : Nat := 3284412767479898902746131

theorem tailTrace_6396371 : CollatzResearch.WordTrace tailWord_6396371 prefixEnd_6396371 3284412767479898902746131 := by
  unfold tailWord_6396371
  simp only [CollatzResearch.WordTrace]
  refine ⟨233294816310047755040452967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155529877540031836693635311 233294816310047755040452967)
  ·
    refine ⟨349942224465071632560679451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233294816310047755040452967 349942224465071632560679451)
    ·
      refine ⟨524913336697607448841019177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349942224465071632560679451 524913336697607448841019177)
      ·
        refine ⟨393685002523205586630764383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524913336697607448841019177 393685002523205586630764383)
        ·
          refine ⟨590527503784808379946146575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393685002523205586630764383 590527503784808379946146575)
          ·
            refine ⟨885791255677212569919219863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590527503784808379946146575 885791255677212569919219863)
            ·
              refine ⟨1328686883515818854878829795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885791255677212569919219863 1328686883515818854878829795)
              ·
                refine ⟨1993030325273728282318244693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1328686883515818854878829795 1993030325273728282318244693)
                ·
                  refine ⟨11677912062150751654208465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1993030325273728282318244693 11677912062150751654208465)
                  ·
                    refine ⟨8758434046613063740656349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11677912062150751654208465 8758434046613063740656349)
                    ·
                      refine ⟨3284412767479898902746131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8758434046613063740656349 3284412767479898902746131)
                      ·
                        rfl

theorem cell23_6396371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 3].length) (baseStart_6396371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396371 prefixEnd_6396371 := by exact prefixLift 6396371
  have htrace : WordTrace (prefixWord ++ tailWord_6396371) baseStart_6396371 baseEnd_6396371 := by
    simpa [prefixWord, tailWord_6396371, baseEnd_6396371] using wordTrace_append hprefix tailTrace_6396371
  have hstable : (prefixWord ++ tailWord_6396371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396371).length < 2 ^ (prefixWord ++ tailWord_6396371).sum := by decide
  have hdescent : baseEnd_6396371 < baseStart_6396371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396439 : List Nat := [1, 1, 3, 6, 1, 1, 3, 1, 1, 2, 3]
def baseStart_6396439 : Nat := 118140960795 + 6396439 * 2 ^ 59
def prefixEnd_6396439 : Nat := 4983230072969 + 3 ^ 40 * 6396439 * 2
def baseEnd_6396439 : Nat := 3284447684164404636695819

theorem tailTrace_6396439 : CollatzResearch.WordTrace tailWord_6396439 prefixEnd_6396439 3284447684164404636695819 := by
  unfold tailWord_6396439
  simp only [CollatzResearch.WordTrace]
  refine ⟨233297296473801402653928371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155531530982534268435952247 233297296473801402653928371)
  ·
    refine ⟨349945944710702103980892557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233297296473801402653928371 349945944710702103980892557)
    ·
      refine ⟨131229729266513288992834709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349945944710702103980892557 131229729266513288992834709)
      ·
        refine ⟨6151393559367810421539127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 131229729266513288992834709 6151393559367810421539127)
        ·
          refine ⟨9227090339051715632308691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6151393559367810421539127 9227090339051715632308691)
          ·
            refine ⟨13840635508577573448463037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9227090339051715632308691 13840635508577573448463037)
            ·
              refine ⟨5190238315716590043173639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13840635508577573448463037 5190238315716590043173639)
              ·
                refine ⟨7785357473574885064760459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5190238315716590043173639 7785357473574885064760459)
                ·
                  refine ⟨11678036210362327597140689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7785357473574885064760459 11678036210362327597140689)
                  ·
                    refine ⟨8758527157771745697855517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11678036210362327597140689 8758527157771745697855517)
                    ·
                      refine ⟨3284447684164404636695819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8758527157771745697855517 3284447684164404636695819)
                      ·
                        rfl

theorem cell23_6396439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_6396439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396439 prefixEnd_6396439 := by exact prefixLift 6396439
  have htrace : WordTrace (prefixWord ++ tailWord_6396439) baseStart_6396439 baseEnd_6396439 := by
    simpa [prefixWord, tailWord_6396439, baseEnd_6396439] using wordTrace_append hprefix tailTrace_6396439
  have hstable : (prefixWord ++ tailWord_6396439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396439).length < 2 ^ (prefixWord ++ tailWord_6396439).sum := by decide
  have hdescent : baseEnd_6396439 < baseStart_6396439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396458 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_6396458 : Nat := 118140960795 + 6396458 * 2 ^ 59
def prefixEnd_6396458 : Nat := 4983230072969 + 3 ^ 40 * 6396458 * 2
def baseEnd_6396458 : Nat := 3284457440296840062358231

theorem tailTrace_6396458 : CollatzResearch.WordTrace tailWord_6396458 prefixEnd_6396458 3284457440296840062358231 := by
  unfold tailWord_6396458
  simp only [CollatzResearch.WordTrace]
  refine ⟨58324497365183142224717507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155531992973821712599246685 58324497365183142224717507)
  ·
    refine ⟨87486746047774713337076261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58324497365183142224717507 87486746047774713337076261)
    ·
      refine ⟨16403764883957758750701799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87486746047774713337076261 16403764883957758750701799)
      ·
        refine ⟨24605647325936638126052699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16403764883957758750701799 24605647325936638126052699)
        ·
          refine ⟨36908470988904957189079049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24605647325936638126052699 36908470988904957189079049)
          ·
            refine ⟨27681353241678717891809287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36908470988904957189079049 27681353241678717891809287)
            ·
              refine ⟨41522029862518076837713931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27681353241678717891809287 41522029862518076837713931)
              ·
                refine ⟨62283044793777115256570897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41522029862518076837713931 62283044793777115256570897)
                ·
                  refine ⟨46712283595332836442428173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62283044793777115256570897 46712283595332836442428173)
                  ·
                    refine ⟨17517106348249813665910565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46712283595332836442428173 17517106348249813665910565)
                    ·
                      refine ⟨3284457440296840062358231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17517106348249813665910565 3284457440296840062358231)
                      ·
                        rfl

theorem cell23_6396458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_6396458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396458 prefixEnd_6396458 := by exact prefixLift 6396458
  have htrace : WordTrace (prefixWord ++ tailWord_6396458) baseStart_6396458 baseEnd_6396458 := by
    simpa [prefixWord, tailWord_6396458, baseEnd_6396458] using wordTrace_append hprefix tailTrace_6396458
  have hstable : (prefixWord ++ tailWord_6396458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396458).length < 2 ^ (prefixWord ++ tailWord_6396458).sum := by decide
  have hdescent : baseEnd_6396458 < baseStart_6396458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396521 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 7]
def baseStart_6396521 : Nat := 118140960795 + 6396521 * 2 ^ 59
def prefixEnd_6396521 : Nat := 4983230072969 + 3 ^ 40 * 6396521 * 2
def baseEnd_6396521 : Nat := 3284489789578073315870441

theorem tailTrace_6396521 : CollatzResearch.WordTrace tailWord_6396521 prefixEnd_6396521 3284489789578073315870441 := by
  unfold tailWord_6396521
  simp only [CollatzResearch.WordTrace]
  refine ⟨233300287259504330658413417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155533524839669553772275611 233300287259504330658413417)
  ·
    refine ⟨174975215444628247993810063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233300287259504330658413417 174975215444628247993810063)
    ·
      refine ⟨262462823166942371990715095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174975215444628247993810063 262462823166942371990715095)
      ·
        refine ⟨393694234750413557986072643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262462823166942371990715095 393694234750413557986072643)
        ·
          refine ⟨590541352125620336979108965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393694234750413557986072643 590541352125620336979108965)
          ·
            refine ⟨110726503523553813183582931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 590541352125620336979108965 110726503523553813183582931)
            ·
              refine ⟨166089755285330719775374397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110726503523553813183582931 166089755285330719775374397)
              ·
                refine ⟨62283658231999019915765399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166089755285330719775374397 62283658231999019915765399)
                ·
                  refine ⟨93425487347998529873648099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62283658231999019915765399 93425487347998529873648099)
                  ·
                    refine ⟨140138231021997794810472149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93425487347998529873648099 140138231021997794810472149)
                    ·
                      refine ⟨3284489789578073315870441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140138231021997794810472149 3284489789578073315870441)
                      ·
                        rfl

theorem cell23_6396521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_6396521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396521 prefixEnd_6396521 := by exact prefixLift 6396521
  have htrace : WordTrace (prefixWord ++ tailWord_6396521) baseStart_6396521 baseEnd_6396521 := by
    simpa [prefixWord, tailWord_6396521, baseEnd_6396521] using wordTrace_append hprefix tailTrace_6396521
  have hstable : (prefixWord ++ tailWord_6396521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396521).length < 2 ^ (prefixWord ++ tailWord_6396521).sum := by decide
  have hdescent : baseEnd_6396521 < baseStart_6396521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396525 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_6396525 : Nat := 118140960795 + 6396525 * 2 ^ 59
def prefixEnd_6396525 : Nat := 4983230072969 + 3 ^ 40 * 6396525 * 2
def baseEnd_6396525 : Nat := 3284491843500691300220423

theorem tailTrace_6396525 : CollatzResearch.WordTrace tailWord_6396525 prefixEnd_6396525 3284491843500691300220423 := by
  unfold tailWord_6396525
  simp only [CollatzResearch.WordTrace]
  refine ⟨233300433151489839341559029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155533622100993226227706019 233300433151489839341559029)
  ·
    refine ⟨21871915607952172438271159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 233300433151489839341559029 21871915607952172438271159)
    ·
      refine ⟨32807873411928258657406739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21871915607952172438271159 32807873411928258657406739)
      ·
        refine ⟨49211810117892387986110109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32807873411928258657406739 49211810117892387986110109)
        ·
          refine ⟨18454428794209645494791291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49211810117892387986110109 18454428794209645494791291)
          ·
            refine ⟨27681643191314468242186937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18454428794209645494791291 27681643191314468242186937)
            ·
              refine ⟨20761232393485851181640203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27681643191314468242186937 20761232393485851181640203)
              ·
                refine ⟨31141848590228776772460305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20761232393485851181640203 31141848590228776772460305)
                ·
                  refine ⟨23356386442671582579345229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31141848590228776772460305 23356386442671582579345229)
                  ·
                    refine ⟨8758644916001843467254461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23356386442671582579345229 8758644916001843467254461)
                    ·
                      refine ⟨3284491843500691300220423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8758644916001843467254461 3284491843500691300220423)
                      ·
                        rfl

theorem cell23_6396525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_6396525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396525 prefixEnd_6396525 := by exact prefixLift 6396525
  have htrace : WordTrace (prefixWord ++ tailWord_6396525) baseStart_6396525 baseEnd_6396525 := by
    simpa [prefixWord, tailWord_6396525, baseEnd_6396525] using wordTrace_append hprefix tailTrace_6396525
  have hstable : (prefixWord ++ tailWord_6396525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396525).length < 2 ^ (prefixWord ++ tailWord_6396525).sum := by decide
  have hdescent : baseEnd_6396525 < baseStart_6396525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396526 : List Nat := [4, 1, 2, 2, 2, 2, 3, 1, 2, 2, 2]
def baseStart_6396526 : Nat := 118140960795 + 6396526 * 2 ^ 59
def prefixEnd_6396526 : Nat := 4983230072969 + 3 ^ 40 * 6396526 * 2
def baseEnd_6396526 : Nat := 3284492356981345796307919

theorem tailTrace_6396526 : CollatzResearch.WordTrace tailWord_6396526 prefixEnd_6396526 3284492356981345796307919 := by
  unfold tailWord_6396526
  simp only [CollatzResearch.WordTrace]
  refine ⟨29162558703060777064043179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155533646416324144341563621 29162558703060777064043179)
  ·
    refine ⟨43743838054591165596064769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29162558703060777064043179 43743838054591165596064769)
    ·
      refine ⟨32807878540943374197048577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43743838054591165596064769 32807878540943374197048577)
      ·
        refine ⟨24605908905707530647786433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32807878540943374197048577 24605908905707530647786433)
        ·
          refine ⟨18454431679280647985839825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24605908905707530647786433 18454431679280647985839825)
          ·
            refine ⟨13840823759460485989379869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18454431679280647985839825 13840823759460485989379869)
            ·
              refine ⟨5190308909797682246017451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13840823759460485989379869 5190308909797682246017451)
              ·
                refine ⟨7785463364696523369026177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5190308909797682246017451 7785463364696523369026177)
                ·
                  refine ⟨5839097523522392526769633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7785463364696523369026177 5839097523522392526769633)
                  ·
                    refine ⟨4379323142641794395077225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5839097523522392526769633 4379323142641794395077225)
                    ·
                      refine ⟨3284492356981345796307919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4379323142641794395077225 3284492356981345796307919)
                      ·
                        rfl

theorem cell23_6396526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_6396526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396526 prefixEnd_6396526 := by exact prefixLift 6396526
  have htrace : WordTrace (prefixWord ++ tailWord_6396526) baseStart_6396526 baseEnd_6396526 := by
    simpa [prefixWord, tailWord_6396526, baseEnd_6396526] using wordTrace_append hprefix tailTrace_6396526
  have hstable : (prefixWord ++ tailWord_6396526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396526).length < 2 ^ (prefixWord ++ tailWord_6396526).sum := by decide
  have hdescent : baseEnd_6396526 < baseStart_6396526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396615 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 7, 1, 3]
def baseStart_6396615 : Nat := 118140960795 + 6396615 * 2 ^ 59
def prefixEnd_6396615 : Nat := 4983230072969 + 3 ^ 40 * 6396615 * 2
def baseEnd_6396615 : Nat := 3284538056759595948095009

theorem tailTrace_6396615 : CollatzResearch.WordTrace tailWord_6396615 prefixEnd_6396615 3284538056759595948095009 := by
  unfold tailWord_6396615
  simp only [CollatzResearch.WordTrace]
  refine ⟨233303715721163784712335299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155535810480775856474890199 233303715721163784712335299)
  ·
    refine ⟨349955573581745677068502949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233303715721163784712335299 349955573581745677068502949)
    ·
      refine ⟨65616670046577314450344303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349955573581745677068502949 65616670046577314450344303)
      ·
        refine ⟨98425005069865971675516455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65616670046577314450344303 98425005069865971675516455)
        ·
          refine ⟨147637507604798957513274683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98425005069865971675516455 147637507604798957513274683)
          ·
            refine ⟨221456261407198436269912025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147637507604798957513274683 221456261407198436269912025)
            ·
              refine ⟨166092196055398827202434019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221456261407198436269912025 166092196055398827202434019)
              ·
                refine ⟨249138294083098240803651029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166092196055398827202434019 249138294083098240803651029)
                ·
                  refine ⟨5839178767572615018835571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 249138294083098240803651029 5839178767572615018835571)
                  ·
                    refine ⟨8758768151358922528253357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5839178767572615018835571 8758768151358922528253357)
                    ·
                      refine ⟨3284538056759595948095009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8758768151358922528253357 3284538056759595948095009)
                      ·
                        rfl

theorem cell23_6396615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_6396615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396615 prefixEnd_6396615 := by exact prefixLift 6396615
  have htrace : WordTrace (prefixWord ++ tailWord_6396615) baseStart_6396615 baseEnd_6396615 := by
    simpa [prefixWord, tailWord_6396615, baseEnd_6396615] using wordTrace_append hprefix tailTrace_6396615
  have hstable : (prefixWord ++ tailWord_6396615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396615).length < 2 ^ (prefixWord ++ tailWord_6396615).sum := by decide
  have hdescent : baseEnd_6396615 < baseStart_6396615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396655 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 4]
def baseStart_6396655 : Nat := 118140960795 + 6396655 * 2 ^ 59
def prefixEnd_6396655 : Nat := 4983230072969 + 3 ^ 40 * 6396655 * 2
def baseEnd_6396655 : Nat := 3284558595985775791594825

theorem tailTrace_6396655 : CollatzResearch.WordTrace tailWord_6396655 prefixEnd_6396655 3284558595985775791594825 := by
  unfold tailWord_6396655
  simp only [CollatzResearch.WordTrace]
  refine ⟨233305174641018871543791419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155536783094012581029194279 233305174641018871543791419)
  ·
    refine ⟨349957761961528307315687129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233305174641018871543791419 349957761961528307315687129)
    ·
      refine ⟨262468321471146230486765347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349957761961528307315687129 262468321471146230486765347)
      ·
        refine ⟨393702482206719345730148021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262468321471146230486765347 393702482206719345730148021)
        ·
          refine ⟨36909607706879938662201377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 393702482206719345730148021 36909607706879938662201377)
          ·
            refine ⟨27682205780159953996651033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36909607706879938662201377 27682205780159953996651033)
            ·
              refine ⟨20761654335119965497488275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27682205780159953996651033 20761654335119965497488275)
              ·
                refine ⟨31142481502679948246232413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20761654335119965497488275 31142481502679948246232413)
                ·
                  refine ⟨11678430563504980592337155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31142481502679948246232413 11678430563504980592337155)
                  ·
                    refine ⟨17517645845257470888505733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11678430563504980592337155 17517645845257470888505733)
                    ·
                      refine ⟨3284558595985775791594825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17517645845257470888505733 3284558595985775791594825)
                      ·
                        rfl

theorem cell23_6396655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 4].length) (baseStart_6396655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396655 prefixEnd_6396655 := by exact prefixLift 6396655
  have htrace : WordTrace (prefixWord ++ tailWord_6396655) baseStart_6396655 baseEnd_6396655 := by
    simpa [prefixWord, tailWord_6396655, baseEnd_6396655] using wordTrace_append hprefix tailTrace_6396655
  have hstable : (prefixWord ++ tailWord_6396655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396655).length < 2 ^ (prefixWord ++ tailWord_6396655).sum := by decide
  have hdescent : baseEnd_6396655 < baseStart_6396655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396717 : List Nat := [1, 5, 3, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_6396717 : Nat := 118140960795 + 6396717 * 2 ^ 59
def prefixEnd_6396717 : Nat := 4983230072969 + 3 ^ 40 * 6396717 * 2
def baseEnd_6396717 : Nat := 3284590431786354549019541

theorem tailTrace_6396717 : CollatzResearch.WordTrace tailWord_6396717 prefixEnd_6396717 3284590431786354549019541 := by
  unfold tailWord_6396717
  simp only [CollatzResearch.WordTrace]
  refine ⟨233307435966794256132548405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155538290644529504088365603 233307435966794256132548405)
  ·
    refine ⟨21872572121886961512426413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 233307435966794256132548405 21872572121886961512426413)
    ·
      refine ⟨8202214545707610567159905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21872572121886961512426413 8202214545707610567159905)
      ·
        refine ⟨6151660909280707925369929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8202214545707610567159905 6151660909280707925369929)
        ·
          refine ⟨4613745681960530944027447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6151660909280707925369929 4613745681960530944027447)
          ·
            refine ⟨6920618522940796416041171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4613745681960530944027447 6920618522940796416041171)
            ·
              refine ⟨10380927784411194624061757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6920618522940796416041171 10380927784411194624061757)
              ·
                refine ⟨3892847919154197984023159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10380927784411194624061757 3892847919154197984023159)
                ·
                  refine ⟨5839271878731296976034739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3892847919154197984023159 5839271878731296976034739)
                  ·
                    refine ⟨8758907818096945464052109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5839271878731296976034739 8758907818096945464052109)
                    ·
                      refine ⟨3284590431786354549019541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8758907818096945464052109 3284590431786354549019541)
                      ·
                        rfl

theorem cell23_6396717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_6396717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396717 prefixEnd_6396717 := by exact prefixLift 6396717
  have htrace : WordTrace (prefixWord ++ tailWord_6396717) baseStart_6396717 baseEnd_6396717 := by
    simpa [prefixWord, tailWord_6396717, baseEnd_6396717] using wordTrace_append hprefix tailTrace_6396717
  have hstable : (prefixWord ++ tailWord_6396717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396717).length < 2 ^ (prefixWord ++ tailWord_6396717).sum := by decide
  have hdescent : baseEnd_6396717 < baseStart_6396717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396722 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3]
def baseStart_6396722 : Nat := 118140960795 + 6396722 * 2 ^ 59
def prefixEnd_6396722 : Nat := 4983230072969 + 3 ^ 40 * 6396722 * 2
def baseEnd_6396722 : Nat := 3284592999189627029457017

theorem tailTrace_6396722 : CollatzResearch.WordTrace tailWord_6396722 prefixEnd_6396722 3284592999189627029457017 := by
  unfold tailWord_6396722
  simp only [CollatzResearch.WordTrace]
  refine ⟨58326904582944035496620105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155538412221184094657653613 58326904582944035496620105)
  ·
    refine ⟨43745178437208026622465079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58326904582944035496620105 43745178437208026622465079)
    ·
      refine ⟨65617767655812039933697619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43745178437208026622465079 65617767655812039933697619)
      ·
        refine ⟨98426651483718059900546429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65617767655812039933697619 98426651483718059900546429)
        ·
          refine ⟨36909994306394272462704911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98426651483718059900546429 36909994306394272462704911)
          ·
            refine ⟨55364991459591408694057367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36909994306394272462704911 55364991459591408694057367)
            ·
              refine ⟨83047487189387113041086051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55364991459591408694057367 83047487189387113041086051)
              ·
                refine ⟨124571230784080669561629077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83047487189387113041086051 124571230784080669561629077)
                ·
                  refine ⟨5839276443003781385701363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124571230784080669561629077 5839276443003781385701363)
                  ·
                    refine ⟨8758914664505672078552045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5839276443003781385701363 8758914664505672078552045)
                    ·
                      refine ⟨3284592999189627029457017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8758914664505672078552045 3284592999189627029457017)
                      ·
                        rfl

theorem cell23_6396722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_6396722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396722 prefixEnd_6396722 := by exact prefixLift 6396722
  have htrace : WordTrace (prefixWord ++ tailWord_6396722) baseStart_6396722 baseEnd_6396722 := by
    simpa [prefixWord, tailWord_6396722, baseEnd_6396722] using wordTrace_append hprefix tailTrace_6396722
  have hstable : (prefixWord ++ tailWord_6396722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396722).length < 2 ^ (prefixWord ++ tailWord_6396722).sum := by decide
  have hdescent : baseEnd_6396722 < baseStart_6396722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396723 : List Nat := [1, 1, 1, 2, 6, 3, 1, 3, 1, 2, 2]
def baseStart_6396723 : Nat := 118140960795 + 6396723 * 2 ^ 59
def prefixEnd_6396723 : Nat := 4983230072969 + 3 ^ 40 * 6396723 * 2
def baseEnd_6396723 : Nat := 3284593512670281525544513

theorem tailTrace_6396723 : CollatzResearch.WordTrace tailWord_6396723 prefixEnd_6396723 3284593512670281525544513 := by
  unfold tailWord_6396723
  simp only [CollatzResearch.WordTrace]
  refine ⟨233307654804772519157266823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155538436536515012771511215 233307654804772519157266823)
  ·
    refine ⟨349961482207158778735900235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233307654804772519157266823 349961482207158778735900235)
    ·
      refine ⟨524942223310738168103850353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349961482207158778735900235 524942223310738168103850353)
      ·
        refine ⟨393706667483053626077887765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524942223310738168103850353 393706667483053626077887765)
        ·
          refine ⟨18455000038268138722400989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 393706667483053626077887765 18455000038268138722400989)
          ·
            refine ⟨6920625014350552020900371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18455000038268138722400989 6920625014350552020900371)
            ·
              refine ⟨10380937521525828031350557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6920625014350552020900371 10380937521525828031350557)
              ·
                refine ⟨3892851570572185511756459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10380937521525828031350557 3892851570572185511756459)
                ·
                  refine ⟨5839277355858278267634689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3892851570572185511756459 5839277355858278267634689)
                  ·
                    refine ⟨4379458016893708700726017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5839277355858278267634689 4379458016893708700726017)
                    ·
                      refine ⟨3284593512670281525544513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4379458016893708700726017 3284593512670281525544513)
                      ·
                        rfl

theorem cell23_6396723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 1, 2, 2].length) (baseStart_6396723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396723 prefixEnd_6396723 := by exact prefixLift 6396723
  have htrace : WordTrace (prefixWord ++ tailWord_6396723) baseStart_6396723 baseEnd_6396723 := by
    simpa [prefixWord, tailWord_6396723, baseEnd_6396723] using wordTrace_append hprefix tailTrace_6396723
  have hstable : (prefixWord ++ tailWord_6396723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396723).length < 2 ^ (prefixWord ++ tailWord_6396723).sum := by decide
  have hdescent : baseEnd_6396723 < baseStart_6396723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396732 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 5, 3, 2]
def baseStart_6396732 : Nat := 118140960795 + 6396732 * 2 ^ 59
def prefixEnd_6396732 : Nat := 4983230072969 + 3 ^ 40 * 6396732 * 2
def baseEnd_6396732 : Nat := 3284598133996171990331971

theorem tailTrace_6396732 : CollatzResearch.WordTrace tailWord_6396732 prefixEnd_6396732 3284598133996171990331971 := by
  unfold tailWord_6396732
  simp only [CollatzResearch.WordTrace]
  refine ⟨116653991530869956847172225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155538655374493275796229633 116653991530869956847172225)
  ·
    refine ⟨87490493648152467635379169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116653991530869956847172225 87490493648152467635379169)
    ·
      refine ⟨65617870236114350726534377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87490493648152467635379169 65617870236114350726534377)
      ·
        refine ⟨49213402677085763044900783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65617870236114350726534377 49213402677085763044900783)
        ·
          refine ⟨73820104015628644567351175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49213402677085763044900783 73820104015628644567351175)
          ·
            refine ⟨110730156023442966851026763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73820104015628644567351175 110730156023442966851026763)
            ·
              refine ⟨166095234035164450276540145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110730156023442966851026763 166095234035164450276540145)
              ·
                refine ⟨124571425526373337707405109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166095234035164450276540145 124571425526373337707405109)
                ·
                  refine ⟨11678571143097500410069229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124571425526373337707405109 11678571143097500410069229)
                  ·
                    refine ⟨4379464178661562653775961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11678571143097500410069229 4379464178661562653775961)
                    ·
                      refine ⟨3284598133996171990331971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4379464178661562653775961 3284598133996171990331971)
                      ·
                        rfl

theorem cell23_6396732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_6396732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396732 prefixEnd_6396732 := by exact prefixLift 6396732
  have htrace : WordTrace (prefixWord ++ tailWord_6396732) baseStart_6396732 baseEnd_6396732 := by
    simpa [prefixWord, tailWord_6396732, baseEnd_6396732] using wordTrace_append hprefix tailTrace_6396732
  have hstable : (prefixWord ++ tailWord_6396732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396732).length < 2 ^ (prefixWord ++ tailWord_6396732).sum := by decide
  have hdescent : baseEnd_6396732 < baseStart_6396732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396740 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_6396740 : Nat := 118140960795 + 6396740 * 2 ^ 59
def prefixEnd_6396740 : Nat := 4983230072969 + 3 ^ 40 * 6396740 * 2
def baseEnd_6396740 : Nat := 3284602241841407959031935

theorem tailTrace_6396740 : CollatzResearch.WordTrace tailWord_6396740 prefixEnd_6396740 3284602241841407959031935 := by
  unfold tailWord_6396740
  simp only [CollatzResearch.WordTrace]
  refine ⟨116654137422855465530317837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155538849897140620707090449 116654137422855465530317837)
  ·
    refine ⟨43745301533570799573869189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116654137422855465530317837 43745301533570799573869189)
    ·
      refine ⟨8202244037544524920100473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43745301533570799573869189 8202244037544524920100473)
      ·
        refine ⟨6151683028158393690075355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8202244037544524920100473 6151683028158393690075355)
        ·
          refine ⟨9227524542237590535113033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6151683028158393690075355 9227524542237590535113033)
          ·
            refine ⟨6920643406678192901334775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9227524542237590535113033 6920643406678192901334775)
            ·
              refine ⟨10380965110017289352002163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6920643406678192901334775 10380965110017289352002163)
              ·
                refine ⟨15571447665025934028003245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10380965110017289352002163 15571447665025934028003245)
                ·
                  refine ⟨5839292874384725260501217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15571447665025934028003245 5839292874384725260501217)
                  ·
                    refine ⟨4379469655788543945375913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5839292874384725260501217 4379469655788543945375913)
                    ·
                      refine ⟨3284602241841407959031935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4379469655788543945375913 3284602241841407959031935)
                      ·
                        rfl

theorem cell23_6396740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_6396740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396740 prefixEnd_6396740 := by exact prefixLift 6396740
  have htrace : WordTrace (prefixWord ++ tailWord_6396740) baseStart_6396740 baseEnd_6396740 := by
    simpa [prefixWord, tailWord_6396740, baseEnd_6396740] using wordTrace_append hprefix tailTrace_6396740
  have hstable : (prefixWord ++ tailWord_6396740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396740).length < 2 ^ (prefixWord ++ tailWord_6396740).sum := by decide
  have hdescent : baseEnd_6396740 < baseStart_6396740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396756 : List Nat := [2, 4, 1, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_6396756 : Nat := 118140960795 + 6396756 * 2 ^ 59
def prefixEnd_6396756 : Nat := 4983230072969 + 3 ^ 40 * 6396756 * 2
def baseEnd_6396756 : Nat := 3284610457531879896431861

theorem tailTrace_6396756 : CollatzResearch.WordTrace tailWord_6396756 prefixEnd_6396756 3284610457531879896431861 := by
  unfold tailWord_6396756
  simp only [CollatzResearch.WordTrace]
  refine ⟨116654429206826482896609061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155539238942435310528812081 116654429206826482896609061)
  ·
    refine ⟨21872705476279965543114199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116654429206826482896609061 21872705476279965543114199)
    ·
      refine ⟨32809058214419948314671299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21872705476279965543114199 32809058214419948314671299)
      ·
        refine ⟨49213587321629922472006949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32809058214419948314671299 49213587321629922472006949)
        ·
          refine ⟨9227547622805610463501303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49213587321629922472006949 9227547622805610463501303)
          ·
            refine ⟨13841321434208415695251955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9227547622805610463501303 13841321434208415695251955)
            ·
              refine ⟨20761982151312623542877933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13841321434208415695251955 20761982151312623542877933)
              ·
                refine ⟨7785743306742233828579225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20761982151312623542877933 7785743306742233828579225)
                ·
                  refine ⟨5839307480056675371434419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7785743306742233828579225 5839307480056675371434419)
                  ·
                    refine ⟨8758961220085013057151629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5839307480056675371434419 8758961220085013057151629)
                    ·
                      refine ⟨3284610457531879896431861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8758961220085013057151629 3284610457531879896431861)
                      ·
                        rfl

theorem cell23_6396756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_6396756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396756 prefixEnd_6396756 := by exact prefixLift 6396756
  have htrace : WordTrace (prefixWord ++ tailWord_6396756) baseStart_6396756 baseEnd_6396756 := by
    simpa [prefixWord, tailWord_6396756, baseEnd_6396756] using wordTrace_append hprefix tailTrace_6396756
  have hstable : (prefixWord ++ tailWord_6396756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396756).length < 2 ^ (prefixWord ++ tailWord_6396756).sum := by decide
  have hdescent : baseEnd_6396756 < baseStart_6396756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396832 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 2, 5]
def baseStart_6396832 : Nat := 118140960795 + 6396832 * 2 ^ 59
def prefixEnd_6396832 : Nat := 4983230072969 + 3 ^ 40 * 6396832 * 2
def baseEnd_6396832 : Nat := 1094883160687207199693837

theorem tailTrace_6396832 : CollatzResearch.WordTrace tailWord_6396832 prefixEnd_6396832 1094883160687207199693837 := by
  unfold tailWord_6396832
  simp only [CollatzResearch.WordTrace]
  refine ⟨116655815180688815386492375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155541086907585087181989833 116655815180688815386492375)
  ·
    refine ⟨174983722771033223079738563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116655815180688815386492375 174983722771033223079738563)
    ·
      refine ⟨262475584156549834619607845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174983722771033223079738563 262475584156549834619607845)
      ·
        refine ⟨49214172029353093991176471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262475584156549834619607845 49214172029353093991176471)
        ·
          refine ⟨73821258044029640986764707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49214172029353093991176471 73821258044029640986764707)
          ·
            refine ⟨110731887066044461480147061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73821258044029640986764707 110731887066044461480147061)
            ·
              refine ⟨10381114412441668263763787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110731887066044461480147061 10381114412441668263763787)
              ·
                refine ⟨15571671618662502395645681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10381114412441668263763787 15571671618662502395645681)
                ·
                  refine ⟨11678753713996876796734261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15571671618662502395645681 11678753713996876796734261)
                  ·
                    refine ⟨1094883160687207199693837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11678753713996876796734261 1094883160687207199693837)
                    ·
                      rfl

theorem cell23_6396832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 2, 5].length) (baseStart_6396832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396832 prefixEnd_6396832 := by exact prefixLift 6396832
  have htrace : WordTrace (prefixWord ++ tailWord_6396832) baseStart_6396832 baseEnd_6396832 := by
    simpa [prefixWord, tailWord_6396832, baseEnd_6396832] using wordTrace_append hprefix tailTrace_6396832
  have hstable : (prefixWord ++ tailWord_6396832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396832).length < 2 ^ (prefixWord ++ tailWord_6396832).sum := by decide
  have hdescent : baseEnd_6396832 < baseStart_6396832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396855 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 5]
def baseStart_6396855 : Nat := 118140960795 + 6396855 * 2 ^ 59
def prefixEnd_6396855 : Nat := 4983230072969 + 3 ^ 40 * 6396855 * 2
def baseEnd_6396855 : Nat := 3284661292116675009093905

theorem tailTrace_6396855 : CollatzResearch.WordTrace tailWord_6396855 prefixEnd_6396855 3284661292116675009093905 := by
  unfold tailWord_6396855
  simp only [CollatzResearch.WordTrace]
  refine ⟨233312469240294305701072019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155541646160196203800714679 233312469240294305701072019)
  ·
    refine ⟨349968703860441458551608029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233312469240294305701072019 349968703860441458551608029)
    ·
      refine ⟨131238263947665546956853011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349968703860441458551608029 131238263947665546956853011)
      ·
        refine ⟨196857395921498320435279517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131238263947665546956853011 196857395921498320435279517)
        ·
          refine ⟨73821523470561870163229819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196857395921498320435279517 73821523470561870163229819)
          ·
            refine ⟨110732285205842805244844729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73821523470561870163229819 110732285205842805244844729)
            ·
              refine ⟨83049213904382103933633547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110732285205842805244844729 83049213904382103933633547)
              ·
                refine ⟨124573820856573155900450321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83049213904382103933633547 124573820856573155900450321)
                ·
                  refine ⟨93430365642429866925337741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124573820856573155900450321 93430365642429866925337741)
                  ·
                    refine ⟨35036387115911200097001653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93430365642429866925337741 35036387115911200097001653)
                    ·
                      refine ⟨3284661292116675009093905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35036387115911200097001653 3284661292116675009093905)
                      ·
                        rfl

theorem cell23_6396855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_6396855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396855 prefixEnd_6396855 := by exact prefixLift 6396855
  have htrace : WordTrace (prefixWord ++ tailWord_6396855) baseStart_6396855 baseEnd_6396855 := by
    simpa [prefixWord, tailWord_6396855, baseEnd_6396855] using wordTrace_append hprefix tailTrace_6396855
  have hstable : (prefixWord ++ tailWord_6396855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396855).length < 2 ^ (prefixWord ++ tailWord_6396855).sum := by decide
  have hdescent : baseEnd_6396855 < baseStart_6396855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396913 : List Nat := [1, 2, 2, 2, 4, 2, 3, 2, 1, 4]
def baseStart_6396913 : Nat := 118140960795 + 6396913 * 2 ^ 59
def prefixEnd_6396913 : Nat := 4983230072969 + 3 ^ 40 * 6396913 * 2
def baseEnd_6396913 : Nat := 1094897024664878594056213

theorem tailTrace_6396913 : CollatzResearch.WordTrace tailWord_6396913 prefixEnd_6396913 1094897024664878594056213 := by
  unfold tailWord_6396913
  simp only [CollatzResearch.WordTrace]
  refine ⟨233314584674084181606683393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155543056449389454404455595 233314584674084181606683393)
  ·
    refine ⟨174985938505563136205012545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233314584674084181606683393 174985938505563136205012545)
    ·
      refine ⟨131239453879172352153759409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174985938505563136205012545 131239453879172352153759409)
      ·
        refine ⟨98429590409379264115319557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131239453879172352153759409 98429590409379264115319557)
        ·
          refine ⟨18455548201758612021622417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98429590409379264115319557 18455548201758612021622417)
          ·
            refine ⟨13841661151318959016216813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18455548201758612021622417 13841661151318959016216813)
            ·
              refine ⟨5190622931744609631081305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13841661151318959016216813 5190622931744609631081305)
              ·
                refine ⟨3892967198808457223310979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5190622931744609631081305 3892967198808457223310979)
                ·
                  refine ⟨5839450798212685834966469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3892967198808457223310979 5839450798212685834966469)
                  ·
                    refine ⟨1094897024664878594056213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5839450798212685834966469 1094897024664878594056213)
                    ·
                      rfl

theorem cell23_6396913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 1, 4].length) (baseStart_6396913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396913 prefixEnd_6396913 := by exact prefixLift 6396913
  have htrace : WordTrace (prefixWord ++ tailWord_6396913) baseStart_6396913 baseEnd_6396913 := by
    simpa [prefixWord, tailWord_6396913, baseEnd_6396913] using wordTrace_append hprefix tailTrace_6396913
  have hstable : (prefixWord ++ tailWord_6396913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396913).length < 2 ^ (prefixWord ++ tailWord_6396913).sum := by decide
  have hdescent : baseEnd_6396913 < baseStart_6396913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396915 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 7]
def baseStart_6396915 : Nat := 118140960795 + 6396915 * 2 ^ 59
def prefixEnd_6396915 : Nat := 4983230072969 + 3 ^ 40 * 6396915 * 2
def baseEnd_6396915 : Nat := 3284692100955944774343629

theorem tailTrace_6396915 : CollatzResearch.WordTrace tailWord_6396915 prefixEnd_6396915 3284692100955944774343629 := by
  unfold tailWord_6396915
  simp only [CollatzResearch.WordTrace]
  refine ⟨233314657620076935948256199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155543105080051290632170799 233314657620076935948256199)
  ·
    refine ⟨349971986430115403922384299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233314657620076935948256199 349971986430115403922384299)
    ·
      refine ⟨524957979645173105883576449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349971986430115403922384299 524957979645173105883576449)
      ·
        refine ⟨393718484733879829412682337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524957979645173105883576449 393718484733879829412682337)
        ·
          refine ⟨295288863550409872059511753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393718484733879829412682337 295288863550409872059511753)
          ·
            refine ⟨221466647662807404044633815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295288863550409872059511753 221466647662807404044633815)
            ·
              refine ⟨332199971494211106066950723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221466647662807404044633815 332199971494211106066950723)
              ·
                refine ⟨498299957241316659100426085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332199971494211106066950723 498299957241316659100426085)
                ·
                  refine ⟨93431241982746873581329891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 498299957241316659100426085 93431241982746873581329891)
                  ·
                    refine ⟨140146862974120310371994837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93431241982746873581329891 140146862974120310371994837)
                    ·
                      refine ⟨3284692100955944774343629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140146862974120310371994837 3284692100955944774343629)
                      ·
                        rfl

theorem cell23_6396915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_6396915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396915 prefixEnd_6396915 := by exact prefixLift 6396915
  have htrace : WordTrace (prefixWord ++ tailWord_6396915) baseStart_6396915 baseEnd_6396915 := by
    simpa [prefixWord, tailWord_6396915, baseEnd_6396915] using wordTrace_append hprefix tailTrace_6396915
  have hstable : (prefixWord ++ tailWord_6396915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396915).length < 2 ^ (prefixWord ++ tailWord_6396915).sum := by decide
  have hdescent : baseEnd_6396915 < baseStart_6396915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396926 : List Nat := [4, 2, 2, 2, 2, 1, 1, 3, 6]
def baseStart_6396926 : Nat := 118140960795 + 6396926 * 2 ^ 59
def prefixEnd_6396926 : Nat := 4983230072969 + 3 ^ 40 * 6396926 * 2
def baseEnd_6396926 : Nat := 364966416582571581256231

theorem tailTrace_6396926 : CollatzResearch.WordTrace tailWord_6396926 prefixEnd_6396926 364966416582571581256231 := by
  unfold tailWord_6396926
  simp only [CollatzResearch.WordTrace]
  refine ⟨29164382352879635603363329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155543372548691389884604421 29164382352879635603363329)
  ·
    refine ⟨21873286764659726702522497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29164382352879635603363329 21873286764659726702522497)
    ·
      refine ⟨16404965073494795026891873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21873286764659726702522497 16404965073494795026891873)
      ·
        refine ⟨12303723805121096270168905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16404965073494795026891873 12303723805121096270168905)
        ·
          refine ⟨9227792853840822202626679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12303723805121096270168905 9227792853840822202626679)
          ·
            refine ⟨13841689280761233303940019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9227792853840822202626679 13841689280761233303940019)
            ·
              refine ⟨20762533921141849955910029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13841689280761233303940019 20762533921141849955910029)
              ·
                refine ⟨7785950220428193733466261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20762533921141849955910029 7785950220428193733466261)
                ·
                  refine ⟨364966416582571581256231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7785950220428193733466261 364966416582571581256231)
                  ·
                    rfl

theorem cell23_6396926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_6396926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396926 prefixEnd_6396926 := by exact prefixLift 6396926
  have htrace : WordTrace (prefixWord ++ tailWord_6396926) baseStart_6396926 baseEnd_6396926 := by
    simpa [prefixWord, tailWord_6396926, baseEnd_6396926] using wordTrace_append hprefix tailTrace_6396926
  have hstable : (prefixWord ++ tailWord_6396926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396926).length < 2 ^ (prefixWord ++ tailWord_6396926).sum := by decide
  have hdescent : baseEnd_6396926 < baseStart_6396926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396939 : List Nat := [1, 1, 1, 1, 6, 2, 3, 2, 1, 5]
def baseStart_6396939 : Nat := 118140960795 + 6396939 * 2 ^ 59
def prefixEnd_6396939 : Nat := 4983230072969 + 3 ^ 40 * 6396939 * 2
def baseEnd_6396939 : Nat := 1094901474830550893481173

theorem tailTrace_6396939 : CollatzResearch.WordTrace tailWord_6396939 prefixEnd_6396939 1094901474830550893481173 := by
  unfold tailWord_6396939
  simp only [CollatzResearch.WordTrace]
  refine ⟨233315532971989988047129871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155543688647993325364753247 233315532971989988047129871)
  ·
    refine ⟨349973299457984982070694807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233315532971989988047129871 349973299457984982070694807)
    ·
      refine ⟨524959949186977473106042211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349973299457984982070694807 524959949186977473106042211)
      ·
        refine ⟨787439923780466209659063317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524959949186977473106042211 787439923780466209659063317)
        ·
          refine ⟨36911246427209353577768593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 787439923780466209659063317 36911246427209353577768593)
          ·
            refine ⟨27683434820407015183326445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36911246427209353577768593 27683434820407015183326445)
            ·
              refine ⟨10381288057652630693747417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27683434820407015183326445 10381288057652630693747417)
              ·
                refine ⟨7785966043239473020310563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10381288057652630693747417 7785966043239473020310563)
                ·
                  refine ⟨11678949064859209530465845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7785966043239473020310563 11678949064859209530465845)
                  ·
                    refine ⟨1094901474830550893481173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11678949064859209530465845 1094901474830550893481173)
                    ·
                      rfl

theorem cell23_6396939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 5].length) (baseStart_6396939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396939 prefixEnd_6396939 := by exact prefixLift 6396939
  have htrace : WordTrace (prefixWord ++ tailWord_6396939) baseStart_6396939 baseEnd_6396939 := by
    simpa [prefixWord, tailWord_6396939, baseEnd_6396939] using wordTrace_append hprefix tailTrace_6396939
  have hstable : (prefixWord ++ tailWord_6396939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396939).length < 2 ^ (prefixWord ++ tailWord_6396939).sum := by decide
  have hdescent : baseEnd_6396939 < baseStart_6396939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396952 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 3, 6]
def baseStart_6396952 : Nat := 118140960795 + 6396952 * 2 ^ 59
def prefixEnd_6396952 : Nat := 4983230072969 + 3 ^ 40 * 6396952 * 2
def baseEnd_6396952 : Nat := 1094903699913387043193653

theorem tailTrace_6396952 : CollatzResearch.WordTrace tailWord_6396952 prefixEnd_6396952 1094903699913387043193653 := by
  unfold tailWord_6396952
  simp only [CollatzResearch.WordTrace]
  refine ⟨116658003560471445633676555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155544004747295260844902073 116658003560471445633676555)
  ·
    refine ⟨174987005340707168450514833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116658003560471445633676555 174987005340707168450514833)
    ·
      refine ⟨131240254005530376337886125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174987005340707168450514833 131240254005530376337886125)
      ·
        refine ⟨49215095252073891126707297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131240254005530376337886125 49215095252073891126707297)
        ·
          refine ⟨36911321439055418345030473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49215095252073891126707297 36911321439055418345030473)
          ·
            refine ⟨27683491079291563758772855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36911321439055418345030473 27683491079291563758772855)
            ·
              refine ⟨41525236618937345638159283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27683491079291563758772855 41525236618937345638159283)
              ·
                refine ⟨62287854928406018457238925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41525236618937345638159283 62287854928406018457238925)
                ·
                  refine ⟨23357945598152256921464597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62287854928406018457238925 23357945598152256921464597)
                  ·
                    refine ⟨1094903699913387043193653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23357945598152256921464597 1094903699913387043193653)
                    ·
                      rfl

theorem cell23_6396952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_6396952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396952 prefixEnd_6396952 := by exact prefixLift 6396952
  have htrace : WordTrace (prefixWord ++ tailWord_6396952) baseStart_6396952 baseEnd_6396952 := by
    simpa [prefixWord, tailWord_6396952, baseEnd_6396952] using wordTrace_append hprefix tailTrace_6396952
  have hstable : (prefixWord ++ tailWord_6396952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396952).length < 2 ^ (prefixWord ++ tailWord_6396952).sum := by decide
  have hdescent : baseEnd_6396952 < baseStart_6396952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396970 : List Nat := [3, 1, 4, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_6396970 : Nat := 118140960795 + 6396970 * 2 ^ 59
def prefixEnd_6396970 : Nat := 4983230072969 + 3 ^ 40 * 6396970 * 2
def baseEnd_6396970 : Nat := 3284720342391942059155877

theorem tailTrace_6396970 : CollatzResearch.WordTrace tailWord_6396970 prefixEnd_6396970 3284720342391942059155877 := by
  unfold tailWord_6396970
  simp only [CollatzResearch.WordTrace]
  refine ⟨58329165908719420085377091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155544442423251786894338909 58329165908719420085377091)
  ·
    refine ⟨87493748863079130128065637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58329165908719420085377091 87493748863079130128065637)
    ·
      refine ⟨16405077911827336899012307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87493748863079130128065637 16405077911827336899012307)
      ·
        refine ⟨24607616867741005348518461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16405077911827336899012307 24607616867741005348518461)
        ·
          refine ⟨9227856325402877005694423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24607616867741005348518461 9227856325402877005694423)
          ·
            refine ⟨13841784488104315508541635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9227856325402877005694423 13841784488104315508541635)
            ·
              refine ⟨20762676732156473262812453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13841784488104315508541635 20762676732156473262812453)
              ·
                refine ⟨3893001887279338736777335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20762676732156473262812453 3893001887279338736777335)
                ·
                  refine ⟨5839502830919008105166003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3893001887279338736777335 5839502830919008105166003)
                  ·
                    refine ⟨8759254246378512157749005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5839502830919008105166003 8759254246378512157749005)
                    ·
                      refine ⟨3284720342391942059155877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8759254246378512157749005 3284720342391942059155877)
                      ·
                        rfl

theorem cell23_6396970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_6396970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396970 prefixEnd_6396970 := by exact prefixLift 6396970
  have htrace : WordTrace (prefixWord ++ tailWord_6396970) baseStart_6396970 baseEnd_6396970 := by
    simpa [prefixWord, tailWord_6396970, baseEnd_6396970] using wordTrace_append hprefix tailTrace_6396970
  have hstable : (prefixWord ++ tailWord_6396970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396970).length < 2 ^ (prefixWord ++ tailWord_6396970).sum := by decide
  have hdescent : baseEnd_6396970 < baseStart_6396970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396972 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 4]
def baseStart_6396972 : Nat := 118140960795 + 6396972 * 2 ^ 59
def prefixEnd_6396972 : Nat := 4983230072969 + 3 ^ 40 * 6396972 * 2
def baseEnd_6396972 : Nat := 3284721369353251051330867

theorem tailTrace_6396972 : CollatzResearch.WordTrace tailWord_6396972 prefixEnd_6396972 3284721369353251051330867 := by
  unfold tailWord_6396972
  simp only [CollatzResearch.WordTrace]
  refine ⟨116658368290435217341540585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155544491053913623122054113 116658368290435217341540585)
  ·
    refine ⟨87493776217826413006155439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116658368290435217341540585 87493776217826413006155439)
    ·
      refine ⟨131240664326739619509233159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87493776217826413006155439 131240664326739619509233159)
      ·
        refine ⟨196860996490109429263849739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131240664326739619509233159 196860996490109429263849739)
        ·
          refine ⟨295291494735164143895774609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196860996490109429263849739 295291494735164143895774609)
          ·
            refine ⟨221468621051373107921830957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295291494735164143895774609 221468621051373107921830957)
            ·
              refine ⟨83050732894264915470686609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221468621051373107921830957 83050732894264915470686609)
              ·
                refine ⟨62288049670698686603014957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83050732894264915470686609 62288049670698686603014957)
                ·
                  refine ⟨23358018626512007476130609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62288049670698686603014957 23358018626512007476130609)
                  ·
                    refine ⟨17518513969884005607097957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23358018626512007476130609 17518513969884005607097957)
                    ·
                      refine ⟨3284721369353251051330867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17518513969884005607097957 3284721369353251051330867)
                      ·
                        rfl

theorem cell23_6396972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_6396972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396972 prefixEnd_6396972 := by exact prefixLift 6396972
  have htrace : WordTrace (prefixWord ++ tailWord_6396972) baseStart_6396972 baseEnd_6396972 := by
    simpa [prefixWord, tailWord_6396972, baseEnd_6396972] using wordTrace_append hprefix tailTrace_6396972
  have hstable : (prefixWord ++ tailWord_6396972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396972).length < 2 ^ (prefixWord ++ tailWord_6396972).sum := by decide
  have hdescent : baseEnd_6396972 < baseStart_6396972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396976 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 3, 2, 2]
def baseStart_6396976 : Nat := 118140960795 + 6396976 * 2 ^ 59
def prefixEnd_6396976 : Nat := 4983230072969 + 3 ^ 40 * 6396976 * 2
def baseEnd_6396976 : Nat := 3284723423275869035680849

theorem tailTrace_6396976 : CollatzResearch.WordTrace tailWord_6396976 prefixEnd_6396976 3284723423275869035680849 := by
  unfold tailWord_6396976
  simp only [CollatzResearch.WordTrace]
  refine ⟨116658441236427971683113391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155544588315237295577484521 116658441236427971683113391)
  ·
    refine ⟨174987661854641957524670087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116658441236427971683113391 174987661854641957524670087)
    ·
      refine ⟨262481492781962936287005131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174987661854641957524670087 262481492781962936287005131)
      ·
        refine ⟨393722239172944404430507697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262481492781962936287005131 393722239172944404430507697)
        ·
          refine ⟨295291679379708303322880773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393722239172944404430507697 295291679379708303322880773)
          ·
            refine ⟨55367189883695306873040145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 295291679379708303322880773 55367189883695306873040145)
            ·
              refine ⟨41525392412771480154780109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55367189883695306873040145 41525392412771480154780109)
              ·
                refine ⟨15572022154789305058042541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41525392412771480154780109 15572022154789305058042541)
                ·
                  refine ⟨5839508308045989396765953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15572022154789305058042541 5839508308045989396765953)
                  ·
                    refine ⟨4379631231034492047574465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5839508308045989396765953 4379631231034492047574465)
                    ·
                      refine ⟨3284723423275869035680849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4379631231034492047574465 3284723423275869035680849)
                      ·
                        rfl

theorem cell23_6396976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 3, 2, 2].length) (baseStart_6396976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396976 prefixEnd_6396976 := by exact prefixLift 6396976
  have htrace : WordTrace (prefixWord ++ tailWord_6396976) baseStart_6396976 baseEnd_6396976 := by
    simpa [prefixWord, tailWord_6396976, baseEnd_6396976] using wordTrace_append hprefix tailTrace_6396976
  have hstable : (prefixWord ++ tailWord_6396976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396976).length < 2 ^ (prefixWord ++ tailWord_6396976).sum := by decide
  have hdescent : baseEnd_6396976 < baseStart_6396976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396989 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_6396989 : Nat := 118140960795 + 6396989 * 2 ^ 59
def prefixEnd_6396989 : Nat := 4983230072969 + 3 ^ 40 * 6396989 * 2
def baseEnd_6396989 : Nat := 3284730098524377484818289

theorem tailTrace_6396989 : CollatzResearch.WordTrace tailWord_6396989 prefixEnd_6396989 3284730098524377484818289 := by
  unfold tailWord_6396989
  simp only [CollatzResearch.WordTrace]
  refine ⟨233317356621808846586450021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155544904414539231057633347 233317356621808846586450021)
  ·
    refine ⟨43747004366589158734959379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233317356621808846586450021 43747004366589158734959379)
    ·
      refine ⟨65620506549883738102439069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43747004366589158734959379 65620506549883738102439069)
      ·
        refine ⟨24607689956206401788414651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65620506549883738102439069 24607689956206401788414651)
        ·
          refine ⟨36911534934309602682621977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24607689956206401788414651 36911534934309602682621977)
          ·
            refine ⟨27683651200732202011966483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36911534934309602682621977 27683651200732202011966483)
            ·
              refine ⟨41525476801098303017949725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27683651200732202011966483 41525476801098303017949725)
              ·
                refine ⟨15572053800411863631731147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41525476801098303017949725 15572053800411863631731147)
                ·
                  refine ⟨23358080700617795447596721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15572053800411863631731147 23358080700617795447596721)
                  ·
                    refine ⟨17518560525463346585697541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23358080700617795447596721 17518560525463346585697541)
                    ·
                      refine ⟨3284730098524377484818289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17518560525463346585697541 3284730098524377484818289)
                      ·
                        rfl

theorem cell23_6396989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_6396989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396989 prefixEnd_6396989 := by exact prefixLift 6396989
  have htrace : WordTrace (prefixWord ++ tailWord_6396989) baseStart_6396989 baseEnd_6396989 := by
    simpa [prefixWord, tailWord_6396989, baseEnd_6396989] using wordTrace_append hprefix tailTrace_6396989
  have hstable : (prefixWord ++ tailWord_6396989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396989).length < 2 ^ (prefixWord ++ tailWord_6396989).sum := by decide
  have hdescent : baseEnd_6396989 < baseStart_6396989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6396999 : List Nat := [1, 1, 4, 1, 3, 3, 3, 7]
def baseStart_6396999 : Nat := 118140960795 + 6396999 * 2 ^ 59
def prefixEnd_6396999 : Nat := 4983230072969 + 3 ^ 40 * 6396999 * 2
def baseEnd_6396999 : Nat := 121656860493737868359009

theorem tailTrace_6396999 : CollatzResearch.WordTrace tailWord_6396999 prefixEnd_6396999 121656860493737868359009 := by
  unfold tailWord_6396999
  simp only [CollatzResearch.WordTrace]
  refine ⟨233317721351772618294314051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155545147567848412196209367 233317721351772618294314051)
  ·
    refine ⟨349976582027658927441471077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233317721351772618294314051 349976582027658927441471077)
    ·
      refine ⟨65620609130186048895275827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 349976582027658927441471077 65620609130186048895275827)
      ·
        refine ⟨98430913695279073342913741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65620609130186048895275827 98430913695279073342913741)
        ·
          refine ⟨36911592635729652503592653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98430913695279073342913741 36911592635729652503592653)
          ·
            refine ⟨13841847238398619688847245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36911592635729652503592653 13841847238398619688847245)
            ·
              refine ⟨5190692714399482383317717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13841847238398619688847245 5190692714399482383317717)
              ·
                refine ⟨121656860493737868359009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5190692714399482383317717 121656860493737868359009)
                ·
                  rfl

theorem cell23_6396999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 7].length) (baseStart_6396999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6396999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6396999 prefixEnd_6396999 := by exact prefixLift 6396999
  have htrace : WordTrace (prefixWord ++ tailWord_6396999) baseStart_6396999 baseEnd_6396999 := by
    simpa [prefixWord, tailWord_6396999, baseEnd_6396999] using wordTrace_append hprefix tailTrace_6396999
  have hstable : (prefixWord ++ tailWord_6396999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6396999).length < 2 ^ (prefixWord ++ tailWord_6396999).sum := by decide
  have hdescent : baseEnd_6396999 < baseStart_6396999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6396999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397009 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 1, 3, 3]
def baseStart_6397009 : Nat := 118140960795 + 6397009 * 2 ^ 59
def prefixEnd_6397009 : Nat := 4983230072969 + 3 ^ 40 * 6397009 * 2
def baseEnd_6397009 : Nat := 3284740368137467406568197

theorem tailTrace_6397009 : CollatzResearch.WordTrace tailWord_6397009 prefixEnd_6397009 3284740368137467406568197 := by
  unfold tailWord_6397009
  simp only [CollatzResearch.WordTrace]
  refine ⟨233318086081736390002178081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155545390721157593334785387 233318086081736390002178081)
  ·
    refine ⟨174988564561302292501633561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233318086081736390002178081 174988564561302292501633561)
    ·
      refine ⟨131241423420976719376225171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174988564561302292501633561 131241423420976719376225171)
      ·
        refine ⟨196862135131465079064337757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131241423420976719376225171 196862135131465079064337757)
        ·
          refine ⟨73823300674299404649126659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196862135131465079064337757 73823300674299404649126659)
          ·
            refine ⟨110734951011449106973689989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73823300674299404649126659 110734951011449106973689989)
            ·
              refine ⟨20762803314646707557566873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110734951011449106973689989 20762803314646707557566873)
              ·
                refine ⟨15572102485985030668175155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20762803314646707557566873 15572102485985030668175155)
                ·
                  refine ⟨23358153728977546002262733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15572102485985030668175155 23358153728977546002262733)
                  ·
                    refine ⟨8759307648366579750848525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23358153728977546002262733 8759307648366579750848525)
                    ·
                      refine ⟨3284740368137467406568197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8759307648366579750848525 3284740368137467406568197)
                      ·
                        rfl

theorem cell23_6397009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_6397009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397009 prefixEnd_6397009 := by exact prefixLift 6397009
  have htrace : WordTrace (prefixWord ++ tailWord_6397009) baseStart_6397009 baseEnd_6397009 := by
    simpa [prefixWord, tailWord_6397009, baseEnd_6397009] using wordTrace_append hprefix tailTrace_6397009
  have hstable : (prefixWord ++ tailWord_6397009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397009).length < 2 ^ (prefixWord ++ tailWord_6397009).sum := by decide
  have hdescent : baseEnd_6397009 < baseStart_6397009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397010 : List Nat := [3, 2, 2, 1, 3, 1, 1, 5, 1, 2, 2]
def baseStart_6397010 : Nat := 118140960795 + 6397010 * 2 ^ 59
def prefixEnd_6397010 : Nat := 4983230072969 + 3 ^ 40 * 6397010 * 2
def baseEnd_6397010 : Nat := 3284740881618121902655693

theorem tailTrace_6397010 : CollatzResearch.WordTrace tailWord_6397010 prefixEnd_6397010 3284740881618121902655693 := by
  unfold tailWord_6397010
  simp only [CollatzResearch.WordTrace]
  refine ⟨58329530638683191793241121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155545415036488511448642989 58329530638683191793241121)
  ·
    refine ⟨43747147979012393844930841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58329530638683191793241121 43747147979012393844930841)
    ·
      refine ⟨32810360984259295383698131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43747147979012393844930841 32810360984259295383698131)
      ·
        refine ⟨49215541476388943075547197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32810360984259295383698131 49215541476388943075547197)
        ·
          refine ⟨18455828053645853653330199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49215541476388943075547197 18455828053645853653330199)
          ·
            refine ⟨27683742080468780479995299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18455828053645853653330199 27683742080468780479995299)
            ·
              refine ⟨41525613120703170719992949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27683742080468780479995299 41525613120703170719992949)
              ·
                refine ⟨3893026230065922254999339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41525613120703170719992949 3893026230065922254999339)
                ·
                  refine ⟨5839539345098883382499009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3893026230065922254999339 5839539345098883382499009)
                  ·
                    refine ⟨4379654508824162536874257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5839539345098883382499009 4379654508824162536874257)
                    ·
                      refine ⟨3284740881618121902655693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4379654508824162536874257 3284740881618121902655693)
                      ·
                        rfl

theorem cell23_6397010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_6397010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397010 prefixEnd_6397010 := by exact prefixLift 6397010
  have htrace : WordTrace (prefixWord ++ tailWord_6397010) baseStart_6397010 baseEnd_6397010 := by
    simpa [prefixWord, tailWord_6397010, baseEnd_6397010] using wordTrace_append hprefix tailTrace_6397010
  have hstable : (prefixWord ++ tailWord_6397010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397010).length < 2 ^ (prefixWord ++ tailWord_6397010).sum := by decide
  have hdescent : baseEnd_6397010 < baseStart_6397010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397053 : List Nat := [1, 4, 1, 1, 3, 1, 4, 2, 1, 3, 2]
def baseStart_6397053 : Nat := 118140960795 + 6397053 * 2 ^ 59
def prefixEnd_6397053 : Nat := 4983230072969 + 3 ^ 40 * 6397053 * 2
def baseEnd_6397053 : Nat := 3284762961286265234417995

theorem tailTrace_6397053 : CollatzResearch.WordTrace tailWord_6397053 prefixEnd_6397053 3284762961286265234417995 := by
  unfold tailWord_6397053
  simp only [CollatzResearch.WordTrace]
  refine ⟨233319690893576985516779813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155546460595717990344519875 233319690893576985516779813)
  ·
    refine ⟨43747442042545684784396215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233319690893576985516779813 43747442042545684784396215)
    ·
      refine ⟨65621163063818527176594323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43747442042545684784396215 65621163063818527176594323)
      ·
        refine ⟨98431744595727790764891485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65621163063818527176594323 98431744595727790764891485)
        ·
          refine ⟨36911904223397921536834307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98431744595727790764891485 36911904223397921536834307)
          ·
            refine ⟨55367856335096882305251461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36911904223397921536834307 55367856335096882305251461)
            ·
              refine ⟨10381473062830665432234649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55367856335096882305251461 10381473062830665432234649)
              ·
                refine ⟨7786104797122999074175987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10381473062830665432234649 7786104797122999074175987)
                ·
                  refine ⟨11679157195684498611263981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7786104797122999074175987 11679157195684498611263981)
                  ·
                    refine ⟨4379683948381686979223993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11679157195684498611263981 4379683948381686979223993)
                    ·
                      refine ⟨3284762961286265234417995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4379683948381686979223993 3284762961286265234417995)
                      ·
                        rfl

theorem cell23_6397053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_6397053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397053 prefixEnd_6397053 := by exact prefixLift 6397053
  have htrace : WordTrace (prefixWord ++ tailWord_6397053) baseStart_6397053 baseEnd_6397053 := by
    simpa [prefixWord, tailWord_6397053, baseEnd_6397053] using wordTrace_append hprefix tailTrace_6397053
  have hstable : (prefixWord ++ tailWord_6397053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397053).length < 2 ^ (prefixWord ++ tailWord_6397053).sum := by decide
  have hdescent : baseEnd_6397053 < baseStart_6397053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397066 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 3, 4, 2]
def baseStart_6397066 : Nat := 118140960795 + 6397066 * 2 ^ 59
def prefixEnd_6397066 : Nat := 4983230072969 + 3 ^ 40 * 6397066 * 2
def baseEnd_6397066 : Nat := 3284769636534773683555435

theorem tailTrace_6397066 : CollatzResearch.WordTrace tailWord_6397066 prefixEnd_6397066 3284769636534773683555435 := by
  unfold tailWord_6397066
  simp only [CollatzResearch.WordTrace]
  refine ⟨58330041260632472184250763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155546776695019925824668701 58330041260632472184250763)
  ·
    refine ⟨87495061890948708276376145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58330041260632472184250763 87495061890948708276376145)
    ·
      refine ⟨65621296418211531207282109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87495061890948708276376145 65621296418211531207282109)
      ·
        refine ⟨24607986156829324202730791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65621296418211531207282109 24607986156829324202730791)
        ·
          refine ⟨36911979235243986304096187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24607986156829324202730791 36911979235243986304096187)
          ·
            refine ⟨55367968852865979456144281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36911979235243986304096187 55367968852865979456144281)
            ·
              refine ⟨41525976639649484592108211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55367968852865979456144281 41525976639649484592108211)
              ·
                refine ⟨62288964959474226888162317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41525976639649484592108211 62288964959474226888162317)
                ·
                  refine ⟨23358361859802835083060869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62288964959474226888162317 23358361859802835083060869)
                  ·
                    refine ⟨4379692848713031578073913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23358361859802835083060869 4379692848713031578073913)
                    ·
                      refine ⟨3284769636534773683555435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4379692848713031578073913 3284769636534773683555435)
                      ·
                        rfl

theorem cell23_6397066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_6397066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397066 prefixEnd_6397066 := by exact prefixLift 6397066
  have htrace : WordTrace (prefixWord ++ tailWord_6397066) baseStart_6397066 baseEnd_6397066 := by
    simpa [prefixWord, tailWord_6397066, baseEnd_6397066] using wordTrace_append hprefix tailTrace_6397066
  have hstable : (prefixWord ++ tailWord_6397066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397066).length < 2 ^ (prefixWord ++ tailWord_6397066).sum := by decide
  have hdescent : baseEnd_6397066 < baseStart_6397066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397119 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 2, 5]
def baseStart_6397119 : Nat := 118140960795 + 6397119 * 2 ^ 59
def prefixEnd_6397119 : Nat := 4983230072969 + 3 ^ 40 * 6397119 * 2
def baseEnd_6397119 : Nat := 1094932283669820658730897

theorem tailTrace_6397119 : CollatzResearch.WordTrace tailWord_6397119 prefixEnd_6397119 1094932283669820658730897 := by
  unfold tailWord_6397119
  simp only [CollatzResearch.WordTrace]
  refine ⟨233322098111337878788682411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155548065407558585859121607 233322098111337878788682411)
  ·
    refine ⟨349983147167006818183023617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233322098111337878788682411 349983147167006818183023617)
    ·
      refine ⟨262487360375255113637267713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349983147167006818183023617 262487360375255113637267713)
      ·
        refine ⟨196865520281441335227950785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262487360375255113637267713 196865520281441335227950785)
        ·
          refine ⟨147649140211081001420963089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196865520281441335227950785 147649140211081001420963089)
          ·
            refine ⟨110736855158310751065722317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147649140211081001420963089 110736855158310751065722317)
            ·
              refine ⟨41526320684366531649645869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110736855158310751065722317 41526320684366531649645869)
              ·
                refine ⟨15572370256637449368617201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41526320684366531649645869 15572370256637449368617201)
                ·
                  refine ⟨11679277692478087026462901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15572370256637449368617201 11679277692478087026462901)
                  ·
                    refine ⟨1094932283669820658730897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11679277692478087026462901 1094932283669820658730897)
                    ·
                      rfl

theorem cell23_6397119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 5].length) (baseStart_6397119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397119 prefixEnd_6397119 := by exact prefixLift 6397119
  have htrace : WordTrace (prefixWord ++ tailWord_6397119) baseStart_6397119 baseEnd_6397119 := by
    simpa [prefixWord, tailWord_6397119, baseEnd_6397119] using wordTrace_append hprefix tailTrace_6397119
  have hstable : (prefixWord ++ tailWord_6397119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397119).length < 2 ^ (prefixWord ++ tailWord_6397119).sum := by decide
  have hdescent : baseEnd_6397119 < baseStart_6397119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397140 : List Nat := [2, 4, 1, 4, 1, 1, 1, 4, 5]
def baseStart_6397140 : Nat := 118140960795 + 6397140 * 2 ^ 59
def prefixEnd_6397140 : Nat := 4983230072969 + 3 ^ 40 * 6397140 * 2
def baseEnd_6397140 : Nat := 364978626011467377114455

theorem tailTrace_6397140 : CollatzResearch.WordTrace tailWord_6397140 prefixEnd_6397140 364978626011467377114455 := by
  unfold tailWord_6397140
  simp only [CollatzResearch.WordTrace]
  refine ⟨116661432022130899687598437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155548576029507866250131249 116661432022130899687598437)
  ·
    refine ⟨21874018504149543691424707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116661432022130899687598437 21874018504149543691424707)
    ·
      refine ⟨32811027756224315537137061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21874018504149543691424707 32811027756224315537137061)
      ·
        refine ⟨6152067704292059163213199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32811027756224315537137061 6152067704292059163213199)
        ·
          refine ⟨9228101556438088744819799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6152067704292059163213199 9228101556438088744819799)
          ·
            refine ⟨13842152334657133117229699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9228101556438088744819799 13842152334657133117229699)
            ·
              refine ⟨20763228501985699675844549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13842152334657133117229699 20763228501985699675844549)
              ·
                refine ⟨3893105344122318689220853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20763228501985699675844549 3893105344122318689220853)
                ·
                  refine ⟨364978626011467377114455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3893105344122318689220853 364978626011467377114455)
                  ·
                    rfl

theorem cell23_6397140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_6397140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397140 prefixEnd_6397140 := by exact prefixLift 6397140
  have htrace : WordTrace (prefixWord ++ tailWord_6397140) baseStart_6397140 baseEnd_6397140 := by
    simpa [prefixWord, tailWord_6397140, baseEnd_6397140] using wordTrace_append hprefix tailTrace_6397140
  have hstable : (prefixWord ++ tailWord_6397140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397140).length < 2 ^ (prefixWord ++ tailWord_6397140).sum := by decide
  have hdescent : baseEnd_6397140 < baseStart_6397140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397156 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 1, 6, 2]
def baseStart_6397156 : Nat := 118140960795 + 6397156 * 2 ^ 59
def prefixEnd_6397156 : Nat := 4983230072969 + 3 ^ 40 * 6397156 * 2
def baseEnd_6397156 : Nat := 3284815849793678331430021

theorem tailTrace_6397156 : CollatzResearch.WordTrace tailWord_6397156 prefixEnd_6397156 3284815849793678331430021 := by
  unfold tailWord_6397156
  simp only [CollatzResearch.WordTrace]
  refine ⟨116661723806101917053889661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155548965074802556071852881 116661723806101917053889661)
  ·
    refine ⟨43748146427288218895208623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116661723806101917053889661 43748146427288218895208623)
    ·
      refine ⟨65622219640932328342812935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43748146427288218895208623 65622219640932328342812935)
      ·
        refine ⟨98433329461398492514219403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65622219640932328342812935 98433329461398492514219403)
        ·
          refine ⟨147649994192097738771329105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98433329461398492514219403 147649994192097738771329105)
          ·
            refine ⟨110737495644073304078496829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147649994192097738771329105 110737495644073304078496829)
            ·
              refine ⟨41526560866527489029436311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110737495644073304078496829 41526560866527489029436311)
              ·
                refine ⟨62289841299791233544154467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41526560866527489029436311 62289841299791233544154467)
                ·
                  refine ⟨93434761949686850316231701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62289841299791233544154467 93434761949686850316231701)
                  ·
                    refine ⟨4379754466391571108573361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93434761949686850316231701 4379754466391571108573361)
                    ·
                      refine ⟨3284815849793678331430021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4379754466391571108573361 3284815849793678331430021)
                      ·
                        rfl

theorem cell23_6397156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_6397156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397156 prefixEnd_6397156 := by exact prefixLift 6397156
  have htrace : WordTrace (prefixWord ++ tailWord_6397156) baseStart_6397156 baseEnd_6397156 := by
    simpa [prefixWord, tailWord_6397156, baseEnd_6397156] using wordTrace_append hprefix tailTrace_6397156
  have hstable : (prefixWord ++ tailWord_6397156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397156).length < 2 ^ (prefixWord ++ tailWord_6397156).sum := by decide
  have hdescent : baseEnd_6397156 < baseStart_6397156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397166 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 5, 4]
def baseStart_6397166 : Nat := 118140960795 + 6397166 * 2 ^ 59
def prefixEnd_6397166 : Nat := 4983230072969 + 3 ^ 40 * 6397166 * 2
def baseEnd_6397166 : Nat := 1094940328200074430768325

theorem tailTrace_6397166 : CollatzResearch.WordTrace tailWord_6397166 prefixEnd_6397166 1094940328200074430768325 := by
  unfold tailWord_6397166
  simp only [CollatzResearch.WordTrace]
  refine ⟨29165476542770950726955419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155549208228111737210428901 29165476542770950726955419)
  ·
    refine ⟨43748214814156426090433129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29165476542770950726955419 43748214814156426090433129)
    ·
      refine ⟨32811161110617319567824847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43748214814156426090433129 32811161110617319567824847)
      ·
        refine ⟨49216741665925979351737271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32811161110617319567824847 49216741665925979351737271)
        ·
          refine ⟨73825112498888969027605907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49216741665925979351737271 73825112498888969027605907)
          ·
            refine ⟨110737668748333453541408861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73825112498888969027605907 110737668748333453541408861)
            ·
              refine ⟨41526625780625045078028323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110737668748333453541408861 41526625780625045078028323)
              ·
                refine ⟨62289938670937567617042485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41526625780625045078028323 62289938670937567617042485)
                ·
                  refine ⟨5839681750400396964097733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62289938670937567617042485 5839681750400396964097733)
                  ·
                    refine ⟨1094940328200074430768325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5839681750400396964097733 1094940328200074430768325)
                    ·
                      rfl

theorem cell23_6397166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_6397166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397166 prefixEnd_6397166 := by exact prefixLift 6397166
  have htrace : WordTrace (prefixWord ++ tailWord_6397166) baseStart_6397166 baseEnd_6397166 := by
    simpa [prefixWord, tailWord_6397166, baseEnd_6397166] using wordTrace_append hprefix tailTrace_6397166
  have hstable : (prefixWord ++ tailWord_6397166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397166).length < 2 ^ (prefixWord ++ tailWord_6397166).sum := by decide
  have hdescent : baseEnd_6397166 < baseStart_6397166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397170 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 2, 5]
def baseStart_6397170 : Nat := 118140960795 + 6397170 * 2 ^ 59
def prefixEnd_6397170 : Nat := 4983230072969 + 3 ^ 40 * 6397170 * 2
def baseEnd_6397170 : Nat := 1094941012840947092218319

theorem tailTrace_6397170 : CollatzResearch.WordTrace tailWord_6397170 prefixEnd_6397170 1094941012840947092218319 := by
  unfold tailWord_6397170
  simp only [CollatzResearch.WordTrace]
  refine ⟨58330989558538278624697241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155549305489435409665859309 58330989558538278624697241)
  ·
    refine ⟨43748242168903708968522931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58330989558538278624697241 43748242168903708968522931)
    ·
      refine ⟨65622363253355563452784397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43748242168903708968522931 65622363253355563452784397)
      ·
        refine ⟨24608386220008336294794149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65622363253355563452784397 24608386220008336294794149)
        ·
          refine ⟨4614072416251563055273903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24608386220008336294794149 4614072416251563055273903)
          ·
            refine ⟨6921108624377344582910855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4614072416251563055273903 6921108624377344582910855)
            ·
              refine ⟨10381662936566016874366283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6921108624377344582910855 10381662936566016874366283)
              ·
                refine ⟨15572494404849025311549425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10381662936566016874366283 15572494404849025311549425)
                ·
                  refine ⟨11679370803636768983662069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15572494404849025311549425 11679370803636768983662069)
                  ·
                    refine ⟨1094941012840947092218319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11679370803636768983662069 1094941012840947092218319)
                    ·
                      rfl

theorem cell23_6397170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_6397170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397170 prefixEnd_6397170 := by exact prefixLift 6397170
  have htrace : WordTrace (prefixWord ++ tailWord_6397170) baseStart_6397170 baseEnd_6397170 := by
    simpa [prefixWord, tailWord_6397170, baseEnd_6397170] using wordTrace_append hprefix tailTrace_6397170
  have hstable : (prefixWord ++ tailWord_6397170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397170).length < 2 ^ (prefixWord ++ tailWord_6397170).sum := by decide
  have hdescent : baseEnd_6397170 < baseStart_6397170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397183 : List Nat := [1, 1, 2, 2, 1, 5, 1, 5, 1, 4]
def baseStart_6397183 : Nat := 118140960795 + 6397183 * 2 ^ 59
def prefixEnd_6397183 : Nat := 4983230072969 + 3 ^ 40 * 6397183 * 2
def baseEnd_6397183 : Nat := 1094943237923783241930799

theorem tailTrace_6397183 : CollatzResearch.WordTrace tailWord_6397183 prefixEnd_6397183 1094943237923783241930799 := by
  unfold tailWord_6397183
  simp only [CollatzResearch.WordTrace]
  refine ⟨233324432383106017719012203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155549621588737345146008135 233324432383106017719012203)
  ·
    refine ⟨349986648574659026578518305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233324432383106017719012203 349986648574659026578518305)
    ·
      refine ⟨262489986430994269933888729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349986648574659026578518305 262489986430994269933888729)
      ·
        refine ⟨196867489823245702450416547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262489986430994269933888729 196867489823245702450416547)
        ·
          refine ⟨295301234734868553675624821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196867489823245702450416547 295301234734868553675624821)
          ·
            refine ⟨27684490756393926907089827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 295301234734868553675624821 27684490756393926907089827)
            ·
              refine ⟨41526736134590890360634741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27684490756393926907089827 41526736134590890360634741)
              ·
                refine ⟨3893131512617895971309507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41526736134590890360634741 3893131512617895971309507)
                ·
                  refine ⟨5839697268926843956964261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3893131512617895971309507 5839697268926843956964261)
                  ·
                    refine ⟨1094943237923783241930799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5839697268926843956964261 1094943237923783241930799)
                    ·
                      rfl

theorem cell23_6397183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 1, 4].length) (baseStart_6397183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397183 prefixEnd_6397183 := by exact prefixLift 6397183
  have htrace : WordTrace (prefixWord ++ tailWord_6397183) baseStart_6397183 baseEnd_6397183 := by
    simpa [prefixWord, tailWord_6397183, baseEnd_6397183] using wordTrace_append hprefix tailTrace_6397183
  have hstable : (prefixWord ++ tailWord_6397183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397183).length < 2 ^ (prefixWord ++ tailWord_6397183).sum := by decide
  have hdescent : baseEnd_6397183 < baseStart_6397183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397196 : List Nat := [2, 2, 1, 2, 2, 3, 3, 2, 6]
def baseStart_6397196 : Nat := 118140960795 + 6397196 * 2 ^ 59
def prefixEnd_6397196 : Nat := 4983230072969 + 3 ^ 40 * 6397196 * 2
def baseEnd_6397196 : Nat := 364981821002206463881093

theorem tailTrace_6397196 : CollatzResearch.WordTrace tailWord_6397196 prefixEnd_6397196 364981821002206463881093 := by
  unfold tailWord_6397196
  simp only [CollatzResearch.WordTrace]
  refine ⟨116662453266029460469617721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155549937688039280626156961 116662453266029460469617721)
  ·
    refine ⟨87496839949522095352213291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116662453266029460469617721 87496839949522095352213291)
    ·
      refine ⟨131245259924283143028319937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87496839949522095352213291 131245259924283143028319937)
      ·
        refine ⟨98433944943212357271239953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131245259924283143028319937 98433944943212357271239953)
        ·
          refine ⟨73825458707409267953429965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98433944943212357271239953 73825458707409267953429965)
          ·
            refine ⟨27684547015278475482536237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73825458707409267953429965 27684547015278475482536237)
            ·
              refine ⟨10381705130729428305951089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27684547015278475482536237 10381705130729428305951089)
              ·
                refine ⟨7786278848047071229463317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10381705130729428305951089 7786278848047071229463317)
                ·
                  refine ⟨364981821002206463881093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7786278848047071229463317 364981821002206463881093)
                  ·
                    rfl

theorem cell23_6397196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 6].length) (baseStart_6397196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397196 prefixEnd_6397196 := by exact prefixLift 6397196
  have htrace : WordTrace (prefixWord ++ tailWord_6397196) baseStart_6397196 baseEnd_6397196 := by
    simpa [prefixWord, tailWord_6397196, baseEnd_6397196] using wordTrace_append hprefix tailTrace_6397196
  have hstable : (prefixWord ++ tailWord_6397196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397196).length < 2 ^ (prefixWord ++ tailWord_6397196).sum := by decide
  have hdescent : baseEnd_6397196 < baseStart_6397196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397233 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 1, 5, 2]
def baseStart_6397233 : Nat := 118140960795 + 6397233 * 2 ^ 59
def prefixEnd_6397233 : Nat := 4983230072969 + 3 ^ 40 * 6397233 * 2
def baseEnd_6397233 : Nat := 3284855387804074530167167

theorem tailTrace_6397233 : CollatzResearch.WordTrace tailWord_6397233 prefixEnd_6397233 3284855387804074530167167 := by
  unfold tailWord_6397233
  simp only [CollatzResearch.WordTrace]
  refine ⟨233326256032924876258332353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155550837355283250838888235 233326256032924876258332353)
  ·
    refine ⟨174994692024693657193749265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233326256032924876258332353 174994692024693657193749265)
    ·
      refine ⟨131246019018520242895311949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174994692024693657193749265 131246019018520242895311949)
      ·
        refine ⟨49217257131945091085741981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131246019018520242895311949 49217257131945091085741981)
        ·
          refine ⟨18456471424479409157153243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49217257131945091085741981 18456471424479409157153243)
          ·
            refine ⟨27684707136719113735729865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18456471424479409157153243 27684707136719113735729865)
            ·
              refine ⟨20763530352539335301797399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27684707136719113735729865 20763530352539335301797399)
              ·
                refine ⟨31145295528809002952696099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20763530352539335301797399 31145295528809002952696099)
                ·
                  refine ⟨46717943293213504429044149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31145295528809002952696099 46717943293213504429044149)
                  ·
                    refine ⟨4379807183738766040222889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46717943293213504429044149 4379807183738766040222889)
                    ·
                      refine ⟨3284855387804074530167167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4379807183738766040222889 3284855387804074530167167)
                      ·
                        rfl

theorem cell23_6397233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_6397233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397233 prefixEnd_6397233 := by exact prefixLift 6397233
  have htrace : WordTrace (prefixWord ++ tailWord_6397233) baseStart_6397233 baseEnd_6397233 := by
    simpa [prefixWord, tailWord_6397233, baseEnd_6397233] using wordTrace_append hprefix tailTrace_6397233
  have hstable : (prefixWord ++ tailWord_6397233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397233).length < 2 ^ (prefixWord ++ tailWord_6397233).sum := by decide
  have hdescent : baseEnd_6397233 < baseStart_6397233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397266 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_6397266 : Nat := 118140960795 + 6397266 * 2 ^ 59
def prefixEnd_6397266 : Nat := 4983230072969 + 3 ^ 40 * 6397266 * 2
def baseEnd_6397266 : Nat := 3284872332665672901054515

theorem tailTrace_6397266 : CollatzResearch.WordTrace tailWord_6397266 prefixEnd_6397266 3284872332665672901054515 := by
  unfold tailWord_6397266
  simp only [CollatzResearch.WordTrace]
  refine ⟨58331864910451330723570913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155551639761203548596189101 58331864910451330723570913)
  ·
    refine ⟨43748898682838498042678185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58331864910451330723570913 43748898682838498042678185)
    ·
      refine ⟨32811674012128873532008639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43748898682838498042678185 32811674012128873532008639)
      ·
        refine ⟨49217511018193310298012959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32811674012128873532008639 49217511018193310298012959)
        ·
          refine ⟨73826266527289965447019439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49217511018193310298012959 73826266527289965447019439)
          ·
            refine ⟨110739399790934948170529159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73826266527289965447019439 110739399790934948170529159)
            ·
              refine ⟨166109099686402422255793739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110739399790934948170529159 166109099686402422255793739)
              ·
                refine ⟨249163649529603633383690609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166109099686402422255793739 249163649529603633383690609)
                ·
                  refine ⟨186872737147202725037767957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249163649529603633383690609 186872737147202725037767957)
                  ·
                    refine ⟨8759659553775127736145373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 186872737147202725037767957 8759659553775127736145373)
                    ·
                      refine ⟨3284872332665672901054515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8759659553775127736145373 3284872332665672901054515)
                      ·
                        rfl

theorem cell23_6397266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_6397266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397266 prefixEnd_6397266 := by exact prefixLift 6397266
  have htrace : WordTrace (prefixWord ++ tailWord_6397266) baseStart_6397266 baseEnd_6397266 := by
    simpa [prefixWord, tailWord_6397266, baseEnd_6397266] using wordTrace_append hprefix tailTrace_6397266
  have hstable : (prefixWord ++ tailWord_6397266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397266).length < 2 ^ (prefixWord ++ tailWord_6397266).sum := by decide
  have hdescent : baseEnd_6397266 < baseStart_6397266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397277 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 3, 5]
def baseStart_6397277 : Nat := 118140960795 + 6397277 * 2 ^ 59
def prefixEnd_6397277 : Nat := 4983230072969 + 3 ^ 40 * 6397277 * 2
def baseEnd_6397277 : Nat := 1094959326984290786005655

theorem tailTrace_6397277 : CollatzResearch.WordTrace tailWord_6397277 prefixEnd_6397277 1094959326984290786005655 := by
  unfold tailWord_6397277
  simp only [CollatzResearch.WordTrace]
  refine ⟨233327860844765471772934085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155551907229843647848622723 233327860844765471772934085)
  ·
    refine ⟨43748973908393525957425141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233327860844765471772934085 43748973908393525957425141)
    ·
      refine ⟨4101466303911893058508607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43748973908393525957425141 4101466303911893058508607)
      ·
        refine ⟨6152199455867839587762911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4101466303911893058508607 6152199455867839587762911)
        ·
          refine ⟨9228299183801759381644367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6152199455867839587762911 9228299183801759381644367)
          ·
            refine ⟨13842448775702639072466551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9228299183801759381644367 13842448775702639072466551)
            ·
              refine ⟨20763673163553958608699827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13842448775702639072466551 20763673163553958608699827)
              ·
                refine ⟨31145509745330937913049741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20763673163553958608699827 31145509745330937913049741)
                ·
                  refine ⟨11679566154499101717393653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31145509745330937913049741 11679566154499101717393653)
                  ·
                    refine ⟨1094959326984290786005655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11679566154499101717393653 1094959326984290786005655)
                    ·
                      rfl

theorem cell23_6397277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_6397277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397277 prefixEnd_6397277 := by exact prefixLift 6397277
  have htrace : WordTrace (prefixWord ++ tailWord_6397277) baseStart_6397277 baseEnd_6397277 := by
    simpa [prefixWord, tailWord_6397277, baseEnd_6397277] using wordTrace_append hprefix tailTrace_6397277
  have hstable : (prefixWord ++ tailWord_6397277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397277).length < 2 ^ (prefixWord ++ tailWord_6397277).sum := by decide
  have hdescent : baseEnd_6397277 < baseStart_6397277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397280 : List Nat := [2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 4]
def baseStart_6397280 : Nat := 118140960795 + 6397280 * 2 ^ 59
def prefixEnd_6397280 : Nat := 4983230072969 + 3 ^ 40 * 6397280 * 2
def baseEnd_6397280 : Nat := 3284879521394835846279451

theorem tailTrace_6397280 : CollatzResearch.WordTrace tailWord_6397280 prefixEnd_6397280 3284879521394835846279451 := by
  unfold tailWord_6397280
  simp only [CollatzResearch.WordTrace]
  refine ⟨116663985131877301642646647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155551980175836402190195529 116663985131877301642646647)
  ·
    refine ⟨174995977697815952463969971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116663985131877301642646647 174995977697815952463969971)
    ·
      refine ⟨262493966546723928695954957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174995977697815952463969971 262493966546723928695954957)
      ·
        refine ⟨98435237455021473260983109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262493966546723928695954957 98435237455021473260983109)
        ·
          refine ⟨18456607022816526236434333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98435237455021473260983109 18456607022816526236434333)
          ·
            refine ⟨6921227633556197338662875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18456607022816526236434333 6921227633556197338662875)
            ·
              refine ⟨10381841450334296007994313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6921227633556197338662875 10381841450334296007994313)
              ·
                refine ⟨7786381087750722005995735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10381841450334296007994313 7786381087750722005995735)
                ·
                  refine ⟨11679571631626083008993603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7786381087750722005995735 11679571631626083008993603)
                  ·
                    refine ⟨17519357447439124513490405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11679571631626083008993603 17519357447439124513490405)
                    ·
                      refine ⟨3284879521394835846279451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17519357447439124513490405 3284879521394835846279451)
                      ·
                        rfl

theorem cell23_6397280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_6397280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397280 prefixEnd_6397280 := by exact prefixLift 6397280
  have htrace : WordTrace (prefixWord ++ tailWord_6397280) baseStart_6397280 baseEnd_6397280 := by
    simpa [prefixWord, tailWord_6397280, baseEnd_6397280] using wordTrace_append hprefix tailTrace_6397280
  have hstable : (prefixWord ++ tailWord_6397280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397280).length < 2 ^ (prefixWord ++ tailWord_6397280).sum := by decide
  have hdescent : baseEnd_6397280 < baseStart_6397280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397283 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 3]
def baseStart_6397283 : Nat := 118140960795 + 6397283 * 2 ^ 59
def prefixEnd_6397283 : Nat := 4983230072969 + 3 ^ 40 * 6397283 * 2
def baseEnd_6397283 : Nat := 3284881061836799334541937

theorem tailTrace_6397283 : CollatzResearch.WordTrace tailWord_6397283 prefixEnd_6397283 3284881061836799334541937 := by
  unfold tailWord_6397283
  simp only [CollatzResearch.WordTrace]
  refine ⟨233328079682743734797652503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155552053121829156531768335 233328079682743734797652503)
  ·
    refine ⟨349992119524115602196478755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233328079682743734797652503 349992119524115602196478755)
    ·
      refine ⟨524988179286173403294718133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349992119524115602196478755 524988179286173403294718133)
      ·
        refine ⟨49217641808078756558879825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 524988179286173403294718133 49217641808078756558879825)
        ·
          refine ⟨36913231356059067419159869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49217641808078756558879825 36913231356059067419159869)
          ·
            refine ⟨13842461758522150282184951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36913231356059067419159869 13842461758522150282184951)
            ·
              refine ⟨20763692637783225423277427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13842461758522150282184951 20763692637783225423277427)
              ·
                refine ⟨31145538956674838134916141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20763692637783225423277427 31145538956674838134916141)
                ·
                  refine ⟨11679577108753064300593553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31145538956674838134916141 11679577108753064300593553)
                  ·
                    refine ⟨8759682831564798225445165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11679577108753064300593553 8759682831564798225445165)
                    ·
                      refine ⟨3284881061836799334541937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8759682831564798225445165 3284881061836799334541937)
                      ·
                        rfl

theorem cell23_6397283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_6397283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397283 prefixEnd_6397283 := by exact prefixLift 6397283
  have htrace : WordTrace (prefixWord ++ tailWord_6397283) baseStart_6397283 baseEnd_6397283 := by
    simpa [prefixWord, tailWord_6397283, baseEnd_6397283] using wordTrace_append hprefix tailTrace_6397283
  have hstable : (prefixWord ++ tailWord_6397283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397283).length < 2 ^ (prefixWord ++ tailWord_6397283).sum := by decide
  have hdescent : baseEnd_6397283 < baseStart_6397283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397293 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_6397293 : Nat := 118140960795 + 6397293 * 2 ^ 59
def prefixEnd_6397293 : Nat := 4983230072969 + 3 ^ 40 * 6397293 * 2
def baseEnd_6397293 : Nat := 3284886196643344295416891

theorem tailTrace_6397293 : CollatzResearch.WordTrace tailWord_6397293 prefixEnd_6397293 3284886196643344295416891 := by
  unfold tailWord_6397293
  simp only [CollatzResearch.WordTrace]
  refine ⟨233328444412707506505516533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155552296275138337670344355 233328444412707506505516533)
  ·
    refine ⟨21874541663691328734892175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 233328444412707506505516533 21874541663691328734892175)
    ·
      refine ⟨32811812495536993102338263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21874541663691328734892175 32811812495536993102338263)
      ·
        refine ⟨49217718743305489653507395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32811812495536993102338263 49217718743305489653507395)
        ·
          refine ⟨73826578114958234480261093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49217718743305489653507395 73826578114958234480261093)
          ·
            refine ⟨13842483396554668965048955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73826578114958234480261093 13842483396554668965048955)
            ·
              refine ⟨20763725094832003447573433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13842483396554668965048955 20763725094832003447573433)
              ·
                refine ⟨15572793821124002585680075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20763725094832003447573433 15572793821124002585680075)
                ·
                  refine ⟨23359190731686003878520113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15572793821124002585680075 23359190731686003878520113)
                  ·
                    refine ⟨17519393048764502908890085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23359190731686003878520113 17519393048764502908890085)
                    ·
                      refine ⟨3284886196643344295416891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17519393048764502908890085 3284886196643344295416891)
                      ·
                        rfl

theorem cell23_6397293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_6397293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397293 prefixEnd_6397293 := by exact prefixLift 6397293
  have htrace : WordTrace (prefixWord ++ tailWord_6397293) baseStart_6397293 baseEnd_6397293 := by
    simpa [prefixWord, tailWord_6397293, baseEnd_6397293] using wordTrace_append hprefix tailTrace_6397293
  have hstable : (prefixWord ++ tailWord_6397293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397293).length < 2 ^ (prefixWord ++ tailWord_6397293).sum := by decide
  have hdescent : baseEnd_6397293 < baseStart_6397293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397299 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 3, 9]
def baseStart_6397299 : Nat := 118140960795 + 6397299 * 2 ^ 59
def prefixEnd_6397299 : Nat := 4983230072969 + 3 ^ 40 * 6397299 * 2
def baseEnd_6397299 : Nat := 1094963092509090423980621

theorem tailTrace_6397299 : CollatzResearch.WordTrace tailWord_6397299 prefixEnd_6397299 1094963092509090423980621 := by
  unfold tailWord_6397299
  simp only [CollatzResearch.WordTrace]
  refine ⟨233328663250685769530234951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155552442167123846353489967 233328663250685769530234951)
  ·
    refine ⟨349992994876028654295352427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233328663250685769530234951 349992994876028654295352427)
    ·
      refine ⟨524989492314042981443028641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349992994876028654295352427 524989492314042981443028641)
      ·
        refine ⟨393742119235532236082271481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524989492314042981443028641 393742119235532236082271481)
        ·
          refine ⟨295306589426649177061703611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393742119235532236082271481 295306589426649177061703611)
          ·
            refine ⟨442959884139973765592555417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295306589426649177061703611 442959884139973765592555417)
            ·
              refine ⟨332219913104980324194416563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442959884139973765592555417 332219913104980324194416563)
              ·
                refine ⟨498329869657470486291624845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332219913104980324194416563 498329869657470486291624845)
                ·
                  refine ⟨186873701121551432359359317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 498329869657470486291624845 186873701121551432359359317)
                  ·
                    refine ⟨1094963092509090423980621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 186873701121551432359359317 1094963092509090423980621)
                    ·
                      rfl

theorem cell23_6397299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 9].length) (baseStart_6397299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397299 prefixEnd_6397299 := by exact prefixLift 6397299
  have htrace : WordTrace (prefixWord ++ tailWord_6397299) baseStart_6397299 baseEnd_6397299 := by
    simpa [prefixWord, tailWord_6397299, baseEnd_6397299] using wordTrace_append hprefix tailTrace_6397299
  have hstable : (prefixWord ++ tailWord_6397299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397299).length < 2 ^ (prefixWord ++ tailWord_6397299).sum := by decide
  have hdescent : baseEnd_6397299 < baseStart_6397299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397316 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 2, 7]
def baseStart_6397316 : Nat := 118140960795 + 6397316 * 2 ^ 59
def prefixEnd_6397316 : Nat := 4983230072969 + 3 ^ 40 * 6397316 * 2
def baseEnd_6397316 : Nat := 1094966002232799235143095

theorem tailTrace_6397316 : CollatzResearch.WordTrace tailWord_6397316 prefixEnd_6397316 1094966002232799235143095 := by
  unfold tailWord_6397316
  simp only [CollatzResearch.WordTrace]
  refine ⟨116664641645812090716801901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155552855527749454289069201 116664641645812090716801901)
  ·
    refine ⟨43749240617179534018800713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116664641645812090716801901 43749240617179534018800713)
    ·
      refine ⟨32811930462884650514100535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43749240617179534018800713 32811930462884650514100535)
      ·
        refine ⟨49217895694326975771150803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32811930462884650514100535 49217895694326975771150803)
        ·
          refine ⟨73826843541490463656726205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49217895694326975771150803 73826843541490463656726205)
          ·
            refine ⟨27685066328058923871272327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73826843541490463656726205 27685066328058923871272327)
            ·
              refine ⟨41527599492088385806908491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27685066328058923871272327 41527599492088385806908491)
              ·
                refine ⟨62291399238132578710362737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41527599492088385806908491 62291399238132578710362737)
                ·
                  refine ⟨46718549428599434032772053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62291399238132578710362737 46718549428599434032772053)
                  ·
                    refine ⟨1094966002232799235143095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46718549428599434032772053 1094966002232799235143095)
                    ·
                      rfl

theorem cell23_6397316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_6397316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397316 prefixEnd_6397316 := by exact prefixLift 6397316
  have htrace : WordTrace (prefixWord ++ tailWord_6397316) baseStart_6397316 baseEnd_6397316 := by
    simpa [prefixWord, tailWord_6397316, baseEnd_6397316] using wordTrace_append hprefix tailTrace_6397316
  have hstable : (prefixWord ++ tailWord_6397316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397316).length < 2 ^ (prefixWord ++ tailWord_6397316).sum := by decide
  have hdescent : baseEnd_6397316 < baseStart_6397316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397323 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 5, 3, 2]
def baseStart_6397323 : Nat := 118140960795 + 6397323 * 2 ^ 59
def prefixEnd_6397323 : Nat := 4983230072969 + 3 ^ 40 * 6397323 * 2
def baseEnd_6397323 : Nat := 3284901601062979178041753

theorem tailTrace_6397323 : CollatzResearch.WordTrace tailWord_6397323 prefixEnd_6397323 3284901601062979178041753 := by
  unfold tailWord_6397323
  simp only [CollatzResearch.WordTrace]
  refine ⟨233329538602598821629108623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155553025735065881086072415 233329538602598821629108623)
  ·
    refine ⟨349994307903898232443662935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233329538602598821629108623 349994307903898232443662935)
    ·
      refine ⟨524991461855847348665494403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349994307903898232443662935 524991461855847348665494403)
      ·
        refine ⟨787487192783771022998241605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524991461855847348665494403 787487192783771022998241605)
        ·
          refine ⟨147653848646957066812170301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 787487192783771022998241605 147653848646957066812170301)
          ·
            refine ⟨55370193242608900054563863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147653848646957066812170301 55370193242608900054563863)
            ·
              refine ⟨83055289863913350081845795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55370193242608900054563863 83055289863913350081845795)
              ·
                refine ⟨124582934795870025122768693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83055289863913350081845795 124582934795870025122768693)
                ·
                  refine ⟨11679650137112814855259565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 124582934795870025122768693 11679650137112814855259565)
                  ·
                    refine ⟨4379868801417305570722337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11679650137112814855259565 4379868801417305570722337)
                    ·
                      refine ⟨3284901601062979178041753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4379868801417305570722337 3284901601062979178041753)
                      ·
                        rfl

theorem cell23_6397323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 3, 2].length) (baseStart_6397323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397323 prefixEnd_6397323 := by exact prefixLift 6397323
  have htrace : WordTrace (prefixWord ++ tailWord_6397323) baseStart_6397323 baseEnd_6397323 := by
    simpa [prefixWord, tailWord_6397323, baseEnd_6397323] using wordTrace_append hprefix tailTrace_6397323
  have hstable : (prefixWord ++ tailWord_6397323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397323).length < 2 ^ (prefixWord ++ tailWord_6397323).sum := by decide
  have hdescent : baseEnd_6397323 < baseStart_6397323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397356 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 5]
def baseStart_6397356 : Nat := 118140960795 + 6397356 * 2 ^ 59
def prefixEnd_6397356 : Nat := 4983230072969 + 3 ^ 40 * 6397356 * 2
def baseEnd_6397356 : Nat := 3284918545924577548929101

theorem tailTrace_6397356 : CollatzResearch.WordTrace tailWord_6397356 prefixEnd_6397356 3284918545924577548929101 := by
  unfold tailWord_6397356
  simp only [CollatzResearch.WordTrace]
  refine ⟨116665371105739634132529961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155553828140986178843373281 116665371105739634132529961)
  ·
    refine ⟨87499028329304725599397471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116665371105739634132529961 87499028329304725599397471)
    ·
      refine ⟨131248542493957088399096207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87499028329304725599397471 131248542493957088399096207)
      ·
        refine ⟨196872813740935632598644311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131248542493957088399096207 196872813740935632598644311)
        ·
          refine ⟨295309220611403448897966467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196872813740935632598644311 295309220611403448897966467)
          ·
            refine ⟨442963830917105173346949701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295309220611403448897966467 442963830917105173346949701)
            ·
              refine ⟨83055718296957220002553069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 442963830917105173346949701 83055718296957220002553069)
              ·
                refine ⟨31145894361358957500957401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83055718296957220002553069 31145894361358957500957401)
                ·
                  refine ⟨23359420771019218125718051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31145894361358957500957401 23359420771019218125718051)
                  ·
                    refine ⟨35039131156528827188577077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23359420771019218125718051 35039131156528827188577077)
                    ·
                      refine ⟨3284918545924577548929101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35039131156528827188577077 3284918545924577548929101)
                      ·
                        rfl

theorem cell23_6397356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_6397356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397356 prefixEnd_6397356 := by exact prefixLift 6397356
  have htrace : WordTrace (prefixWord ++ tailWord_6397356) baseStart_6397356 baseEnd_6397356 := by
    simpa [prefixWord, tailWord_6397356, baseEnd_6397356] using wordTrace_append hprefix tailTrace_6397356
  have hstable : (prefixWord ++ tailWord_6397356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397356).length < 2 ^ (prefixWord ++ tailWord_6397356).sum := by decide
  have hdescent : baseEnd_6397356 < baseStart_6397356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397376 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 7]
def baseStart_6397376 : Nat := 118140960795 + 6397376 * 2 ^ 59
def prefixEnd_6397376 : Nat := 4983230072969 + 3 ^ 40 * 6397376 * 2
def baseEnd_6397376 : Nat := 364992090615296385631001

theorem tailTrace_6397376 : CollatzResearch.WordTrace tailWord_6397376 prefixEnd_6397376 364992090615296385631001 := by
  unfold tailWord_6397376
  simp only [CollatzResearch.WordTrace]
  refine ⟨116665735835703405840393991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155554314447604541120525321 116665735835703405840393991)
  ·
    refine ⟨174998603753555108760590987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116665735835703405840393991 174998603753555108760590987)
    ·
      refine ⟨262497905630332663140886481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174998603753555108760590987 262497905630332663140886481)
      ·
        refine ⟨196873429222749497355664861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262497905630332663140886481 196873429222749497355664861)
        ·
          refine ⟨73827535958531061508374323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196873429222749497355664861 73827535958531061508374323)
          ·
            refine ⟨110741303937796592262561485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73827535958531061508374323 110741303937796592262561485)
            ·
              refine ⟨41527988976673722098460557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110741303937796592262561485 41527988976673722098460557)
              ·
                refine ⟨15572995866252645786922709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41527988976673722098460557 15572995866252645786922709)
                ·
                  refine ⟨364992090615296385631001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15572995866252645786922709 364992090615296385631001)
                  ·
                    rfl

theorem cell23_6397376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 7].length) (baseStart_6397376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397376 prefixEnd_6397376 := by exact prefixLift 6397376
  have htrace : WordTrace (prefixWord ++ tailWord_6397376) baseStart_6397376 baseEnd_6397376 := by
    simpa [prefixWord, tailWord_6397376, baseEnd_6397376] using wordTrace_append hprefix tailTrace_6397376
  have hstable : (prefixWord ++ tailWord_6397376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397376).length < 2 ^ (prefixWord ++ tailWord_6397376).sum := by decide
  have hdescent : baseEnd_6397376 < baseStart_6397376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397378 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_6397378 : Nat := 118140960795 + 6397378 * 2 ^ 59
def prefixEnd_6397378 : Nat := 4983230072969 + 3 ^ 40 * 6397378 * 2
def baseEnd_6397378 : Nat := 3284929842498976462854001

theorem tailTrace_6397378 : CollatzResearch.WordTrace tailWord_6397378 prefixEnd_6397378 3284929842498976462854001 := by
  unfold tailWord_6397378
  simp only [CollatzResearch.WordTrace]
  refine ⟨58332886154349891505590197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155554363078266377348240525 58332886154349891505590197)
  ·
    refine ⟨5468708076970302328649081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58332886154349891505590197 5468708076970302328649081)
    ·
      refine ⟨4101531057727726746486811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5468708076970302328649081 4101531057727726746486811)
      ·
        refine ⟨6152296586591590119730217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4101531057727726746486811 6152296586591590119730217)
        ·
          refine ⟨4614222439943692589797663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6152296586591590119730217 4614222439943692589797663)
          ·
            refine ⟨6921333659915538884696495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4614222439943692589797663 6921333659915538884696495)
            ·
              refine ⟨10382000489873308327044743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6921333659915538884696495 10382000489873308327044743)
              ·
                refine ⟨15573000734809962490567115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10382000489873308327044743 15573000734809962490567115)
                ·
                  refine ⟨23359501102214943735850673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15573000734809962490567115 23359501102214943735850673)
                  ·
                    refine ⟨17519625826661207801888005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23359501102214943735850673 17519625826661207801888005)
                    ·
                      refine ⟨3284929842498976462854001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17519625826661207801888005 3284929842498976462854001)
                      ·
                        rfl

theorem cell23_6397378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_6397378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397378 prefixEnd_6397378 := by exact prefixLift 6397378
  have htrace : WordTrace (prefixWord ++ tailWord_6397378) baseStart_6397378 baseEnd_6397378 := by
    simpa [prefixWord, tailWord_6397378, baseEnd_6397378] using wordTrace_append hprefix tailTrace_6397378
  have hstable : (prefixWord ++ tailWord_6397378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397378).length < 2 ^ (prefixWord ++ tailWord_6397378).sum := by decide
  have hdescent : baseEnd_6397378 < baseStart_6397378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397494 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_6397494 : Nat := 118140960795 + 6397494 * 2 ^ 59
def prefixEnd_6397494 : Nat := 4983230072969 + 3 ^ 40 * 6397494 * 2
def baseEnd_6397494 : Nat := 3284989406254898009003467

theorem tailTrace_6397494 : CollatzResearch.WordTrace tailWord_6397494 prefixEnd_6397494 3284989406254898009003467 := by
  unfold tailWord_6397494
  simp only [CollatzResearch.WordTrace]
  refine ⟨14583485967811207364598971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 155557183656652878555722357 14583485967811207364598971)
  ·
    refine ⟨21875228951716811046898457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14583485967811207364598971 21875228951716811046898457)
    ·
      refine ⟨16406421713787608285173843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21875228951716811046898457 16406421713787608285173843)
      ·
        refine ⟨24609632570681412427760765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16406421713787608285173843 24609632570681412427760765)
        ·
          refine ⟨9228612214005529660410287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24609632570681412427760765 9228612214005529660410287)
          ·
            refine ⟨13842918321008294490615431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9228612214005529660410287 13842918321008294490615431)
            ·
              refine ⟨20764377481512441735923147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13842918321008294490615431 20764377481512441735923147)
              ·
                refine ⟨31146566222268662603884721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20764377481512441735923147 31146566222268662603884721)
                ·
                  refine ⟨23359924666701496952913541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31146566222268662603884721 23359924666701496952913541)
                  ·
                    refine ⟨4379985875006530678671289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23359924666701496952913541 4379985875006530678671289)
                    ·
                      refine ⟨3284989406254898009003467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4379985875006530678671289 3284989406254898009003467)
                      ·
                        rfl

theorem cell23_6397494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_6397494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397494 prefixEnd_6397494 := by exact prefixLift 6397494
  have htrace : WordTrace (prefixWord ++ tailWord_6397494) baseStart_6397494 baseEnd_6397494 := by
    simpa [prefixWord, tailWord_6397494, baseEnd_6397494] using wordTrace_append hprefix tailTrace_6397494
  have hstable : (prefixWord ++ tailWord_6397494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397494).length < 2 ^ (prefixWord ++ tailWord_6397494).sum := by decide
  have hdescent : baseEnd_6397494 < baseStart_6397494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397520 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 1, 5, 2]
def baseStart_6397520 : Nat := 118140960795 + 6397520 * 2 ^ 59
def prefixEnd_6397520 : Nat := 4983230072969 + 3 ^ 40 * 6397520 * 2
def baseEnd_6397520 : Nat := 3285002756751914907278347

theorem tailTrace_6397520 : CollatzResearch.WordTrace tailWord_6397520 prefixEnd_6397520 3285002756751914907278347 := by
  unfold tailWord_6397520
  simp only [CollatzResearch.WordTrace]
  refine ⟨116668361891442562137015007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155557815855256749516020009 116668361891442562137015007)
  ·
    refine ⟨175002542837163843205522511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116668361891442562137015007 175002542837163843205522511)
    ·
      refine ⟨262503814255745764808283767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175002542837163843205522511 262503814255745764808283767)
      ·
        refine ⟨393755721383618647212425651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262503814255745764808283767 393755721383618647212425651)
        ·
          refine ⟨590633582075427970818638477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393755721383618647212425651 590633582075427970818638477)
          ·
            refine ⟨221487593278285489056989429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 590633582075427970818638477 221487593278285489056989429)
            ·
              refine ⟨20764461869839264599092759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221487593278285489056989429 20764461869839264599092759)
              ·
                refine ⟨31146692804758896898639139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20764461869839264599092759 31146692804758896898639139)
                ·
                  refine ⟨46720039207138345347958709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31146692804758896898639139 46720039207138345347958709)
                  ·
                    refine ⟨4380003675669219876371129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46720039207138345347958709 4380003675669219876371129)
                    ·
                      refine ⟨3285002756751914907278347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4380003675669219876371129 3285002756751914907278347)
                      ·
                        rfl

theorem cell23_6397520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 1, 5, 2].length) (baseStart_6397520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397520 prefixEnd_6397520 := by exact prefixLift 6397520
  have htrace : WordTrace (prefixWord ++ tailWord_6397520) baseStart_6397520 baseEnd_6397520 := by
    simpa [prefixWord, tailWord_6397520, baseEnd_6397520] using wordTrace_append hprefix tailTrace_6397520
  have hstable : (prefixWord ++ tailWord_6397520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397520).length < 2 ^ (prefixWord ++ tailWord_6397520).sum := by decide
  have hdescent : baseEnd_6397520 < baseStart_6397520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397543 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 3, 6]
def baseStart_6397543 : Nat := 118140960795 + 6397543 * 2 ^ 59
def prefixEnd_6397543 : Nat := 4983230072969 + 3 ^ 40 * 6397543 * 2
def baseEnd_6397543 : Nat := 1095004855602322772430247

theorem tailTrace_6397543 : CollatzResearch.WordTrace tailWord_6397543 prefixEnd_6397543 1095004855602322772430247 := by
  unfold tailWord_6397543
  simp only [CollatzResearch.WordTrace]
  refine ⟨233337562661801799202117283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155558375107867866134744855 233337562661801799202117283)
  ·
    refine ⟨350006343992702698803175925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233337562661801799202117283 350006343992702698803175925)
    ·
      refine ⟨32813094749315878012797743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 350006343992702698803175925 32813094749315878012797743)
      ·
        refine ⟨49219642123973817019196615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32813094749315878012797743 49219642123973817019196615)
        ·
          refine ⟨73829463185960725528794923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49219642123973817019196615 73829463185960725528794923)
          ·
            refine ⟨110744194778941088293192385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73829463185960725528794923 110744194778941088293192385)
            ·
              refine ⟨83058146084205816219894289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110744194778941088293192385 83058146084205816219894289)
              ·
                refine ⟨62293609563154362164920717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83058146084205816219894289 62293609563154362164920717)
                ·
                  refine ⟨23360103586182885811845269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62293609563154362164920717 23360103586182885811845269)
                  ·
                    refine ⟨1095004855602322772430247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23360103586182885811845269 1095004855602322772430247)
                    ·
                      rfl

theorem cell23_6397543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_6397543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397543 prefixEnd_6397543 := by exact prefixLift 6397543
  have htrace : WordTrace (prefixWord ++ tailWord_6397543) baseStart_6397543 baseEnd_6397543 := by
    simpa [prefixWord, tailWord_6397543, baseEnd_6397543] using wordTrace_append hprefix tailTrace_6397543
  have hstable : (prefixWord ++ tailWord_6397543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397543).length < 2 ^ (prefixWord ++ tailWord_6397543).sum := by decide
  have hdescent : baseEnd_6397543 < baseStart_6397543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397544 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_6397544 : Nat := 118140960795 + 6397544 * 2 ^ 59
def prefixEnd_6397544 : Nat := 4983230072969 + 3 ^ 40 * 6397544 * 2
def baseEnd_6397544 : Nat := 3285015080287622813378237

theorem tailTrace_6397544 : CollatzResearch.WordTrace tailWord_6397544 prefixEnd_6397544 3285015080287622813378237 := by
  unfold tailWord_6397544
  simp only [CollatzResearch.WordTrace]
  refine ⟨116668799567399088186451843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155558399423198784248602457 116668799567399088186451843)
  ·
    refine ⟨175003199351098632279677765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116668799567399088186451843 175003199351098632279677765)
    ·
      refine ⟨32813099878330993552439581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175003199351098632279677765 32813099878330993552439581)
      ·
        refine ⟨12304912454374122582164843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32813099878330993552439581 12304912454374122582164843)
        ·
          refine ⟨18457368681561183873247265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12304912454374122582164843 18457368681561183873247265)
          ·
            refine ⟨13843026511170887904935449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18457368681561183873247265 13843026511170887904935449)
            ·
              refine ⟨10382269883378165928701587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13843026511170887904935449 10382269883378165928701587)
              ·
                refine ⟨15573404825067248893052381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10382269883378165928701587 15573404825067248893052381)
                ·
                  refine ⟨5840026809400218334894643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15573404825067248893052381 5840026809400218334894643)
                  ·
                    refine ⟨8760040214100327502341965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5840026809400218334894643 8760040214100327502341965)
                    ·
                      refine ⟨3285015080287622813378237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8760040214100327502341965 3285015080287622813378237)
                      ·
                        rfl

theorem cell23_6397544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_6397544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397544 prefixEnd_6397544 := by exact prefixLift 6397544
  have htrace : WordTrace (prefixWord ++ tailWord_6397544) baseStart_6397544 baseEnd_6397544 := by
    simpa [prefixWord, tailWord_6397544, baseEnd_6397544] using wordTrace_append hprefix tailTrace_6397544
  have hstable : (prefixWord ++ tailWord_6397544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397544).length < 2 ^ (prefixWord ++ tailWord_6397544).sum := by decide
  have hdescent : baseEnd_6397544 < baseStart_6397544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397563 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 6]
def baseStart_6397563 : Nat := 118140960795 + 6397563 * 2 ^ 59
def prefixEnd_6397563 : Nat := 4983230072969 + 3 ^ 40 * 6397563 * 2
def baseEnd_6397563 : Nat := 3285024836420058239040649

theorem tailTrace_6397563 : CollatzResearch.WordTrace tailWord_6397563 prefixEnd_6397563 3285024836420058239040649 := by
  unfold tailWord_6397563
  simp only [CollatzResearch.WordTrace]
  refine ⟨233338292121729342617845343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155558861414486228411896895 233338292121729342617845343)
  ·
    refine ⟨350007438182594013926768015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233338292121729342617845343 350007438182594013926768015)
    ·
      refine ⟨525011157273891020890152023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350007438182594013926768015 525011157273891020890152023)
      ·
        refine ⟨787516735910836531335228035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525011157273891020890152023 787516735910836531335228035)
        ·
          refine ⟨1181275103866254797002842053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787516735910836531335228035 1181275103866254797002842053)
          ·
            refine ⟨221489081974922774438032885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1181275103866254797002842053 221489081974922774438032885)
            ·
              refine ⟨20764601435149010103565583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221489081974922774438032885 20764601435149010103565583)
              ·
                refine ⟨31146902152723515155348375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20764601435149010103565583 31146902152723515155348375)
                ·
                  refine ⟨46720353229085272733022563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31146902152723515155348375 46720353229085272733022563)
                  ·
                    refine ⟨70080529843627909099533845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46720353229085272733022563 70080529843627909099533845)
                    ·
                      refine ⟨3285024836420058239040649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70080529843627909099533845 3285024836420058239040649)
                      ·
                        rfl

theorem cell23_6397563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 6].length) (baseStart_6397563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397563 prefixEnd_6397563 := by exact prefixLift 6397563
  have htrace : WordTrace (prefixWord ++ tailWord_6397563) baseStart_6397563 baseEnd_6397563 := by
    simpa [prefixWord, tailWord_6397563, baseEnd_6397563] using wordTrace_append hprefix tailTrace_6397563
  have hstable : (prefixWord ++ tailWord_6397563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397563).length < 2 ^ (prefixWord ++ tailWord_6397563).sum := by decide
  have hdescent : baseEnd_6397563 < baseStart_6397563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397573 : List Nat := [1, 3, 1, 1, 4, 1, 3, 9]
def baseStart_6397573 : Nat := 118140960795 + 6397573 * 2 ^ 59
def prefixEnd_6397573 : Nat := 4983230072969 + 3 ^ 40 * 6397573 * 2
def baseEnd_6397573 : Nat := 121667776712096414811689

theorem tailTrace_6397573 : CollatzResearch.WordTrace tailWord_6397573 prefixEnd_6397573 121667776712096414811689 := by
  unfold tailWord_6397573
  simp only [CollatzResearch.WordTrace]
  refine ⟨233338656851693114325709373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155559104567795409550472915 233338656851693114325709373)
  ·
    refine ⟨87501996319384917872141015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233338656851693114325709373 87501996319384917872141015)
    ·
      refine ⟨131252994479077376808211523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87501996319384917872141015 131252994479077376808211523)
      ·
        refine ⟨196879491718616065212317285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131252994479077376808211523 196879491718616065212317285)
        ·
          refine ⟨36914904697240512227309491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196879491718616065212317285 36914904697240512227309491)
          ·
            refine ⟨55372357045860768340964237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36914904697240512227309491 55372357045860768340964237)
            ·
              refine ⟨20764633892197788127861589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55372357045860768340964237 20764633892197788127861589)
              ·
                refine ⟨121667776712096414811689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20764633892197788127861589 121667776712096414811689)
                ·
                  rfl

theorem cell23_6397573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 9].length) (baseStart_6397573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397573 prefixEnd_6397573 := by exact prefixLift 6397573
  have htrace : WordTrace (prefixWord ++ tailWord_6397573) baseStart_6397573 baseEnd_6397573 := by
    simpa [prefixWord, tailWord_6397573, baseEnd_6397573] using wordTrace_append hprefix tailTrace_6397573
  have hstable : (prefixWord ++ tailWord_6397573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397573).length < 2 ^ (prefixWord ++ tailWord_6397573).sum := by decide
  have hdescent : baseEnd_6397573 < baseStart_6397573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397601 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 3, 2, 2]
def baseStart_6397601 : Nat := 118140960795 + 6397601 * 2 ^ 59
def prefixEnd_6397601 : Nat := 4983230072969 + 3 ^ 40 * 6397601 * 2
def baseEnd_6397601 : Nat := 3285044348684929090365475

theorem tailTrace_6397601 : CollatzResearch.WordTrace tailWord_6397601 prefixEnd_6397601 3285044348684929090365475 := by
  unfold tailWord_6397601
  simp only [CollatzResearch.WordTrace]
  refine ⟨233339678095591675107728657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155559785397061116738485771 233339678095591675107728657)
  ·
    refine ⟨175004758571693756330796493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233339678095591675107728657 175004758571693756330796493)
    ·
      refine ⟨65626784464385158624048685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175004758571693756330796493 65626784464385158624048685)
      ·
        refine ⟨24610044174144434484018257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65626784464385158624048685 24610044174144434484018257)
        ·
          refine ⟨18457533130608325863013693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24610044174144434484018257 18457533130608325863013693)
          ·
            refine ⟨6921574923978122198630135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18457533130608325863013693 6921574923978122198630135)
            ·
              refine ⟨10382362385967183297945203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6921574923978122198630135 10382362385967183297945203)
              ·
                refine ⟨15573543578950774946917805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10382362385967183297945203 15573543578950774946917805)
                ·
                  refine ⟨5840078842106540605094177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15573543578950774946917805 5840078842106540605094177)
                  ·
                    refine ⟨4380059131579905453820633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5840078842106540605094177 4380059131579905453820633)
                    ·
                      refine ⟨3285044348684929090365475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4380059131579905453820633 3285044348684929090365475)
                      ·
                        rfl

theorem cell23_6397601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_6397601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397601 prefixEnd_6397601 := by exact prefixLift 6397601
  have htrace : WordTrace (prefixWord ++ tailWord_6397601) baseStart_6397601 baseEnd_6397601 := by
    simpa [prefixWord, tailWord_6397601, baseEnd_6397601] using wordTrace_append hprefix tailTrace_6397601
  have hstable : (prefixWord ++ tailWord_6397601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397601).length < 2 ^ (prefixWord ++ tailWord_6397601).sum := by decide
  have hdescent : baseEnd_6397601 < baseStart_6397601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397603 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 2, 7]
def baseStart_6397603 : Nat := 118140960795 + 6397603 * 2 ^ 59
def prefixEnd_6397603 : Nat := 4983230072969 + 3 ^ 40 * 6397603 * 2
def baseEnd_6397603 : Nat := 1095015125215412694180155

theorem tailTrace_6397603 : CollatzResearch.WordTrace tailWord_6397603 prefixEnd_6397603 1095015125215412694180155 := by
  unfold tailWord_6397603
  simp only [CollatzResearch.WordTrace]
  refine ⟨233339751041584429449301463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155559834027722952966200975 233339751041584429449301463)
  ·
    refine ⟨350009626562376644173952195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233339751041584429449301463 350009626562376644173952195)
    ·
      refine ⟨525014439843564966260928293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350009626562376644173952195 525014439843564966260928293)
      ·
        refine ⟨98440207470668431173924055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 525014439843564966260928293 98440207470668431173924055)
        ·
          refine ⟨147660311206002646760886083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98440207470668431173924055 147660311206002646760886083)
          ·
            refine ⟨221490466809003970141329125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147660311206002646760886083 221490466809003970141329125)
            ·
              refine ⟨41529462526688244401499211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 221490466809003970141329125 41529462526688244401499211)
              ·
                refine ⟨62294193790032366602248817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41529462526688244401499211 62294193790032366602248817)
                ·
                  refine ⟨46720645342524274951686613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62294193790032366602248817 46720645342524274951686613)
                  ·
                    refine ⟨1095015125215412694180155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46720645342524274951686613 1095015125215412694180155)
                    ·
                      rfl

theorem cell23_6397603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 7].length) (baseStart_6397603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397603 prefixEnd_6397603 := by exact prefixLift 6397603
  have htrace : WordTrace (prefixWord ++ tailWord_6397603) baseStart_6397603 baseEnd_6397603 := by
    simpa [prefixWord, tailWord_6397603, baseEnd_6397603] using wordTrace_append hprefix tailTrace_6397603
  have hstable : (prefixWord ++ tailWord_6397603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397603).length < 2 ^ (prefixWord ++ tailWord_6397603).sum := by decide
  have hdescent : baseEnd_6397603 < baseStart_6397603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397621 : List Nat := [1, 3, 3, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_6397621 : Nat := 118140960795 + 6397621 * 2 ^ 59
def prefixEnd_6397621 : Nat := 4983230072969 + 3 ^ 40 * 6397621 * 2
def baseEnd_6397621 : Nat := 3285054618298019012115383

theorem tailTrace_6397621 : CollatzResearch.WordTrace tailWord_6397621 prefixEnd_6397621 3285054618298019012115383 := by
  unfold tailWord_6397621
  simp only [CollatzResearch.WordTrace]
  refine ⟨233340407555519218523456717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155560271703679479015637811 233340407555519218523456717)
  ·
    refine ⟨87502652833319706946296269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233340407555519218523456717 87502652833319706946296269)
    ·
      refine ⟨32813494812494890104861101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87502652833319706946296269 32813494812494890104861101)
      ·
        refine ⟨12305060554685583789322913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32813494812494890104861101 12305060554685583789322913)
        ·
          refine ⟨9228795416014187841992185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12305060554685583789322913 9228795416014187841992185)
          ·
            refine ⟨6921596562010640881494139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9228795416014187841992185 6921596562010640881494139)
            ·
              refine ⟨10382394843015961322241209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6921596562010640881494139 10382394843015961322241209)
              ·
                refine ⟨7786796132261970991680907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10382394843015961322241209 7786796132261970991680907)
                ·
                  refine ⟨11680194198392956487521361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7786796132261970991680907 11680194198392956487521361)
                  ·
                    refine ⟨8760145648794717365641021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11680194198392956487521361 8760145648794717365641021)
                    ·
                      refine ⟨3285054618298019012115383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8760145648794717365641021 3285054618298019012115383)
                      ·
                        rfl

theorem cell23_6397621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_6397621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397621 prefixEnd_6397621 := by exact prefixLift 6397621
  have htrace : WordTrace (prefixWord ++ tailWord_6397621) baseStart_6397621 baseEnd_6397621 := by
    simpa [prefixWord, tailWord_6397621, baseEnd_6397621] using wordTrace_append hprefix tailTrace_6397621
  have hstable : (prefixWord ++ tailWord_6397621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397621).length < 2 ^ (prefixWord ++ tailWord_6397621).sum := by decide
  have hdescent : baseEnd_6397621 < baseStart_6397621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397667 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 2, 6]
def baseStart_6397667 : Nat := 118140960795 + 6397667 * 2 ^ 59
def prefixEnd_6397667 : Nat := 4983230072969 + 3 ^ 40 * 6397667 * 2
def baseEnd_6397667 : Nat := 1095026079469375277380057

theorem tailTrace_6397667 : CollatzResearch.WordTrace tailWord_6397667 prefixEnd_6397667 1095026079469375277380057 := by
  unfold tailWord_6397667
  simp only [CollatzResearch.WordTrace]
  refine ⟨233342085313352568379631255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155561390208901712253087503 233342085313352568379631255)
  ·
    refine ⟨350013127970028852569446883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233342085313352568379631255 350013127970028852569446883)
    ·
      refine ⟨525019691955043278854170325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350013127970028852569446883 525019691955043278854170325)
      ·
        refine ⟨12305149030196326848144617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 525019691955043278854170325 12305149030196326848144617)
        ·
          refine ⟨9228861772647245136108463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12305149030196326848144617 9228861772647245136108463)
          ·
            refine ⟨13843292658970867704162695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9228861772647245136108463 13843292658970867704162695)
            ·
              refine ⟨20764938988456301556244043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13843292658970867704162695 20764938988456301556244043)
              ·
                refine ⟨31147408482684452334366065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20764938988456301556244043 31147408482684452334366065)
                ·
                  refine ⟨23360556362013339250774549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31147408482684452334366065 23360556362013339250774549)
                  ·
                    refine ⟨1095026079469375277380057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23360556362013339250774549 1095026079469375277380057)
                    ·
                      rfl

theorem cell23_6397667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 6].length) (baseStart_6397667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397667 prefixEnd_6397667 := by exact prefixLift 6397667
  have htrace : WordTrace (prefixWord ++ tailWord_6397667) baseStart_6397667 baseEnd_6397667 := by
    simpa [prefixWord, tailWord_6397667, baseEnd_6397667] using wordTrace_append hprefix tailTrace_6397667
  have hstable : (prefixWord ++ tailWord_6397667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397667).length < 2 ^ (prefixWord ++ tailWord_6397667).sum := by decide
  have hdescent : baseEnd_6397667 < baseStart_6397667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397690 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3]
def baseStart_6397690 : Nat := 118140960795 + 6397690 * 2 ^ 59
def prefixEnd_6397690 : Nat := 4983230072969 + 3 ^ 40 * 6397690 * 2
def baseEnd_6397690 : Nat := 3285090048463179242152565

theorem tailTrace_6397690 : CollatzResearch.WordTrace tailWord_6397690 prefixEnd_6397690 3285090048463179242152565 := by
  unfold tailWord_6397690
  simp only [CollatzResearch.WordTrace]
  refine ⟨58335731048067310826929631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155561949461512828871812349 58335731048067310826929631)
  ·
    refine ⟨87503596572100966240394447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58335731048067310826929631 87503596572100966240394447)
    ·
      refine ⟨131255394858151449360591671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87503596572100966240394447 131255394858151449360591671)
      ·
        refine ⟨196883092287227174040887507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131255394858151449360591671 196883092287227174040887507)
        ·
          refine ⟨295324638430840761061331261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196883092287227174040887507 295324638430840761061331261)
          ·
            refine ⟨110746739411565285397999223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295324638430840761061331261 110746739411565285397999223)
            ·
              refine ⟨166120109117347928096998835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110746739411565285397999223 166120109117347928096998835)
              ·
                refine ⟨249180163676021892145498253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166120109117347928096998835 249180163676021892145498253)
                ·
                  refine ⟨93442561378508209554561845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249180163676021892145498253 93442561378508209554561845)
                  ·
                    refine ⟨8760240129235144645740173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93442561378508209554561845 8760240129235144645740173)
                    ·
                      refine ⟨3285090048463179242152565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8760240129235144645740173 3285090048463179242152565)
                      ·
                        rfl

theorem cell23_6397690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_6397690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397690 prefixEnd_6397690 := by exact prefixLift 6397690
  have htrace : WordTrace (prefixWord ++ tailWord_6397690) baseStart_6397690 baseEnd_6397690 := by
    simpa [prefixWord, tailWord_6397690, baseEnd_6397690] using wordTrace_append hprefix tailTrace_6397690
  have hstable : (prefixWord ++ tailWord_6397690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397690).length < 2 ^ (prefixWord ++ tailWord_6397690).sum := by decide
  have hdescent : baseEnd_6397690 < baseStart_6397690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397697 : List Nat := [1, 2, 4, 1, 1, 1, 3, 5, 5]
def baseStart_6397697 : Nat := 118140960795 + 6397697 * 2 ^ 59
def prefixEnd_6397697 : Nat := 4983230072969 + 3 ^ 40 * 6397697 * 2
def baseEnd_6397697 : Nat := 365010404758640079418337

theorem tailTrace_6397697 : CollatzResearch.WordTrace tailWord_6397697 prefixEnd_6397697 365010404758640079418337 := by
  unfold tailWord_6397697
  simp only [CollatzResearch.WordTrace]
  refine ⟨233343179503243883503223345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155562119668829255668815563 233343179503243883503223345)
  ·
    refine ⟨175007384627432912627417509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233343179503243883503223345 175007384627432912627417509)
    ·
      refine ⟨32813884617643671117640783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175007384627432912627417509 32813884617643671117640783)
      ·
        refine ⟨49220826926465506676461175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32813884617643671117640783 49220826926465506676461175)
        ·
          refine ⟨73831240389698260014691763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49220826926465506676461175 73831240389698260014691763)
          ·
            refine ⟨110746860584547390022037645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73831240389698260014691763 110746860584547390022037645)
            ·
              refine ⟨41530072719205271258264117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110746860584547390022037645 41530072719205271258264117)
              ·
                refine ⟨3893444317425494180462261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41530072719205271258264117 3893444317425494180462261)
                ·
                  refine ⟨365010404758640079418337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3893444317425494180462261 365010404758640079418337)
                  ·
                    rfl

theorem cell23_6397697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 5].length) (baseStart_6397697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397697 prefixEnd_6397697 := by exact prefixLift 6397697
  have htrace : WordTrace (prefixWord ++ tailWord_6397697) baseStart_6397697 baseEnd_6397697 := by
    simpa [prefixWord, tailWord_6397697, baseEnd_6397697] using wordTrace_append hprefix tailTrace_6397697
  have hstable : (prefixWord ++ tailWord_6397697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397697).length < 2 ^ (prefixWord ++ tailWord_6397697).sum := by decide
  have hdescent : baseEnd_6397697 < baseStart_6397697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397702 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_6397702 : Nat := 118140960795 + 6397702 * 2 ^ 59
def prefixEnd_6397702 : Nat := 4983230072969 + 3 ^ 40 * 6397702 * 2
def baseEnd_6397702 : Nat := 3285096210231033195202511

theorem tailTrace_6397702 : CollatzResearch.WordTrace tailWord_6397702 prefixEnd_6397702 3285096210231033195202511 := by
  unfold tailWord_6397702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7291980058382055292411105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 155562241245483846238103573 7291980058382055292411105)
  ·
    refine ⟨5468985043786541469308329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7291980058382055292411105 5468985043786541469308329)
    ·
      refine ⟨4101738782839906101981247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5468985043786541469308329 4101738782839906101981247)
      ·
        refine ⟨6152608174259859152971871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4101738782839906101981247 6152608174259859152971871)
        ·
          refine ⟨9228912261389788729457807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6152608174259859152971871 9228912261389788729457807)
          ·
            refine ⟨13843368392084683094186711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9228912261389788729457807 13843368392084683094186711)
            ·
              refine ⟨20765052588127024641280067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13843368392084683094186711 20765052588127024641280067)
              ·
                refine ⟨31147578882190536961920101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20765052588127024641280067 31147578882190536961920101)
                ·
                  refine ⟨5840171040410725680360019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31147578882190536961920101 5840171040410725680360019)
                  ·
                    refine ⟨8760256560616088520540029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5840171040410725680360019 8760256560616088520540029)
                    ·
                      refine ⟨3285096210231033195202511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8760256560616088520540029 3285096210231033195202511)
                      ·
                        rfl

theorem cell23_6397702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_6397702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397702 prefixEnd_6397702 := by exact prefixLift 6397702
  have htrace : WordTrace (prefixWord ++ tailWord_6397702) baseStart_6397702 baseEnd_6397702 := by
    simpa [prefixWord, tailWord_6397702, baseEnd_6397702] using wordTrace_append hprefix tailTrace_6397702
  have hstable : (prefixWord ++ tailWord_6397702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397702).length < 2 ^ (prefixWord ++ tailWord_6397702).sum := by decide
  have hdescent : baseEnd_6397702 < baseStart_6397702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397714 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 7]
def baseStart_6397714 : Nat := 118140960795 + 6397714 * 2 ^ 59
def prefixEnd_6397714 : Nat := 4983230072969 + 3 ^ 40 * 6397714 * 2
def baseEnd_6397714 : Nat := 365011374666543016472495

theorem tailTrace_6397714 : CollatzResearch.WordTrace tailWord_6397714 prefixEnd_6397714 365011374666543016472495 := by
  unfold tailWord_6397714
  simp only [CollatzResearch.WordTrace]
  refine ⟨58335949886045573851648049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155562533029454863604394797 58335949886045573851648049)
  ·
    refine ⟨43751962414534180388736037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58335949886045573851648049 43751962414534180388736037)
    ·
      refine ⟨8203492952725158822888007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43751962414534180388736037 8203492952725158822888007)
      ·
        refine ⟨12305239429087738234332011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8203492952725158822888007 12305239429087738234332011)
        ·
          refine ⟨18457859143631607351498017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12305239429087738234332011 18457859143631607351498017)
          ·
            refine ⟨13843394357723705513623513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18457859143631607351498017 13843394357723705513623513)
            ·
              refine ⟨10382545768292779135217635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13843394357723705513623513 10382545768292779135217635)
              ·
                refine ⟨15573818652439168702826453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10382545768292779135217635 15573818652439168702826453)
                ·
                  refine ⟨365011374666543016472495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15573818652439168702826453 365011374666543016472495)
                  ·
                    rfl

theorem cell23_6397714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_6397714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397714 prefixEnd_6397714 := by exact prefixLift 6397714
  have htrace : WordTrace (prefixWord ++ tailWord_6397714) baseStart_6397714 baseEnd_6397714 := by
    simpa [prefixWord, tailWord_6397714, baseEnd_6397714] using wordTrace_append hprefix tailTrace_6397714
  have hstable : (prefixWord ++ tailWord_6397714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397714).length < 2 ^ (prefixWord ++ tailWord_6397714).sum := by decide
  have hdescent : baseEnd_6397714 < baseStart_6397714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397720 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 1, 2, 5]
def baseStart_6397720 : Nat := 118140960795 + 6397720 * 2 ^ 59
def prefixEnd_6397720 : Nat := 4983230072969 + 3 ^ 40 * 6397720 * 2
def baseEnd_6397720 : Nat := 3285105452882814124777427

theorem tailTrace_6397720 : CollatzResearch.WordTrace tailWord_6397720 prefixEnd_6397720 3285105452882814124777427 := by
  unfold tailWord_6397720
  simp only [CollatzResearch.WordTrace]
  refine ⟨116672009191080279215655307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155562678921440372287540409 116672009191080279215655307)
  ·
    refine ⟨175008013786620418823482961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116672009191080279215655307 175008013786620418823482961)
    ·
      refine ⟨131256010339965314117612221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175008013786620418823482961 131256010339965314117612221)
      ·
        refine ⟨49221003877486992794104583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131256010339965314117612221 49221003877486992794104583)
        ·
          refine ⟨73831505816230489191156875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49221003877486992794104583 73831505816230489191156875)
          ·
            refine ⟨110747258724345733786735313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73831505816230489191156875 110747258724345733786735313)
            ·
              refine ⟨83060444043259300340051485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110747258724345733786735313 83060444043259300340051485)
              ·
                refine ⟨31147666516222237627519307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83060444043259300340051485 31147666516222237627519307)
                ·
                  refine ⟨46721499774333356441278961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31147666516222237627519307 46721499774333356441278961)
                  ·
                    refine ⟨35041124830750017330959221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46721499774333356441278961 35041124830750017330959221)
                    ·
                      refine ⟨3285105452882814124777427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35041124830750017330959221 3285105452882814124777427)
                      ·
                        rfl

theorem cell23_6397720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_6397720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397720 prefixEnd_6397720 := by exact prefixLift 6397720
  have htrace : WordTrace (prefixWord ++ tailWord_6397720) baseStart_6397720 baseEnd_6397720 := by
    simpa [prefixWord, tailWord_6397720, baseEnd_6397720] using wordTrace_append hprefix tailTrace_6397720
  have hstable : (prefixWord ++ tailWord_6397720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397720).length < 2 ^ (prefixWord ++ tailWord_6397720).sum := by decide
  have hdescent : baseEnd_6397720 < baseStart_6397720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397767 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 3]
def baseStart_6397767 : Nat := 118140960795 + 6397767 * 2 ^ 59
def prefixEnd_6397767 : Nat := 4983230072969 + 3 ^ 40 * 6397767 * 2
def baseEnd_6397767 : Nat := 3285129586473575440889711

theorem tailTrace_6397767 : CollatzResearch.WordTrace tailWord_6397767 prefixEnd_6397767 3285129586473575440889711 := by
  unfold tailWord_6397767
  simp only [CollatzResearch.WordTrace]
  refine ⟨233345732612990285458271555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155563821741993523638847703 233345732612990285458271555)
  ·
    refine ⟨350018598919485428187407333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233345732612990285458271555 350018598919485428187407333)
    ·
      refine ⟨65628487297403517785138875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 350018598919485428187407333 65628487297403517785138875)
      ·
        refine ⟨98442730946105276677708313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65628487297403517785138875 98442730946105276677708313)
        ·
          refine ⟨73832048209578957508281235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98442730946105276677708313 73832048209578957508281235)
          ·
            refine ⟨110748072314368436262421853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73832048209578957508281235 110748072314368436262421853)
            ·
              refine ⟨41530527117888163598408195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110748072314368436262421853 41530527117888163598408195)
              ·
                refine ⟨62295790676832245397612293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41530527117888163598408195 62295790676832245397612293)
                ·
                  refine ⟨11680460751906046012052305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62295790676832245397612293 11680460751906046012052305)
                  ·
                    refine ⟨8760345563929534509039229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11680460751906046012052305 8760345563929534509039229)
                    ·
                      refine ⟨3285129586473575440889711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8760345563929534509039229 3285129586473575440889711)
                      ·
                        rfl

theorem cell23_6397767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_6397767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397767 prefixEnd_6397767 := by exact prefixLift 6397767
  have htrace : WordTrace (prefixWord ++ tailWord_6397767) baseStart_6397767 baseEnd_6397767 := by
    simpa [prefixWord, tailWord_6397767, baseEnd_6397767] using wordTrace_append hprefix tailTrace_6397767
  have hstable : (prefixWord ++ tailWord_6397767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397767).length < 2 ^ (prefixWord ++ tailWord_6397767).sum := by decide
  have hdescent : baseEnd_6397767 < baseStart_6397767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397770 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 8]
def baseStart_6397770 : Nat := 118140960795 + 6397770 * 2 ^ 59
def prefixEnd_6397770 : Nat := 4983230072969 + 3 ^ 40 * 6397770 * 2
def baseEnd_6397770 : Nat := 365014569657282103239133

theorem tailTrace_6397770 : CollatzResearch.WordTrace tailWord_6397770 prefixEnd_6397770 365014569657282103239133 := by
  unfold tailWord_6397770
  simp only [CollatzResearch.WordTrace]
  refine ⟨58336460507994854242657691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155563894687986277980420509 58336460507994854242657691)
  ·
    refine ⟨87504690761992281363986537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58336460507994854242657691 87504690761992281363986537)
    ·
      refine ⟨65628518071494211022989903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87504690761992281363986537 65628518071494211022989903)
      ·
        refine ⟨98442777107241316534484855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65628518071494211022989903 98442777107241316534484855)
        ·
          refine ⟨147664165660861974801727283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98442777107241316534484855 147664165660861974801727283)
          ·
            refine ⟨221496248491292962202590925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147664165660861974801727283 221496248491292962202590925)
            ·
              refine ⟨83061093184234860825971597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221496248491292962202590925 83061093184234860825971597)
              ·
                refine ⟨31147909944088072809739349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83061093184234860825971597 31147909944088072809739349)
                ·
                  refine ⟨365014569657282103239133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31147909944088072809739349 365014569657282103239133)
                  ·
                    rfl

theorem cell23_6397770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 8].length) (baseStart_6397770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397770 prefixEnd_6397770 := by exact prefixLift 6397770
  have htrace : WordTrace (prefixWord ++ tailWord_6397770) baseStart_6397770 baseEnd_6397770 := by
    simpa [prefixWord, tailWord_6397770, baseEnd_6397770] using wordTrace_append hprefix tailTrace_6397770
  have hstable : (prefixWord ++ tailWord_6397770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397770).length < 2 ^ (prefixWord ++ tailWord_6397770).sum := by decide
  have hdescent : baseEnd_6397770 < baseStart_6397770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397824 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 2, 3, 2]
def baseStart_6397824 : Nat := 118140960795 + 6397824 * 2 ^ 59
def prefixEnd_6397824 : Nat := 4983230072969 + 3 ^ 40 * 6397824 * 2
def baseEnd_6397824 : Nat := 3285158854870881717876949

theorem tailTrace_6397824 : CollatzResearch.WordTrace tailWord_6397824 prefixEnd_6397824 3285158854870881717876949 := by
  unfold tailWord_6397824
  simp only [CollatzResearch.WordTrace]
  refine ⟨116673905786891892096548263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155565207715855856128731017 116673905786891892096548263)
  ·
    refine ⟨175010858680337838144822395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116673905786891892096548263 175010858680337838144822395)
    ·
      refine ⟨262516288020506757217233593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175010858680337838144822395 262516288020506757217233593)
      ·
        refine ⟨196887216015380067912925195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262516288020506757217233593 196887216015380067912925195)
        ·
          refine ⟨295330824023070101869387793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196887216015380067912925195 295330824023070101869387793)
          ·
            refine ⟨221498118017302576402040845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295330824023070101869387793 221498118017302576402040845)
            ·
              refine ⟨83061794256488466150765317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221498118017302576402040845 83061794256488466150765317)
              ·
                refine ⟨15574086423091587403268497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83061794256488466150765317 15574086423091587403268497)
                ·
                  refine ⟨11680564817318690552451373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15574086423091587403268497 11680564817318690552451373)
                  ·
                    refine ⟨4380211806494508957169265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11680564817318690552451373 4380211806494508957169265)
                    ·
                      refine ⟨3285158854870881717876949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4380211806494508957169265 3285158854870881717876949)
                      ·
                        rfl

theorem cell23_6397824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 2, 3, 2].length) (baseStart_6397824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397824 prefixEnd_6397824 := by exact prefixLift 6397824
  have htrace : WordTrace (prefixWord ++ tailWord_6397824) baseStart_6397824 baseEnd_6397824 := by
    simpa [prefixWord, tailWord_6397824, baseEnd_6397824] using wordTrace_append hprefix tailTrace_6397824
  have hstable : (prefixWord ++ tailWord_6397824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397824).length < 2 ^ (prefixWord ++ tailWord_6397824).sum := by decide
  have hdescent : baseEnd_6397824 < baseStart_6397824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397847 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 1, 6]
def baseStart_6397847 : Nat := 118140960795 + 6397847 * 2 ^ 59
def prefixEnd_6397847 : Nat := 4983230072969 + 3 ^ 40 * 6397847 * 2
def baseEnd_6397847 : Nat := 1095056888308645042629781

theorem tailTrace_6397847 : CollatzResearch.WordTrace tailWord_6397847 prefixEnd_6397847 1095056888308645042629781 := by
  unfold tailWord_6397847
  simp only [CollatzResearch.WordTrace]
  refine ⟨233348650452700459121183795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155565766968466972747455863 233348650452700459121183795)
  ·
    refine ⟨350022975679050688681775693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233348650452700459121183795 350022975679050688681775693)
    ·
      refine ⟨131258615879644008255665885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350022975679050688681775693 131258615879644008255665885)
      ·
        refine ⟨49221980954866503095874707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131258615879644008255665885 49221980954866503095874707)
        ·
          refine ⟨73832971432299754643812061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49221980954866503095874707 73832971432299754643812061)
          ·
            refine ⟨27687364287112407991429523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73832971432299754643812061 27687364287112407991429523)
            ·
              refine ⟨41531046430668611987144285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27687364287112407991429523 41531046430668611987144285)
              ·
                refine ⟨15574142411500729495179107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41531046430668611987144285 15574142411500729495179107)
                ·
                  refine ⟨23361213617251094242768661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15574142411500729495179107 23361213617251094242768661)
                  ·
                    refine ⟨1095056888308645042629781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23361213617251094242768661 1095056888308645042629781)
                    ·
                      rfl

theorem cell23_6397847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_6397847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397847 prefixEnd_6397847 := by exact prefixLift 6397847
  have htrace : WordTrace (prefixWord ++ tailWord_6397847) baseStart_6397847 baseEnd_6397847 := by
    simpa [prefixWord, tailWord_6397847, baseEnd_6397847] using wordTrace_append hprefix tailTrace_6397847
  have hstable : (prefixWord ++ tailWord_6397847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397847).length < 2 ^ (prefixWord ++ tailWord_6397847).sum := by decide
  have hdescent : baseEnd_6397847 < baseStart_6397847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397848 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 3, 1, 3]
def baseStart_6397848 : Nat := 118140960795 + 6397848 * 2 ^ 59
def prefixEnd_6397848 : Nat := 4983230072969 + 3 ^ 40 * 6397848 * 2
def baseEnd_6397848 : Nat := 3285171178406589623976839

theorem tailTrace_6397848 : CollatzResearch.WordTrace tailWord_6397848 prefixEnd_6397848 3285171178406589623976839 := by
  unfold tailWord_6397848
  simp only [CollatzResearch.WordTrace]
  refine ⟨116674343462848418145985099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155565791283797890861313465 116674343462848418145985099)
  ·
    refine ⟨175011515194272627218977649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116674343462848418145985099 175011515194272627218977649)
    ·
      refine ⟨131258636395704470414233237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175011515194272627218977649 131258636395704470414233237)
      ·
        refine ⟨6152748581048647050667183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 131258636395704470414233237 6152748581048647050667183)
        ·
          refine ⟨9229122871572970576000775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6152748581048647050667183 9229122871572970576000775)
          ·
            refine ⟨13843684307359455864001163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9229122871572970576000775 13843684307359455864001163)
            ·
              refine ⟨20765526461039183796001745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13843684307359455864001163 20765526461039183796001745)
              ·
                refine ⟨15574144845779387847001309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20765526461039183796001745 15574144845779387847001309)
                ·
                  refine ⟨5840304317167270442625491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15574144845779387847001309 5840304317167270442625491)
                  ·
                    refine ⟨8760456475750905663938237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5840304317167270442625491 8760456475750905663938237)
                    ·
                      refine ⟨3285171178406589623976839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8760456475750905663938237 3285171178406589623976839)
                      ·
                        rfl

theorem cell23_6397848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_6397848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397848 prefixEnd_6397848 := by exact prefixLift 6397848
  have htrace : WordTrace (prefixWord ++ tailWord_6397848) baseStart_6397848 baseEnd_6397848 := by
    simpa [prefixWord, tailWord_6397848, baseEnd_6397848] using wordTrace_append hprefix tailTrace_6397848
  have hstable : (prefixWord ++ tailWord_6397848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397848).length < 2 ^ (prefixWord ++ tailWord_6397848).sum := by decide
  have hdescent : baseEnd_6397848 < baseStart_6397848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397877 : List Nat := [1, 3, 3, 2, 1, 3, 10]
def baseStart_6397877 : Nat := 118140960795 + 6397877 * 2 ^ 59
def prefixEnd_6397877 : Nat := 4983230072969 + 3 ^ 40 * 6397877 * 2
def baseEnd_6397877 : Nat := 40557852707970000129805

theorem tailTrace_6397877 : CollatzResearch.WordTrace tailWord_6397877 prefixEnd_6397877 40557852707970000129805 := by
  unfold tailWord_6397877
  simp only [CollatzResearch.WordTrace]
  refine ⟨233349744642591774244775885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155566496428394516163183923 233349744642591774244775885)
  ·
    refine ⟨87506154240971915341790957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233349744642591774244775885 87506154240971915341790957)
    ·
      refine ⟨32814807840364468253171609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87506154240971915341790957 32814807840364468253171609)
      ·
        refine ⟨24611105880273351189878707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32814807840364468253171609 24611105880273351189878707)
        ·
          refine ⟨36916658820410026784818061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24611105880273351189878707 36916658820410026784818061)
          ·
            refine ⟨13843747057653760044306773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36916658820410026784818061 13843747057653760044306773)
            ·
              refine ⟨40557852707970000129805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13843747057653760044306773 40557852707970000129805)
              ·
                rfl

theorem cell23_6397877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 10].length) (baseStart_6397877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397877 prefixEnd_6397877 := by exact prefixLift 6397877
  have htrace : WordTrace (prefixWord ++ tailWord_6397877) baseStart_6397877 baseEnd_6397877 := by
    simpa [prefixWord, tailWord_6397877, baseEnd_6397877] using wordTrace_append hprefix tailTrace_6397877
  have hstable : (prefixWord ++ tailWord_6397877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397877).length < 2 ^ (prefixWord ++ tailWord_6397877).sum := by decide
  have hdescent : baseEnd_6397877 < baseStart_6397877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397888 : List Nat := [2, 1, 1, 2, 3, 2, 1, 6, 1, 2, 2]
def baseStart_6397888 : Nat := 118140960795 + 6397888 * 2 ^ 59
def prefixEnd_6397888 : Nat := 4983230072969 + 3 ^ 40 * 6397888 * 2
def baseEnd_6397888 : Nat := 3285191717632769467476655

theorem tailTrace_6397888 : CollatzResearch.WordTrace tailWord_6397888 prefixEnd_6397888 3285191717632769467476655 := by
  unfold tailWord_6397888
  simp only [CollatzResearch.WordTrace]
  refine ⟨116675072922775961561713159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155566763897034615415617545 116675072922775961561713159)
  ·
    refine ⟨175012609384163942342569739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116675072922775961561713159 175012609384163942342569739)
    ·
      refine ⟨262518914076245913513854609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175012609384163942342569739 262518914076245913513854609)
      ·
        refine ⟨196889185557184435135390957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262518914076245913513854609 196889185557184435135390957)
        ·
          refine ⟨73833444583944163175771609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196889185557184435135390957 73833444583944163175771609)
          ·
            refine ⟨55375083437958122381828707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73833444583944163175771609 55375083437958122381828707)
            ·
              refine ⟨83062625156937183572743061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55375083437958122381828707 83062625156937183572743061)
              ·
                refine ⟨3893560554231430479972331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83062625156937183572743061 3893560554231430479972331)
                ·
                  refine ⟨5840340831347145719958497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3893560554231430479972331 5840340831347145719958497)
                  ·
                    refine ⟨4380255623510359289968873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5840340831347145719958497 4380255623510359289968873)
                    ·
                      refine ⟨3285191717632769467476655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4380255623510359289968873 3285191717632769467476655)
                      ·
                        rfl

theorem cell23_6397888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 1, 2, 2].length) (baseStart_6397888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397888 prefixEnd_6397888 := by exact prefixLift 6397888
  have htrace : WordTrace (prefixWord ++ tailWord_6397888) baseStart_6397888 baseEnd_6397888 := by
    simpa [prefixWord, tailWord_6397888, baseEnd_6397888] using wordTrace_append hprefix tailTrace_6397888
  have hstable : (prefixWord ++ tailWord_6397888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397888).length < 2 ^ (prefixWord ++ tailWord_6397888).sum := by decide
  have hdescent : baseEnd_6397888 < baseStart_6397888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397904 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 3]
def baseStart_6397904 : Nat := 118140960795 + 6397904 * 2 ^ 59
def prefixEnd_6397904 : Nat := 4983230072969 + 3 ^ 40 * 6397904 * 2
def baseEnd_6397904 : Nat := 3285199933323241404876581

theorem tailTrace_6397904 : CollatzResearch.WordTrace tailWord_6397904 prefixEnd_6397904 3285199933323241404876581 := by
  unfold tailWord_6397904
  simp only [CollatzResearch.WordTrace]
  refine ⟨116675364706746978928004383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155567152942329305237339177 116675364706746978928004383)
  ·
    refine ⟨175013047060120468392006575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116675364706746978928004383 175013047060120468392006575)
    ·
      refine ⟨262519570590180702588009863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175013047060120468392006575 262519570590180702588009863)
      ·
        refine ⟨393779355885271053882014795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262519570590180702588009863 393779355885271053882014795)
        ·
          refine ⟨590669033827906580823022193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393779355885271053882014795 590669033827906580823022193)
          ·
            refine ⟨443001775370929935617266645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 590669033827906580823022193 443001775370929935617266645)
            ·
              refine ⟨10382854110256170366029687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 443001775370929935617266645 10382854110256170366029687)
              ·
                refine ⟨15574281165384255549044531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10382854110256170366029687 15574281165384255549044531)
                ·
                  refine ⟨23361421748076383323566797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15574281165384255549044531 23361421748076383323566797)
                  ·
                    refine ⟨8760533155528643746337549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23361421748076383323566797 8760533155528643746337549)
                    ·
                      refine ⟨3285199933323241404876581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8760533155528643746337549 3285199933323241404876581)
                      ·
                        rfl

theorem cell23_6397904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 3].length) (baseStart_6397904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397904 prefixEnd_6397904 := by exact prefixLift 6397904
  have htrace : WordTrace (prefixWord ++ tailWord_6397904) baseStart_6397904 baseEnd_6397904 := by
    simpa [prefixWord, tailWord_6397904, baseEnd_6397904] using wordTrace_append hprefix tailTrace_6397904
  have hstable : (prefixWord ++ tailWord_6397904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397904).length < 2 ^ (prefixWord ++ tailWord_6397904).sum := by decide
  have hdescent : baseEnd_6397904 < baseStart_6397904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6397916 : List Nat := [2, 2, 6, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_6397916 : Nat := 118140960795 + 6397916 * 2 ^ 59
def prefixEnd_6397916 : Nat := 4983230072969 + 3 ^ 40 * 6397916 * 2
def baseEnd_6397916 : Nat := 3285206095091095357926527

theorem tailTrace_6397916 : CollatzResearch.WordTrace tailWord_6397916 prefixEnd_6397916 3285206095091095357926527 := by
  unfold tailWord_6397916
  simp only [CollatzResearch.WordTrace]
  refine ⟨116675583544725241952722801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155567444726300322603630401 116675583544725241952722801)
  ·
    refine ⟨87506687658543931464542101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116675583544725241952722801 87506687658543931464542101)
    ·
      refine ⟨4101875983994246787400411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87506687658543931464542101 4101875983994246787400411)
      ·
        refine ⟨6152813975991370181100617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4101875983994246787400411 6152813975991370181100617)
        ·
          refine ⟨4614610481993527635825463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6152813975991370181100617 4614610481993527635825463)
          ·
            refine ⟨6921915722990291453738195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4614610481993527635825463 6921915722990291453738195)
            ·
              refine ⟨10382873584485437180607293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6921915722990291453738195 10382873584485437180607293)
              ·
                refine ⟨3893577594182038942727735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10382873584485437180607293 3893577594182038942727735)
                ·
                  refine ⟨5840366391273058414091603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3893577594182038942727735 5840366391273058414091603)
                  ·
                    refine ⟨8760549586909587621137405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5840366391273058414091603 8760549586909587621137405)
                    ·
                      refine ⟨3285206095091095357926527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8760549586909587621137405 3285206095091095357926527)
                      ·
                        rfl

theorem cell23_6397916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_6397916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6397916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6397916 prefixEnd_6397916 := by exact prefixLift 6397916
  have htrace : WordTrace (prefixWord ++ tailWord_6397916) baseStart_6397916 baseEnd_6397916 := by
    simpa [prefixWord, tailWord_6397916, baseEnd_6397916] using wordTrace_append hprefix tailTrace_6397916
  have hstable : (prefixWord ++ tailWord_6397916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6397916).length < 2 ^ (prefixWord ++ tailWord_6397916).sum := by decide
  have hdescent : baseEnd_6397916 < baseStart_6397916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6397916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398001 : List Nat := [1, 2, 2, 3, 1, 4, 1, 4, 5]
def baseStart_6398001 : Nat := 118140960795 + 6398001 * 2 ^ 59
def prefixEnd_6398001 : Nat := 4983230072969 + 3 ^ 40 * 6398001 * 2
def baseEnd_6398001 : Nat := 365027748994080836151515

theorem tailTrace_6398001 : CollatzResearch.WordTrace tailWord_6398001 prefixEnd_6398001 365027748994080836151515 := by
  unfold tailWord_6398001
  simp only [CollatzResearch.WordTrace]
  refine ⟨233354267294142543422289857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155569511529428362281526571 233354267294142543422289857)
  ·
    refine ⟨175015700470606907566717393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233354267294142543422289857 175015700470606907566717393)
    ·
      refine ⟨131261775352955180675038045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175015700470606907566717393 131261775352955180675038045)
      ·
        refine ⟨49223165757358192753139267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131261775352955180675038045 49223165757358192753139267)
        ·
          refine ⟨73834748636037289129708901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49223165757358192753139267 73834748636037289129708901)
          ·
            refine ⟨13844015369256991711820419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73834748636037289129708901 13844015369256991711820419)
            ·
              refine ⟨20766023053885487567730629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13844015369256991711820419 20766023053885487567730629)
              ·
                refine ⟨3893629322603528918949493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20766023053885487567730629 3893629322603528918949493)
                ·
                  refine ⟨365027748994080836151515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3893629322603528918949493 365027748994080836151515)
                  ·
                    rfl

theorem cell23_6398001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 5].length) (baseStart_6398001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398001 prefixEnd_6398001 := by exact prefixLift 6398001
  have htrace : WordTrace (prefixWord ++ tailWord_6398001) baseStart_6398001 baseEnd_6398001 := by
    simpa [prefixWord, tailWord_6398001, baseEnd_6398001] using wordTrace_append hprefix tailTrace_6398001
  have hstable : (prefixWord ++ tailWord_6398001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398001).length < 2 ^ (prefixWord ++ tailWord_6398001).sum := by decide
  have hdescent : baseEnd_6398001 < baseStart_6398001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398027 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 2, 8]
def baseStart_6398027 : Nat := 118140960795 + 6398027 * 2 ^ 59
def prefixEnd_6398027 : Nat := 4983230072969 + 3 ^ 40 * 6398027 * 2
def baseEnd_6398027 : Nat := 1095087697147914807879505

theorem tailTrace_6398027 : CollatzResearch.WordTrace tailWord_6398027 prefixEnd_6398027 1095087697147914807879505 := by
  unfold tailWord_6398027
  simp only [CollatzResearch.WordTrace]
  refine ⟨233355215592048349862736335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155570143728032233241824223 233355215592048349862736335)
  ·
    refine ⟨350032823388072524794104503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233355215592048349862736335 350032823388072524794104503)
    ·
      refine ⟨525049235082108787191156755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350032823388072524794104503 525049235082108787191156755)
      ·
        refine ⟨787573852623163180786735133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525049235082108787191156755 787573852623163180786735133)
        ·
          refine ⟨295340194733686192795025675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 787573852623163180786735133 295340194733686192795025675)
          ·
            refine ⟨443010292100529289192538513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295340194733686192795025675 443010292100529289192538513)
            ·
              refine ⟨332257719075396966894403885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443010292100529289192538513 332257719075396966894403885)
              ·
                refine ⟨124596644653273862585401457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332257719075396966894403885 124596644653273862585401457)
                ·
                  refine ⟨93447483489955396939051093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124596644653273862585401457 93447483489955396939051093)
                  ·
                    refine ⟨1095087697147914807879505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93447483489955396939051093 1095087697147914807879505)
                    ·
                      rfl

theorem cell23_6398027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 8].length) (baseStart_6398027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398027 prefixEnd_6398027 := by exact prefixLift 6398027
  have htrace : WordTrace (prefixWord ++ tailWord_6398027) baseStart_6398027 baseEnd_6398027 := by
    simpa [prefixWord, tailWord_6398027, baseEnd_6398027] using wordTrace_append hprefix tailTrace_6398027
  have hstable : (prefixWord ++ tailWord_6398027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398027).length < 2 ^ (prefixWord ++ tailWord_6398027).sum := by decide
  have hdescent : baseEnd_6398027 < baseStart_6398027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398046 : List Nat := [4, 4, 1, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_6398046 : Nat := 118140960795 + 6398046 * 2 ^ 59
def prefixEnd_6398046 : Nat := 4983230072969 + 3 ^ 40 * 6398046 * 2
def baseEnd_6398046 : Nat := 3285272847576179849300929

theorem tailTrace_6398046 : CollatzResearch.WordTrace tailWord_6398046 prefixEnd_6398046 3285272847576179849300929 := by
  unfold tailWord_6398046
  simp only [CollatzResearch.WordTrace]
  refine ⟨29169488572372439513459749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155570605719319677405118661 29169488572372439513459749)
  ·
    refine ⟨5469279107319832408773703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29169488572372439513459749 5469279107319832408773703)
    ·
      refine ⟨8203918660979748613160555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5469279107319832408773703 8203918660979748613160555)
      ·
        refine ⟨12305877991469622919740833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8203918660979748613160555 12305877991469622919740833)
        ·
          refine ⟨9229408493602217189805625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12305877991469622919740833 9229408493602217189805625)
          ·
            refine ⟨6922056370201662892354219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9229408493602217189805625 6922056370201662892354219)
            ·
              refine ⟨10383084555302494338531329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6922056370201662892354219 10383084555302494338531329)
              ·
                refine ⟨7787313416476870753898497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10383084555302494338531329 7787313416476870753898497)
                ·
                  refine ⟨5840485062357653065423873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7787313416476870753898497 5840485062357653065423873)
                  ·
                    refine ⟨4380363796768239799067905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5840485062357653065423873 4380363796768239799067905)
                    ·
                      refine ⟨3285272847576179849300929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4380363796768239799067905 3285272847576179849300929)
                      ·
                        rfl

theorem cell23_6398046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_6398046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398046 prefixEnd_6398046 := by exact prefixLift 6398046
  have htrace : WordTrace (prefixWord ++ tailWord_6398046) baseStart_6398046 baseEnd_6398046 := by
    simpa [prefixWord, tailWord_6398046, baseEnd_6398046] using wordTrace_append hprefix tailTrace_6398046
  have hstable : (prefixWord ++ tailWord_6398046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398046).length < 2 ^ (prefixWord ++ tailWord_6398046).sum := by decide
  have hdescent : baseEnd_6398046 < baseStart_6398046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398051 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 2, 4, 2]
def baseStart_6398051 : Nat := 118140960795 + 6398051 * 2 ^ 59
def prefixEnd_6398051 : Nat := 4983230072969 + 3 ^ 40 * 6398051 * 2
def baseEnd_6398051 : Nat := 3285275414979452329738405

theorem tailTrace_6398051 : CollatzResearch.WordTrace tailWord_6398051 prefixEnd_6398051 3285275414979452329738405 := by
  unfold tailWord_6398051
  simp only [CollatzResearch.WordTrace]
  refine ⟨233356090943961401961610007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155570727295974267974406671 233356090943961401961610007)
  ·
    refine ⟨350034136415942102942415011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233356090943961401961610007 350034136415942102942415011)
    ·
      refine ⟨525051204623913154413622517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350034136415942102942415011 525051204623913154413622517)
      ·
        refine ⟨49223550433491858226277111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 525051204623913154413622517 49223550433491858226277111)
        ·
          refine ⟨73835325650237787339415667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49223550433491858226277111 73835325650237787339415667)
          ·
            refine ⟨110752988475356681009123501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73835325650237787339415667 110752988475356681009123501)
            ·
              refine ⟨41532370678258755378421313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110752988475356681009123501 41532370678258755378421313)
              ·
                refine ⟨31149278008694066533815985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41532370678258755378421313 31149278008694066533815985)
                ·
                  refine ⟨23361958506520549900361989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31149278008694066533815985 23361958506520549900361989)
                  ·
                    refine ⟨4380367219972603106317873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23361958506520549900361989 4380367219972603106317873)
                    ·
                      refine ⟨3285275414979452329738405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4380367219972603106317873 3285275414979452329738405)
                      ·
                        rfl

theorem cell23_6398051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_6398051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398051 prefixEnd_6398051 := by exact prefixLift 6398051
  have htrace : WordTrace (prefixWord ++ tailWord_6398051) baseStart_6398051 baseEnd_6398051 := by
    simpa [prefixWord, tailWord_6398051, baseEnd_6398051] using wordTrace_append hprefix tailTrace_6398051
  have hstable : (prefixWord ++ tailWord_6398051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398051).length < 2 ^ (prefixWord ++ tailWord_6398051).sum := by decide
  have hdescent : baseEnd_6398051 < baseStart_6398051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398125 : List Nat := [1, 5, 2, 1, 2, 3, 2, 1, 6]
def baseStart_6398125 : Nat := 118140960795 + 6398125 * 2 ^ 59
def prefixEnd_6398125 : Nat := 4983230072969 + 3 ^ 40 * 6398125 * 2
def baseEnd_6398125 : Nat := 365034823616431671134785

theorem tailTrace_6398125 : CollatzResearch.WordTrace tailWord_6398125 prefixEnd_6398125 365034823616431671134785 := by
  unfold tailWord_6398125
  simp only [CollatzResearch.WordTrace]
  refine ⟨233358789945693312599803829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155572526630462208399869219 233358789945693312599803829)
  ·
    refine ⟨21877386557408748056231609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 233358789945693312599803829 21877386557408748056231609)
    ·
      refine ⟨16408039918056561042173707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21877386557408748056231609 16408039918056561042173707)
      ·
        refine ⟨24612059877084841563260561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16408039918056561042173707 24612059877084841563260561)
        ·
          refine ⟨18459044907813631172445421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24612059877084841563260561 18459044907813631172445421)
          ·
            refine ⟨6922141840430111689667033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18459044907813631172445421 6922141840430111689667033)
            ·
              refine ⟨5191606380322583767250275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6922141840430111689667033 5191606380322583767250275)
              ·
                refine ⟨7787409570483875650875413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5191606380322583767250275 7787409570483875650875413)
                ·
                  refine ⟨365034823616431671134785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7787409570483875650875413 365034823616431671134785)
                  ·
                    rfl

theorem cell23_6398125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_6398125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398125 prefixEnd_6398125 := by exact prefixLift 6398125
  have htrace : WordTrace (prefixWord ++ tailWord_6398125) baseStart_6398125 baseEnd_6398125 := by
    simpa [prefixWord, tailWord_6398125, baseEnd_6398125] using wordTrace_append hprefix tailTrace_6398125
  have hstable : (prefixWord ++ tailWord_6398125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398125).length < 2 ^ (prefixWord ++ tailWord_6398125).sum := by decide
  have hdescent : baseEnd_6398125 < baseStart_6398125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398161 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 1, 1, 5]
def baseStart_6398161 : Nat := 118140960795 + 6398161 * 2 ^ 59
def prefixEnd_6398161 : Nat := 4983230072969 + 3 ^ 40 * 6398161 * 2
def baseEnd_6398161 : Nat := 3285331897851446899362899

theorem tailTrace_6398161 : CollatzResearch.WordTrace tailWord_6398161 prefixEnd_6398161 3285331897851446899362899 := by
  unfold tailWord_6398161
  simp only [CollatzResearch.WordTrace]
  refine ⟨233360102973562890748114337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155573401982375260498742891 233360102973562890748114337)
  ·
    refine ⟨175020077230172168061085753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233360102973562890748114337 175020077230172168061085753)
    ·
      refine ⟨131265057922629126045814315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175020077230172168061085753 131265057922629126045814315)
      ·
        refine ⟨196897586883943689068721473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131265057922629126045814315 196897586883943689068721473)
        ·
          refine ⟨147673190162957766801541105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196897586883943689068721473 147673190162957766801541105)
          ·
            refine ⟨110754892622218325101155829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147673190162957766801541105 110754892622218325101155829)
            ·
              refine ⟨10383271183332967978233359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110754892622218325101155829 10383271183332967978233359)
              ·
                refine ⟨15574906774999451967350039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10383271183332967978233359 15574906774999451967350039)
                ·
                  refine ⟨23362360162499177951025059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15574906774999451967350039 23362360162499177951025059)
                  ·
                    refine ⟨35043540243748766926537589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23362360162499177951025059 35043540243748766926537589)
                    ·
                      refine ⟨3285331897851446899362899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35043540243748766926537589 3285331897851446899362899)
                      ·
                        rfl

theorem cell23_6398161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_6398161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398161 prefixEnd_6398161 := by exact prefixLift 6398161
  have htrace : WordTrace (prefixWord ++ tailWord_6398161) baseStart_6398161 baseEnd_6398161 := by
    simpa [prefixWord, tailWord_6398161, baseEnd_6398161] using wordTrace_append hprefix tailTrace_6398161
  have hstable : (prefixWord ++ tailWord_6398161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398161).length < 2 ^ (prefixWord ++ tailWord_6398161).sum := by decide
  have hdescent : baseEnd_6398161 < baseStart_6398161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398164 : List Nat := [2, 4, 1, 16]
def baseStart_6398164 : Nat := 118140960795 + 6398164 * 2 ^ 59
def prefixEnd_6398164 : Nat := 4983230072969 + 3 ^ 40 * 6398164 * 2
def baseEnd_6398164 : Nat := 1502210076951719427355

theorem tailTrace_6398164 : CollatzResearch.WordTrace tailWord_6398164 prefixEnd_6398164 1502210076951719427355 := by
  unfold tailWord_6398164
  simp only [CollatzResearch.WordTrace]
  refine ⟨116680106196276011130236773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155573474928368014840315697 116680106196276011130236773)
  ·
    refine ⟨21877519911801752086919395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116680106196276011130236773 21877519911801752086919395)
    ·
      refine ⟨32816279867702628130379093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21877519911801752086919395 32816279867702628130379093)
      ·
        refine ⟨1502210076951719427355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 32816279867702628130379093 1502210076951719427355)
        ·
          rfl

theorem cell23_6398164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 16].length) (baseStart_6398164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398164 prefixEnd_6398164 := by exact prefixLift 6398164
  have htrace : WordTrace (prefixWord ++ tailWord_6398164) baseStart_6398164 baseEnd_6398164 := by
    simpa [prefixWord, tailWord_6398164, baseEnd_6398164] using wordTrace_append hprefix tailTrace_6398164
  have hstable : (prefixWord ++ tailWord_6398164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398164).length < 2 ^ (prefixWord ++ tailWord_6398164).sum := by decide
  have hdescent : baseEnd_6398164 < baseStart_6398164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398168 : List Nat := [2, 1, 2, 2, 4, 1, 1, 4, 2, 4]
def baseStart_6398168 : Nat := 118140960795 + 6398168 * 2 ^ 59
def prefixEnd_6398168 : Nat := 4983230072969 + 3 ^ 40 * 6398168 * 2
def baseEnd_6398168 : Nat := 1095111830738676123991789

theorem tailTrace_6398168 : CollatzResearch.WordTrace tailWord_6398168 prefixEnd_6398168 1095111830738676123991789 := by
  unfold tailWord_6398168
  simp only [CollatzResearch.WordTrace]
  refine ⟨116680179142268765471809579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155573572189691687295746105 116680179142268765471809579)
  ·
    refine ⟨175020268713403148207714369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116680179142268765471809579 175020268713403148207714369)
    ·
      refine ⟨131265201535052361155785777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175020268713403148207714369 131265201535052361155785777)
      ·
        refine ⟨98448901151289270866839333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131265201535052361155785777 98448901151289270866839333)
        ·
          refine ⟨18459168965866738287532375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98448901151289270866839333 18459168965866738287532375)
          ·
            refine ⟨27688753448800107431298563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18459168965866738287532375 27688753448800107431298563)
            ·
              refine ⟨41533130173200161146947845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27688753448800107431298563 41533130173200161146947845)
              ·
                refine ⟨7787461907475030215052721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41533130173200161146947845 7787461907475030215052721)
                ·
                  refine ⟨5840596430606272661289541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7787461907475030215052721 5840596430606272661289541)
                  ·
                    refine ⟨1095111830738676123991789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5840596430606272661289541 1095111830738676123991789)
                    ·
                      rfl

theorem cell23_6398168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_6398168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398168 prefixEnd_6398168 := by exact prefixLift 6398168
  have htrace : WordTrace (prefixWord ++ tailWord_6398168) baseStart_6398168 baseEnd_6398168 := by
    simpa [prefixWord, tailWord_6398168, baseEnd_6398168] using wordTrace_append hprefix tailTrace_6398168
  have hstable : (prefixWord ++ tailWord_6398168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398168).length < 2 ^ (prefixWord ++ tailWord_6398168).sum := by decide
  have hdescent : baseEnd_6398168 < baseStart_6398168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398181 : List Nat := [1, 3, 1, 4, 2, 1, 3, 8]
def baseStart_6398181 : Nat := 118140960795 + 6398181 * 2 ^ 59
def prefixEnd_6398181 : Nat := 4983230072969 + 3 ^ 40 * 6398181 * 2
def baseEnd_6398181 : Nat := 121679339535723585967141

theorem tailTrace_6398181 : CollatzResearch.WordTrace tailWord_6398181 prefixEnd_6398181 121679339535723585967141 := by
  unfold tailWord_6398181
  simp only [CollatzResearch.WordTrace]
  refine ⟨233360832433490434163842397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155573888288993622775894931 233360832433490434163842397)
  ·
    refine ⟨87510312162558912811440899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233360832433490434163842397 87510312162558912811440899)
    ·
      refine ⟨131265468243838369217161349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87510312162558912811440899 131265468243838369217161349)
      ·
        refine ⟨24612275295719694228217753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131265468243838369217161349 24612275295719694228217753)
        ·
          refine ⟨18459206471789770671163315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24612275295719694228217753 18459206471789770671163315)
          ·
            refine ⟨27688809707684656006744973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18459206471789770671163315 27688809707684656006744973)
            ·
              refine ⟨10383303640381746002529365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27688809707684656006744973 10383303640381746002529365)
              ·
                refine ⟨121679339535723585967141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10383303640381746002529365 121679339535723585967141)
                ·
                  rfl

theorem cell23_6398181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 8].length) (baseStart_6398181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398181 prefixEnd_6398181 := by exact prefixLift 6398181
  have htrace : WordTrace (prefixWord ++ tailWord_6398181) baseStart_6398181 baseEnd_6398181 := by
    simpa [prefixWord, tailWord_6398181, baseEnd_6398181] using wordTrace_append hprefix tailTrace_6398181
  have hstable : (prefixWord ++ tailWord_6398181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398181).length < 2 ^ (prefixWord ++ tailWord_6398181).sum := by decide
  have hdescent : baseEnd_6398181 < baseStart_6398181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398224 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 2, 12]
def baseStart_6398224 : Nat := 118140960795 + 6398224 * 2 ^ 59
def prefixEnd_6398224 : Nat := 4983230072969 + 3 ^ 40 * 6398224 * 2
def baseEnd_6398224 : Nat := 1095121415710893384291703

theorem tailTrace_6398224 : CollatzResearch.WordTrace tailWord_6398224 prefixEnd_6398224 1095121415710893384291703 := by
  unfold tailWord_6398224
  simp only [CollatzResearch.WordTrace]
  refine ⟨116681200386167326253828863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155574933848223101671771817 116681200386167326253828863)
  ·
    refine ⟨175021800579250989380743295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116681200386167326253828863 175021800579250989380743295)
    ·
      refine ⟨262532700868876484071114943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175021800579250989380743295 262532700868876484071114943)
      ·
        refine ⟨393799051303314726106672415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262532700868876484071114943 393799051303314726106672415)
        ·
          refine ⟨590698576954972089160008623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393799051303314726106672415 590698576954972089160008623)
          ·
            refine ⟨886047865432458133740012935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590698576954972089160008623 886047865432458133740012935)
            ·
              refine ⟨1329071798148687200610019403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886047865432458133740012935 1329071798148687200610019403)
              ·
                refine ⟨1993607697223030800915029105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1329071798148687200610019403 1993607697223030800915029105)
                ·
                  refine ⟨1495205772917273100686271829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1993607697223030800915029105 1495205772917273100686271829)
                  ·
                    refine ⟨1095121415710893384291703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1495205772917273100686271829 1095121415710893384291703)
                    ·
                      rfl

theorem cell23_6398224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 12].length) (baseStart_6398224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398224 prefixEnd_6398224 := by exact prefixLift 6398224
  have htrace : WordTrace (prefixWord ++ tailWord_6398224) baseStart_6398224 baseEnd_6398224 := by
    simpa [prefixWord, tailWord_6398224, baseEnd_6398224] using wordTrace_append hprefix tailTrace_6398224
  have hstable : (prefixWord ++ tailWord_6398224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398224).length < 2 ^ (prefixWord ++ tailWord_6398224).sum := by decide
  have hdescent : baseEnd_6398224 < baseStart_6398224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398225 : List Nat := [1, 2, 2, 1, 1, 5, 3, 2, 2, 1, 3]
def baseStart_6398225 : Nat := 118140960795 + 6398225 * 2 ^ 59
def prefixEnd_6398225 : Nat := 4983230072969 + 3 ^ 40 * 6398225 * 2
def baseEnd_6398225 : Nat := 3285364760613334648962605

theorem tailTrace_6398225 : CollatzResearch.WordTrace tailWord_6398225 prefixEnd_6398225 3285364760613334648962605 := by
  unfold tailWord_6398225
  simp only [CollatzResearch.WordTrace]
  refine ⟨233362437245331029678444129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155574958163554019785629419 233362437245331029678444129)
  ·
    refine ⟨175021827933998272258833097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233362437245331029678444129 175021827933998272258833097)
    ·
      refine ⟨131266370950498704194124823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175021827933998272258833097 131266370950498704194124823)
      ·
        refine ⟨196899556425748056291187235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131266370950498704194124823 196899556425748056291187235)
        ·
          refine ⟨295349334638622084436780853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196899556425748056291187235 295349334638622084436780853)
          ·
            refine ⟨27689000122370820415948205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 295349334638622084436780853 27689000122370820415948205)
            ·
              refine ⟨10383375045889057655980577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27689000122370820415948205 10383375045889057655980577)
              ·
                refine ⟨7787531284416793241985433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10383375045889057655980577 7787531284416793241985433)
                ·
                  refine ⟨5840648463312594931489075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7787531284416793241985433 5840648463312594931489075)
                  ·
                    refine ⟨8760972694968892397233613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5840648463312594931489075 8760972694968892397233613)
                    ·
                      refine ⟨3285364760613334648962605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8760972694968892397233613 3285364760613334648962605)
                      ·
                        rfl

theorem cell23_6398225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 1, 3].length) (baseStart_6398225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398225 prefixEnd_6398225 := by exact prefixLift 6398225
  have htrace : WordTrace (prefixWord ++ tailWord_6398225) baseStart_6398225 baseEnd_6398225 := by
    simpa [prefixWord, tailWord_6398225, baseEnd_6398225] using wordTrace_append hprefix tailTrace_6398225
  have hstable : (prefixWord ++ tailWord_6398225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398225).length < 2 ^ (prefixWord ++ tailWord_6398225).sum := by decide
  have hdescent : baseEnd_6398225 < baseStart_6398225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398241 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 2, 6]
def baseStart_6398241 : Nat := 118140960795 + 6398241 * 2 ^ 59
def prefixEnd_6398241 : Nat := 4983230072969 + 3 ^ 40 * 6398241 * 2
def baseEnd_6398241 : Nat := 1095124325434602195454177

theorem tailTrace_6398241 : CollatzResearch.WordTrace tailWord_6398241 prefixEnd_6398241 1095124325434602195454177 := by
  unfold tailWord_6398241
  simp only [CollatzResearch.WordTrace]
  refine ⟨233363020813273064411026577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155575347208848709607351051 233363020813273064411026577)
  ·
    refine ⟨175022265609954798308269933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233363020813273064411026577 175022265609954798308269933)
    ·
      refine ⟨65633349603733049365601225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175022265609954798308269933 65633349603733049365601225)
      ·
        refine ⟨49225012202799787024200919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65633349603733049365601225 49225012202799787024200919)
        ·
          refine ⟨73837518304199680536301379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49225012202799787024200919 73837518304199680536301379)
          ·
            refine ⟨110756277456299520804452069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73837518304199680536301379 110756277456299520804452069)
            ·
              refine ⟨20766802023056160150834763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110756277456299520804452069 20766802023056160150834763)
              ·
                refine ⟨31150203034584240226252145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20766802023056160150834763 31150203034584240226252145)
                ·
                  refine ⟨23362652275938180169689109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31150203034584240226252145 23362652275938180169689109)
                  ·
                    refine ⟨1095124325434602195454177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23362652275938180169689109 1095124325434602195454177)
                    ·
                      rfl

theorem cell23_6398241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_6398241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398241 prefixEnd_6398241 := by exact prefixLift 6398241
  have htrace : WordTrace (prefixWord ++ tailWord_6398241) baseStart_6398241 baseEnd_6398241 := by
    simpa [prefixWord, tailWord_6398241, baseEnd_6398241] using wordTrace_append hprefix tailTrace_6398241
  have hstable : (prefixWord ++ tailWord_6398241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398241).length < 2 ^ (prefixWord ++ tailWord_6398241).sum := by decide
  have hdescent : baseEnd_6398241 < baseStart_6398241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398288 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 7]
def baseStart_6398288 : Nat := 118140960795 + 6398288 * 2 ^ 59
def prefixEnd_6398288 : Nat := 4983230072969 + 3 ^ 40 * 6398288 * 2
def baseEnd_6398288 : Nat := 365044123321618655830535

theorem tailTrace_6398288 : CollatzResearch.WordTrace tailWord_6398288 prefixEnd_6398288 365044123321618655830535 := by
  unfold tailWord_6398288
  simp only [CollatzResearch.WordTrace]
  refine ⟨116682367522051395718993759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155576490029401860958658345 116682367522051395718993759)
  ·
    refine ⟨175023551283077093578490639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116682367522051395718993759 175023551283077093578490639)
    ·
      refine ⟨262535326924615640367735959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175023551283077093578490639 262535326924615640367735959)
      ·
        refine ⟨393802990386923460551603939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262535326924615640367735959 393802990386923460551603939)
        ·
          refine ⟨590704485580385190827405909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393802990386923460551603939 590704485580385190827405909)
          ·
            refine ⟨6922318190395138955008663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 590704485580385190827405909 6922318190395138955008663)
            ·
              refine ⟨10383477285592708432512995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6922318190395138955008663 10383477285592708432512995)
              ·
                refine ⟨15575215928389062648769493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10383477285592708432512995 15575215928389062648769493)
                ·
                  refine ⟨365044123321618655830535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15575215928389062648769493 365044123321618655830535)
                  ·
                    rfl

theorem cell23_6398288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 7].length) (baseStart_6398288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398288 prefixEnd_6398288 := by exact prefixLift 6398288
  have htrace : WordTrace (prefixWord ++ tailWord_6398288) baseStart_6398288 baseEnd_6398288 := by
    simpa [prefixWord, tailWord_6398288, baseEnd_6398288] using wordTrace_append hprefix tailTrace_6398288
  have hstable : (prefixWord ++ tailWord_6398288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398288).length < 2 ^ (prefixWord ++ tailWord_6398288).sum := by decide
  have hdescent : baseEnd_6398288 < baseStart_6398288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398339 : List Nat := [1, 1, 1, 3, 7, 1, 2, 2, 5]
def baseStart_6398339 : Nat := 118140960795 + 6398339 * 2 ^ 59
def prefixEnd_6398339 : Nat := 4983230072969 + 3 ^ 40 * 6398339 * 2
def baseEnd_6398339 : Nat := 365047033045327466993009

theorem tailTrace_6398339 : CollatzResearch.WordTrace tailWord_6398339 prefixEnd_6398339 365047033045327466993009 := by
  unfold tailWord_6398339
  simp only [CollatzResearch.WordTrace]
  refine ⟨233366595166918027148094071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155577730111278684765396047 233366595166918027148094071)
  ·
    refine ⟨350049892750377040722141107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233366595166918027148094071 350049892750377040722141107)
    ·
      refine ⟨525074839125565561083211661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350049892750377040722141107 525074839125565561083211661)
      ·
        refine ⟨196903064672087085406204373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 525074839125565561083211661 196903064672087085406204373)
        ·
          refine ⟨4614915578252041064207915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 196903064672087085406204373 4614915578252041064207915)
          ·
            refine ⟨6922373367378061596311873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4614915578252041064207915 6922373367378061596311873)
            ·
              refine ⟨5191780025533546197233905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6922373367378061596311873 5191780025533546197233905)
              ·
                refine ⟨3893835019150159647925429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5191780025533546197233905 3893835019150159647925429)
                ·
                  refine ⟨365047033045327466993009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3893835019150159647925429 365047033045327466993009)
                  ·
                    rfl

theorem cell23_6398339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 5].length) (baseStart_6398339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398339 prefixEnd_6398339 := by exact prefixLift 6398339
  have htrace : WordTrace (prefixWord ++ tailWord_6398339) baseStart_6398339 baseEnd_6398339 := by
    simpa [prefixWord, tailWord_6398339, baseEnd_6398339] using wordTrace_append hprefix tailTrace_6398339
  have hstable : (prefixWord ++ tailWord_6398339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398339).length < 2 ^ (prefixWord ++ tailWord_6398339).sum := by decide
  have hdescent : baseEnd_6398339 < baseStart_6398339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398341 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 1, 5, 5]
def baseStart_6398341 : Nat := 118140960795 + 6398341 * 2 ^ 59
def prefixEnd_6398341 : Nat := 4983230072969 + 3 ^ 40 * 6398341 * 2
def baseEnd_6398341 : Nat := 3285424324369256195112071

theorem tailTrace_6398341 : CollatzResearch.WordTrace tailWord_6398341 prefixEnd_6398341 3285424324369256195112071 := by
  unfold tailWord_6398341
  simp only [CollatzResearch.WordTrace]
  refine ⟨233366668112910781489666877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155577778741940520993111251 233366668112910781489666877)
  ·
    refine ⟨87512500542341543058625079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233366668112910781489666877 87512500542341543058625079)
    ·
      refine ⟨131268750813512314587937619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87512500542341543058625079 131268750813512314587937619)
      ·
        refine ⟨196903126220268471881906429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131268750813512314587937619 196903126220268471881906429)
        ·
          refine ⟨73838672332600676955714911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196903126220268471881906429 73838672332600676955714911)
          ·
            refine ⟨110758008498901015433572367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73838672332600676955714911 110758008498901015433572367)
            ·
              refine ⟨166137012748351523150358551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110758008498901015433572367 166137012748351523150358551)
              ·
                refine ⟨249205519122527284725537827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166137012748351523150358551 249205519122527284725537827)
                ·
                  refine ⟨373808278683790927088306741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249205519122527284725537827 373808278683790927088306741)
                  ·
                    refine ⟨35044526126605399414528757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 373808278683790927088306741 35044526126605399414528757)
                    ·
                      refine ⟨3285424324369256195112071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35044526126605399414528757 3285424324369256195112071)
                      ·
                        rfl

theorem cell23_6398341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_6398341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398341 prefixEnd_6398341 := by exact prefixLift 6398341
  have htrace : WordTrace (prefixWord ++ tailWord_6398341) baseStart_6398341 baseEnd_6398341 := by
    simpa [prefixWord, tailWord_6398341, baseEnd_6398341] using wordTrace_append hprefix tailTrace_6398341
  have hstable : (prefixWord ++ tailWord_6398341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398341).length < 2 ^ (prefixWord ++ tailWord_6398341).sum := by decide
  have hdescent : baseEnd_6398341 < baseStart_6398341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398369 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 2, 5]
def baseStart_6398369 : Nat := 118140960795 + 6398369 * 2 ^ 59
def prefixEnd_6398369 : Nat := 4983230072969 + 3 ^ 40 * 6398369 * 2
def baseEnd_6398369 : Nat := 1095146233942527361853981

theorem tailTrace_6398369 : CollatzResearch.WordTrace tailWord_6398369 prefixEnd_6398369 1095146233942527361853981 := by
  unfold tailWord_6398369
  simp only [CollatzResearch.WordTrace]
  refine ⟨233367689356809342271686161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155578459571206228181124107 233367689356809342271686161)
  ·
    refine ⟨175025767017607006703764621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233367689356809342271686161 175025767017607006703764621)
    ·
      refine ⟨65634662631602627513911733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175025767017607006703764621 65634662631602627513911733)
      ·
        refine ⟨6153249621712746329429225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65634662631602627513911733 6153249621712746329429225)
        ·
          refine ⟨4614937216284559747071919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6153249621712746329429225 4614937216284559747071919)
          ·
            refine ⟨6922405824426839620607879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4614937216284559747071919 6922405824426839620607879)
            ·
              refine ⟨10383608736640259430911819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6922405824426839620607879 10383608736640259430911819)
              ·
                refine ⟨15575413104960389146367729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10383608736640259430911819 15575413104960389146367729)
                ·
                  refine ⟨11681559828720291859775797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15575413104960389146367729 11681559828720291859775797)
                  ·
                    refine ⟨1095146233942527361853981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11681559828720291859775797 1095146233942527361853981)
                    ·
                      rfl

theorem cell23_6398369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_6398369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398369 prefixEnd_6398369 := by exact prefixLift 6398369
  have htrace : WordTrace (prefixWord ++ tailWord_6398369) baseStart_6398369 baseEnd_6398369 := by
    simpa [prefixWord, tailWord_6398369, baseEnd_6398369] using wordTrace_append hprefix tailTrace_6398369
  have hstable : (prefixWord ++ tailWord_6398369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398369).length < 2 ^ (prefixWord ++ tailWord_6398369).sum := by decide
  have hdescent : baseEnd_6398369 < baseStart_6398369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398375 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_6398375 : Nat := 118140960795 + 6398375 * 2 ^ 59
def prefixEnd_6398375 : Nat := 4983230072969 + 3 ^ 40 * 6398375 * 2
def baseEnd_6398375 : Nat := 3285441782711509062086915

theorem tailTrace_6398375 : CollatzResearch.WordTrace tailWord_6398375 prefixEnd_6398375 3285441782711509062086915 := by
  unfold tailWord_6398375
  simp only [CollatzResearch.WordTrace]
  refine ⟨233367908194787605296404579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155578605463191736864269719 233367908194787605296404579)
  ·
    refine ⟨350051862292181407944606869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233367908194787605296404579 350051862292181407944606869)
    ·
      refine ⟨16408681044946003497403447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 350051862292181407944606869 16408681044946003497403447)
      ·
        refine ⟨24613021567419005246105171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16408681044946003497403447 24613021567419005246105171)
        ·
          refine ⟨36919532351128507869157757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24613021567419005246105171 36919532351128507869157757)
          ·
            refine ⟨13844824631673190450934159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36919532351128507869157757 13844824631673190450934159)
            ·
              refine ⟨20767236947509785676401239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13844824631673190450934159 20767236947509785676401239)
              ·
                refine ⟨31150855421264678514601859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20767236947509785676401239 31150855421264678514601859)
                ·
                  refine ⟨46726283131897017771902789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31150855421264678514601859 46726283131897017771902789)
                  ·
                    refine ⟨8761178087230690832231773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46726283131897017771902789 8761178087230690832231773)
                    ·
                      refine ⟨3285441782711509062086915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8761178087230690832231773 3285441782711509062086915)
                      ·
                        rfl

theorem cell23_6398375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_6398375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398375 prefixEnd_6398375 := by exact prefixLift 6398375
  have htrace : WordTrace (prefixWord ++ tailWord_6398375) baseStart_6398375 baseEnd_6398375 := by
    simpa [prefixWord, tailWord_6398375, baseEnd_6398375] using wordTrace_append hprefix tailTrace_6398375
  have hstable : (prefixWord ++ tailWord_6398375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398375).length < 2 ^ (prefixWord ++ tailWord_6398375).sum := by decide
  have hdescent : baseEnd_6398375 < baseStart_6398375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398398 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_6398398 : Nat := 118140960795 + 6398398 * 2 ^ 59
def prefixEnd_6398398 : Nat := 4983230072969 + 3 ^ 40 * 6398398 * 2
def baseEnd_6398398 : Nat := 3285453592766562472099309

theorem tailTrace_6398398 : CollatzResearch.WordTrace tailWord_6398398 prefixEnd_6398398 3285453592766562472099309 := by
  unfold tailWord_6398398
  simp only [CollatzResearch.WordTrace]
  refine ⟨29171093384213035028061481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155579164715802853482994565 29171093384213035028061481)
  ·
    refine ⟨21878320038159776271046111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29171093384213035028061481 21878320038159776271046111)
    ·
      refine ⟨32817480057239664406569167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21878320038159776271046111 32817480057239664406569167)
      ·
        refine ⟨49226220085859496609853751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32817480057239664406569167 49226220085859496609853751)
        ·
          refine ⟨73839330128789244914780627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49226220085859496609853751 73839330128789244914780627)
          ·
            refine ⟨110758995193183867372170941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73839330128789244914780627 110758995193183867372170941)
            ·
              refine ⟨41534623197443950264564103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110758995193183867372170941 41534623197443950264564103)
              ·
                refine ⟨62301934796165925396846155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41534623197443950264564103 62301934796165925396846155)
                ·
                  refine ⟨93452902194248888095269233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62301934796165925396846155 93452902194248888095269233)
                  ·
                    refine ⟨70089676645686666071451925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93452902194248888095269233 70089676645686666071451925)
                    ·
                      refine ⟨3285453592766562472099309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70089676645686666071451925 3285453592766562472099309)
                      ·
                        rfl

theorem cell23_6398398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_6398398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398398 prefixEnd_6398398 := by exact prefixLift 6398398
  have htrace : WordTrace (prefixWord ++ tailWord_6398398) baseStart_6398398 baseEnd_6398398 := by
    simpa [prefixWord, tailWord_6398398, baseEnd_6398398] using wordTrace_append hprefix tailTrace_6398398
  have hstable : (prefixWord ++ tailWord_6398398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398398).length < 2 ^ (prefixWord ++ tailWord_6398398).sum := by decide
  have hdescent : baseEnd_6398398 < baseStart_6398398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398412 : List Nat := [2, 2, 1, 4, 3, 1, 3, 1, 6]
def baseStart_6398412 : Nat := 118140960795 + 6398412 * 2 ^ 59
def prefixEnd_6398412 : Nat := 4983230072969 + 3 ^ 40 * 6398412 * 2
def baseEnd_6398412 : Nat := 365051197943969490813805

theorem tailTrace_6398412 : CollatzResearch.WordTrace tailWord_6398412 prefixEnd_6398412 365051197943969490813805 := by
  unfold tailWord_6398412
  simp only [CollatzResearch.WordTrace]
  refine ⟨116684628847826780307750745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155579505130435707077000993 116684628847826780307750745)
  ·
    refine ⟨87513471635870085230813059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116684628847826780307750745 87513471635870085230813059)
    ·
      refine ⟨131270207453805127846219589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87513471635870085230813059 131270207453805127846219589)
      ·
        refine ⟨24613163897588461471166173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131270207453805127846219589 24613163897588461471166173)
        ·
          refine ⟨9229936461595673051687315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24613163897588461471166173 9229936461595673051687315)
          ·
            refine ⟨13844904692393509577530973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9229936461595673051687315 13844904692393509577530973)
            ·
              refine ⟨5191839259647566091574115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13844904692393509577530973 5191839259647566091574115)
              ·
                refine ⟨7787758889471349137361173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5191839259647566091574115 7787758889471349137361173)
                ·
                  refine ⟨365051197943969490813805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7787758889471349137361173 365051197943969490813805)
                  ·
                    rfl

theorem cell23_6398412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 6].length) (baseStart_6398412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398412 prefixEnd_6398412 := by exact prefixLift 6398412
  have htrace : WordTrace (prefixWord ++ tailWord_6398412) baseStart_6398412 baseEnd_6398412 := by
    simpa [prefixWord, tailWord_6398412, baseEnd_6398412] using wordTrace_append hprefix tailTrace_6398412
  have hstable : (prefixWord ++ tailWord_6398412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398412).length < 2 ^ (prefixWord ++ tailWord_6398412).sum := by decide
  have hdescent : baseEnd_6398412 < baseStart_6398412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398425 : List Nat := [1, 2, 1, 2, 4, 1, 4, 2, 1, 5]
def baseStart_6398425 : Nat := 118140960795 + 6398425 * 2 ^ 59
def prefixEnd_6398425 : Nat := 4983230072969 + 3 ^ 40 * 6398425 * 2
def baseEnd_6398425 : Nat := 1095155818914744622153895

theorem tailTrace_6398425 : CollatzResearch.WordTrace tailWord_6398425 prefixEnd_6398425 1095155818914744622153895 := by
  unfold tailWord_6398425
  simp only [CollatzResearch.WordTrace]
  refine ⟨233369731844606463835724729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155579821229737642557149819 233369731844606463835724729)
  ·
    refine ⟨175027298883454847876793547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233369731844606463835724729 175027298883454847876793547)
    ·
      refine ⟨262540948325182271815190321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175027298883454847876793547 262540948325182271815190321)
      ·
        refine ⟨196905711243886703861392741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262540948325182271815190321 196905711243886703861392741)
        ·
          refine ⟨36919820858228756974011139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196905711243886703861392741 36919820858228756974011139)
          ·
            refine ⟨55379731287343135461016709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36919820858228756974011139 55379731287343135461016709)
            ·
              refine ⟨10383699616376837898940633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55379731287343135461016709 10383699616376837898940633)
              ·
                refine ⟨7787774712282628424205475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10383699616376837898940633 7787774712282628424205475)
                ·
                  refine ⟨11681662068423942636308213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7787774712282628424205475 11681662068423942636308213)
                  ·
                    refine ⟨1095155818914744622153895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11681662068423942636308213 1095155818914744622153895)
                    ·
                      rfl

theorem cell23_6398425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 5].length) (baseStart_6398425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398425 prefixEnd_6398425 := by exact prefixLift 6398425
  have htrace : WordTrace (prefixWord ++ tailWord_6398425) baseStart_6398425 baseEnd_6398425 := by
    simpa [prefixWord, tailWord_6398425, baseEnd_6398425] using wordTrace_append hprefix tailTrace_6398425
  have hstable : (prefixWord ++ tailWord_6398425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398425).length < 2 ^ (prefixWord ++ tailWord_6398425).sum := by decide
  have hdescent : baseEnd_6398425 < baseStart_6398425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398458 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4]
def baseStart_6398458 : Nat := 118140960795 + 6398458 * 2 ^ 59
def prefixEnd_6398458 : Nat := 4983230072969 + 3 ^ 40 * 6398458 * 2
def baseEnd_6398458 : Nat := 3285484401605832237349033

theorem tailTrace_6398458 : CollatzResearch.WordTrace tailWord_6398458 prefixEnd_6398458 3285484401605832237349033 := by
  unfold tailWord_6398458
  simp only [CollatzResearch.WordTrace]
  refine ⟨58342733863371727617919007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155580623635657940314450685 58342733863371727617919007)
  ·
    refine ⟨87514100795057591426878511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58342733863371727617919007 87514100795057591426878511)
    ·
      refine ⟨131271151192586387140317767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87514100795057591426878511 131271151192586387140317767)
      ·
        refine ⟨196906726788879580710476651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131271151192586387140317767 196906726788879580710476651)
        ·
          refine ⟨295360090183319371065714977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196906726788879580710476651 295360090183319371065714977)
          ·
            refine ⟨221520067637489528299286233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295360090183319371065714977 221520067637489528299286233)
            ·
              refine ⟨166140050728117146224464675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221520067637489528299286233 166140050728117146224464675)
              ·
                refine ⟨249210076092175719336697013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166140050728117146224464675 249210076092175719336697013)
                ·
                  refine ⟨23363444633641473687815345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 249210076092175719336697013 23363444633641473687815345)
                  ·
                    refine ⟨17522583475231105265861509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23363444633641473687815345 17522583475231105265861509)
                    ·
                      refine ⟨3285484401605832237349033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17522583475231105265861509 3285484401605832237349033)
                      ·
                        rfl

theorem cell23_6398458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_6398458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398458 prefixEnd_6398458 := by exact prefixLift 6398458
  have htrace : WordTrace (prefixWord ++ tailWord_6398458) baseStart_6398458 baseEnd_6398458 := by
    simpa [prefixWord, tailWord_6398458, baseEnd_6398458] using wordTrace_append hprefix tailTrace_6398458
  have hstable : (prefixWord ++ tailWord_6398458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398458).length < 2 ^ (prefixWord ++ tailWord_6398458).sum := by decide
  have hdescent : baseEnd_6398458 < baseStart_6398458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398465 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_6398465 : Nat := 118140960795 + 6398465 * 2 ^ 59
def prefixEnd_6398465 : Nat := 4983230072969 + 3 ^ 40 * 6398465 * 2
def baseEnd_6398465 : Nat := 3285487995970413709961501

theorem tailTrace_6398465 : CollatzResearch.WordTrace tailWord_6398465 prefixEnd_6398465 3285487995970413709961501 := by
  unfold tailWord_6398465
  simp only [CollatzResearch.WordTrace]
  refine ⟨233371190764461550667180849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155580793842974367111453899 233371190764461550667180849)
  ·
    refine ⟨175028393073346163000385637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233371190764461550667180849 175028393073346163000385637)
    ·
      refine ⟨32817823701252405562572307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175028393073346163000385637 32817823701252405562572307)
      ·
        refine ⟨49226735551878608343858461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32817823701252405562572307 49226735551878608343858461)
        ·
          refine ⟨18460025831954478128946923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49226735551878608343858461 18460025831954478128946923)
          ·
            refine ⟨27690038747931717193420385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18460025831954478128946923 27690038747931717193420385)
            ·
              refine ⟨20767529060948787895065289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27690038747931717193420385 20767529060948787895065289)
              ·
                refine ⟨15575646795711590921298967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20767529060948787895065289 15575646795711590921298967)
                ·
                  refine ⟨23363470193567386381948451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15575646795711590921298967 23363470193567386381948451)
                  ·
                    refine ⟨35045205290351079572922677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23363470193567386381948451 35045205290351079572922677)
                    ·
                      refine ⟨3285487995970413709961501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35045205290351079572922677 3285487995970413709961501)
                      ·
                        rfl

theorem cell23_6398465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_6398465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398465 prefixEnd_6398465 := by exact prefixLift 6398465
  have htrace : WordTrace (prefixWord ++ tailWord_6398465) baseStart_6398465 baseEnd_6398465 := by
    simpa [prefixWord, tailWord_6398465, baseEnd_6398465] using wordTrace_append hprefix tailTrace_6398465
  have hstable : (prefixWord ++ tailWord_6398465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398465).length < 2 ^ (prefixWord ++ tailWord_6398465).sum := by decide
  have hdescent : baseEnd_6398465 < baseStart_6398465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398499 : List Nat := [1, 1, 1, 4, 4, 2, 3, 1, 1, 2, 3]
def baseStart_6398499 : Nat := 118140960795 + 6398499 * 2 ^ 59
def prefixEnd_6398499 : Nat := 4983230072969 + 3 ^ 40 * 6398499 * 2
def baseEnd_6398499 : Nat := 3285505454312666576936345

theorem tailTrace_6398499 : CollatzResearch.WordTrace tailWord_6398499 prefixEnd_6398499 3285505454312666576936345 := by
  unfold tailWord_6398499
  simp only [CollatzResearch.WordTrace]
  refine ⟨233372430846338374473918551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155581620564225582982612367 233372430846338374473918551)
  ·
    refine ⟨350058646269507561710877827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233372430846338374473918551 350058646269507561710877827)
    ·
      refine ⟨525087969404261342566316741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350058646269507561710877827 525087969404261342566316741)
      ·
        refine ⟨98453994263299001731184389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 525087969404261342566316741 98453994263299001731184389)
        ·
          refine ⟨18460123924368562824597073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98453994263299001731184389 18460123924368562824597073)
          ·
            refine ⟨13845092943276422118447805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18460123924368562824597073 13845092943276422118447805)
            ·
              refine ⟨5191909853728658294417927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13845092943276422118447805 5191909853728658294417927)
              ·
                refine ⟨7787864780592987441626891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5191909853728658294417927 7787864780592987441626891)
                ·
                  refine ⟨11681797170889481162440337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7787864780592987441626891 11681797170889481162440337)
                  ·
                    refine ⟨8761347878167110871830253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11681797170889481162440337 8761347878167110871830253)
                    ·
                      refine ⟨3285505454312666576936345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8761347878167110871830253 3285505454312666576936345)
                      ·
                        rfl

theorem cell23_6398499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_6398499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398499 prefixEnd_6398499 := by exact prefixLift 6398499
  have htrace : WordTrace (prefixWord ++ tailWord_6398499) baseStart_6398499 baseEnd_6398499 := by
    simpa [prefixWord, tailWord_6398499, baseEnd_6398499] using wordTrace_append hprefix tailTrace_6398499
  have hstable : (prefixWord ++ tailWord_6398499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398499).length < 2 ^ (prefixWord ++ tailWord_6398499).sum := by decide
  have hdescent : baseEnd_6398499 < baseStart_6398499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398508 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 5]
def baseStart_6398508 : Nat := 118140960795 + 6398508 * 2 ^ 59
def prefixEnd_6398508 : Nat := 4983230072969 + 3 ^ 40 * 6398508 * 2
def baseEnd_6398508 : Nat := 3285510075638557041723803

theorem tailTrace_6398508 : CollatzResearch.WordTrace tailWord_6398508 prefixEnd_6398508 3285510075638557041723803 := by
  unfold tailWord_6398508
  simp only [CollatzResearch.WordTrace]
  refine ⟨116686379551652884505498089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155581839402203846007330785 116686379551652884505498089)
  ·
    refine ⟨87514784663739663379123567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116686379551652884505498089 87514784663739663379123567)
    ·
      refine ⟨131272176995609495068685351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87514784663739663379123567 131272176995609495068685351)
      ·
        refine ⟨196908265493414242603028027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131272176995609495068685351 196908265493414242603028027)
        ·
          refine ⟨295362398240121363904542041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196908265493414242603028027 295362398240121363904542041)
          ·
            refine ⟨221521798680091022928406531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295362398240121363904542041 221521798680091022928406531)
            ·
              refine ⟨332282698020136534392609797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221521798680091022928406531 332282698020136534392609797)
              ·
                refine ⟨62303005878775600198614337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 332282698020136534392609797 62303005878775600198614337)
                ·
                  refine ⟨46727254409081700148960753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62303005878775600198614337 46727254409081700148960753)
                  ·
                    refine ⟨35045440806811275111720565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46727254409081700148960753 35045440806811275111720565)
                    ·
                      refine ⟨3285510075638557041723803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35045440806811275111720565 3285510075638557041723803)
                      ·
                        rfl

theorem cell23_6398508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_6398508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398508 prefixEnd_6398508 := by exact prefixLift 6398508
  have htrace : WordTrace (prefixWord ++ tailWord_6398508) baseStart_6398508 baseEnd_6398508 := by
    simpa [prefixWord, tailWord_6398508, baseEnd_6398508] using wordTrace_append hprefix tailTrace_6398508
  have hstable : (prefixWord ++ tailWord_6398508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398508).length < 2 ^ (prefixWord ++ tailWord_6398508).sum := by decide
  have hdescent : baseEnd_6398508 < baseStart_6398508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398512 : List Nat := [2, 1, 1, 1, 2, 3, 3, 4, 2, 1, 3]
def baseStart_6398512 : Nat := 118140960795 + 6398512 * 2 ^ 59
def prefixEnd_6398512 : Nat := 4983230072969 + 3 ^ 40 * 6398512 * 2
def baseEnd_6398512 : Nat := 3285512129561175026073785

theorem tailTrace_6398512 : CollatzResearch.WordTrace tailWord_6398512 prefixEnd_6398512 3285512129561175026073785 := by
  unfold tailWord_6398512
  simp only [CollatzResearch.WordTrace]
  refine ⟨116686452497645638847070895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155581936663527518462761193 116686452497645638847070895)
  ·
    refine ⟨175029678746468458270606343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116686452497645638847070895 175029678746468458270606343)
    ·
      refine ⟨262544518119702687405909515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175029678746468458270606343 262544518119702687405909515)
      ·
        refine ⟨393816777179554031108864273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262544518119702687405909515 393816777179554031108864273)
        ·
          refine ⟨295362582884665523331648205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393816777179554031108864273 295362582884665523331648205)
          ·
            refine ⟨110760968581749571249368077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295362582884665523331648205 110760968581749571249368077)
            ·
              refine ⟨41535363218156089218513029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110760968581749571249368077 41535363218156089218513029)
              ·
                refine ⟨7787880603404266728471193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41535363218156089218513029 7787880603404266728471193)
                ·
                  refine ⟨5840910452553200046353395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7787880603404266728471193 5840910452553200046353395)
                  ·
                    refine ⟨8761365678829800069530093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5840910452553200046353395 8761365678829800069530093)
                    ·
                      refine ⟨3285512129561175026073785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8761365678829800069530093 3285512129561175026073785)
                      ·
                        rfl

theorem cell23_6398512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 2, 1, 3].length) (baseStart_6398512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398512 prefixEnd_6398512 := by exact prefixLift 6398512
  have htrace : WordTrace (prefixWord ++ tailWord_6398512) baseStart_6398512 baseEnd_6398512 := by
    simpa [prefixWord, tailWord_6398512, baseEnd_6398512] using wordTrace_append hprefix tailTrace_6398512
  have hstable : (prefixWord ++ tailWord_6398512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398512).length < 2 ^ (prefixWord ++ tailWord_6398512).sum := by decide
  have hdescent : baseEnd_6398512 < baseStart_6398512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398522 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2]
def baseStart_6398522 : Nat := 118140960795 + 6398522 * 2 ^ 59
def prefixEnd_6398522 : Nat := 4983230072969 + 3 ^ 40 * 6398522 * 2
def baseEnd_6398522 : Nat := 3285517264367719986948739

theorem tailTrace_6398522 : CollatzResearch.WordTrace tailWord_6398522 prefixEnd_6398522 3285517264367719986948739 := by
  unfold tailWord_6398522
  simp only [CollatzResearch.WordTrace]
  refine ⟨58343317431313762350501455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155582179816836699601337213 58343317431313762350501455)
  ·
    refine ⟨87514976146970643525752183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58343317431313762350501455 87514976146970643525752183)
    ·
      refine ⟨131272464220455965288628275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87514976146970643525752183 131272464220455965288628275)
      ·
        refine ⟨196908696330683947932942413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131272464220455965288628275 196908696330683947932942413)
        ·
          refine ⟨73840761124006480474853405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196908696330683947932942413 73840761124006480474853405)
          ·
            refine ⟨27690285421502430178070027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73840761124006480474853405 27690285421502430178070027)
            ·
              refine ⟨41535428132253645267105041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27690285421502430178070027 41535428132253645267105041)
              ·
                refine ⟨31151571099190233950328781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41535428132253645267105041 31151571099190233950328781)
                ·
                  refine ⟨11681839162196337731373293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31151571099190233950328781 11681839162196337731373293)
                  ·
                    refine ⟨4380689685823626649264985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11681839162196337731373293 4380689685823626649264985)
                    ·
                      refine ⟨3285517264367719986948739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4380689685823626649264985 3285517264367719986948739)
                      ·
                        rfl

theorem cell23_6398522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2].length) (baseStart_6398522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398522 prefixEnd_6398522 := by exact prefixLift 6398522
  have htrace : WordTrace (prefixWord ++ tailWord_6398522) baseStart_6398522 baseEnd_6398522 := by
    simpa [prefixWord, tailWord_6398522, baseEnd_6398522] using wordTrace_append hprefix tailTrace_6398522
  have hstable : (prefixWord ++ tailWord_6398522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398522).length < 2 ^ (prefixWord ++ tailWord_6398522).sum := by decide
  have hdescent : baseEnd_6398522 < baseStart_6398522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398528 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 1, 8]
def baseStart_6398528 : Nat := 118140960795 + 6398528 * 2 ^ 59
def prefixEnd_6398528 : Nat := 4983230072969 + 3 ^ 40 * 6398528 * 2
def baseEnd_6398528 : Nat := 1095173448417215654491237

theorem tailTrace_6398528 : CollatzResearch.WordTrace tailWord_6398528 prefixEnd_6398528 1095173448417215654491237 := by
  unfold tailWord_6398528
  simp only [CollatzResearch.WordTrace]
  refine ⟨116686744281616656213362119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155582325708822208284482825 116686744281616656213362119)
  ·
    refine ⟨175030116422424984320043179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116686744281616656213362119 175030116422424984320043179)
    ·
      refine ⟨262545174633637476480064769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175030116422424984320043179 262545174633637476480064769)
      ·
        refine ⟨196908880975228107360048577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262545174633637476480064769 196908880975228107360048577)
        ·
          refine ⟨147681660731421080520036433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196908880975228107360048577 147681660731421080520036433)
          ·
            refine ⟨110761245548565810390027325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147681660731421080520036433 110761245548565810390027325)
            ·
              refine ⟨41535467080712178896260247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110761245548565810390027325 41535467080712178896260247)
              ·
                refine ⟨62303200621068268344390371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41535467080712178896260247 62303200621068268344390371)
                ·
                  refine ⟨93454800931602402516585557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62303200621068268344390371 93454800931602402516585557)
                  ·
                    refine ⟨1095173448417215654491237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93454800931602402516585557 1095173448417215654491237)
                    ·
                      rfl

theorem cell23_6398528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 8].length) (baseStart_6398528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398528 prefixEnd_6398528 := by exact prefixLift 6398528
  have htrace : WordTrace (prefixWord ++ tailWord_6398528) baseStart_6398528 baseEnd_6398528 := by
    simpa [prefixWord, tailWord_6398528, baseEnd_6398528] using wordTrace_append hprefix tailTrace_6398528
  have hstable : (prefixWord ++ tailWord_6398528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398528).length < 2 ^ (prefixWord ++ tailWord_6398528).sum := by decide
  have hdescent : baseEnd_6398528 < baseStart_6398528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398529 : List Nat := [1, 2, 5, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_6398529 : Nat := 118140960795 + 6398529 * 2 ^ 59
def prefixEnd_6398529 : Nat := 4983230072969 + 3 ^ 40 * 6398529 * 2
def baseEnd_6398529 : Nat := 3285520858732301459561207

theorem tailTrace_6398529 : CollatzResearch.WordTrace tailWord_6398529 prefixEnd_6398529 3285520858732301459561207 := by
  unfold tailWord_6398529
  simp only [CollatzResearch.WordTrace]
  refine ⟨233373525036229689597510641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155582350024153126398340427 233373525036229689597510641)
  ·
    refine ⟨175030143777172267198132981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233373525036229689597510641 175030143777172267198132981)
    ·
      refine ⟨16409075979109900049824967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 175030143777172267198132981 16409075979109900049824967)
      ·
        refine ⟨24613613968664850074737451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16409075979109900049824967 24613613968664850074737451)
        ·
          refine ⟨36920420952997275112106177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24613613968664850074737451 36920420952997275112106177)
          ·
            refine ⟨27690315714747956334079633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36920420952997275112106177 27690315714747956334079633)
            ·
              refine ⟨20767736786060967250559725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27690315714747956334079633 20767736786060967250559725)
              ·
                refine ⟨7787901294772862718959897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20767736786060967250559725 7787901294772862718959897)
                ·
                  refine ⟨5840925971079647039219923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7787901294772862718959897 5840925971079647039219923)
                  ·
                    refine ⟨8761388956619470558829885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5840925971079647039219923 8761388956619470558829885)
                    ·
                      refine ⟨3285520858732301459561207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8761388956619470558829885 3285520858732301459561207)
                      ·
                        rfl

theorem cell23_6398529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_6398529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398529 prefixEnd_6398529 := by exact prefixLift 6398529
  have htrace : WordTrace (prefixWord ++ tailWord_6398529) baseStart_6398529 baseEnd_6398529 := by
    simpa [prefixWord, tailWord_6398529, baseEnd_6398529] using wordTrace_append hprefix tailTrace_6398529
  have hstable : (prefixWord ++ tailWord_6398529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398529).length < 2 ^ (prefixWord ++ tailWord_6398529).sum := by decide
  have hdescent : baseEnd_6398529 < baseStart_6398529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398552 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 1, 4, 2]
def baseStart_6398552 : Nat := 118140960795 + 6398552 * 2 ^ 59
def prefixEnd_6398552 : Nat := 4983230072969 + 3 ^ 40 * 6398552 * 2
def baseEnd_6398552 : Nat := 3285532668787354869573601

theorem tailTrace_6398552 : CollatzResearch.WordTrace tailWord_6398552 prefixEnd_6398552 3285532668787354869573601 := by
  unfold tailWord_6398552
  simp only [CollatzResearch.WordTrace]
  refine ⟨116687181957573182262798955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155582909276764243017065273 116687181957573182262798955)
  ·
    refine ⟨175030772936359773394198433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116687181957573182262798955 175030772936359773394198433)
    ·
      refine ⟨131273079702269830045648825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175030772936359773394198433 131273079702269830045648825)
      ·
        refine ⟨98454809776702372534236619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131273079702269830045648825 98454809776702372534236619)
        ·
          refine ⟨147682214665053558801354929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98454809776702372534236619 147682214665053558801354929)
          ·
            refine ⟨110761660998790169101016197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147682214665053558801354929 110761660998790169101016197)
            ·
              refine ⟨20767811437273156706440537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110761660998790169101016197 20767811437273156706440537)
              ·
                refine ⟨15575858577954867529830403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20767811437273156706440537 15575858577954867529830403)
                ·
                  refine ⟨23363787866932301294745605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15575858577954867529830403 23363787866932301294745605)
                  ·
                    refine ⟨4380710225049806492764801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23363787866932301294745605 4380710225049806492764801)
                    ·
                      refine ⟨3285532668787354869573601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4380710225049806492764801 3285532668787354869573601)
                      ·
                        rfl

theorem cell23_6398552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_6398552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398552 prefixEnd_6398552 := by exact prefixLift 6398552
  have htrace : WordTrace (prefixWord ++ tailWord_6398552) baseStart_6398552 baseEnd_6398552 := by
    simpa [prefixWord, tailWord_6398552, baseEnd_6398552] using wordTrace_append hprefix tailTrace_6398552
  have hstable : (prefixWord ++ tailWord_6398552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398552).length < 2 ^ (prefixWord ++ tailWord_6398552).sum := by decide
  have hdescent : baseEnd_6398552 < baseStart_6398552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398556 : List Nat := [2, 2, 4, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_6398556 : Nat := 118140960795 + 6398556 * 2 ^ 59
def prefixEnd_6398556 : Nat := 4983230072969 + 3 ^ 40 * 6398556 * 2
def baseEnd_6398556 : Nat := 3285534722709972853923583

theorem tailTrace_6398556 : CollatzResearch.WordTrace tailWord_6398556 prefixEnd_6398556 3285534722709972853923583 := by
  unfold tailWord_6398556
  simp only [CollatzResearch.WordTrace]
  refine ⟨116687254903565936604371761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155583006538087915472495681 116687254903565936604371761)
  ·
    refine ⟨87515441177674452453278821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116687254903565936604371761 87515441177674452453278821)
    ·
      refine ⟨16409145220813959834989779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87515441177674452453278821 16409145220813959834989779)
      ·
        refine ⟨24613717831220939752484669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16409145220813959834989779 24613717831220939752484669)
        ·
          refine ⟨9230144186707852407181751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24613717831220939752484669 9230144186707852407181751)
          ·
            refine ⟨13845216280061778610772627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9230144186707852407181751 13845216280061778610772627)
            ·
              refine ⟨20767824420092667916158941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13845216280061778610772627 20767824420092667916158941)
              ·
                refine ⟨7787934157534750468559603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20767824420092667916158941 7787934157534750468559603)
                ·
                  refine ⟨11681901236302125702839405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7787934157534750468559603 11681901236302125702839405)
                  ·
                    refine ⟨4380712963613297138564777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11681901236302125702839405 4380712963613297138564777)
                    ·
                      refine ⟨3285534722709972853923583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4380712963613297138564777 3285534722709972853923583)
                      ·
                        rfl

theorem cell23_6398556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_6398556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398556 prefixEnd_6398556 := by exact prefixLift 6398556
  have htrace : WordTrace (prefixWord ++ tailWord_6398556) baseStart_6398556 baseEnd_6398556 := by
    simpa [prefixWord, tailWord_6398556, baseEnd_6398556] using wordTrace_append hprefix tailTrace_6398556
  have hstable : (prefixWord ++ tailWord_6398556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398556).length < 2 ^ (prefixWord ++ tailWord_6398556).sum := by decide
  have hdescent : baseEnd_6398556 < baseStart_6398556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398615 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 5]
def baseStart_6398615 : Nat := 118140960795 + 6398615 * 2 ^ 59
def prefixEnd_6398615 : Nat := 4983230072969 + 3 ^ 40 * 6398615 * 2
def baseEnd_6398615 : Nat := 3285565018068588123085811

theorem tailTrace_6398615 : CollatzResearch.WordTrace tailWord_6398615 prefixEnd_6398615 3285565018068588123085811 := by
  unfold tailWord_6398615
  simp only [CollatzResearch.WordTrace]
  refine ⟨233376661713918126285141299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155584441142612084190094199 233376661713918126285141299)
  ·
    refine ⟨350064992570877189427711949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233376661713918126285141299 350064992570877189427711949)
    ·
      refine ⟨131274372214078946035391981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350064992570877189427711949 131274372214078946035391981)
      ·
        refine ⟨49227889580279604763271993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131274372214078946035391981 49227889580279604763271993)
        ·
          refine ⟨36920917185209703572453995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49227889580279604763271993 36920917185209703572453995)
          ·
            refine ⟨55381375777814555358680993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36920917185209703572453995 55381375777814555358680993)
            ·
              refine ⟨41536031833360916519010745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55381375777814555358680993 41536031833360916519010745)
              ·
                refine ⟨31152023875020687389258059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41536031833360916519010745 31152023875020687389258059)
                ·
                  refine ⟨46728035812531031083887089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31152023875020687389258059 46728035812531031083887089)
                  ·
                    refine ⟨35046026859398273312915317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46728035812531031083887089 35046026859398273312915317)
                    ·
                      refine ⟨3285565018068588123085811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35046026859398273312915317 3285565018068588123085811)
                      ·
                        rfl

theorem cell23_6398615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_6398615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398615 prefixEnd_6398615 := by exact prefixLift 6398615
  have htrace : WordTrace (prefixWord ++ tailWord_6398615) baseStart_6398615 baseEnd_6398615 := by
    simpa [prefixWord, tailWord_6398615, baseEnd_6398615] using wordTrace_append hprefix tailTrace_6398615
  have hstable : (prefixWord ++ tailWord_6398615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398615).length < 2 ^ (prefixWord ++ tailWord_6398615).sum := by decide
  have hdescent : baseEnd_6398615 < baseStart_6398615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398642 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2]
def baseStart_6398642 : Nat := 118140960795 + 6398642 * 2 ^ 59
def prefixEnd_6398642 : Nat := 4983230072969 + 3 ^ 40 * 6398642 * 2
def baseEnd_6398642 : Nat := 3285578882046259517448187

theorem tailTrace_6398642 : CollatzResearch.WordTrace tailWord_6398642 prefixEnd_6398642 3285578882046259517448187 := by
  unfold tailWord_6398642
  simp only [CollatzResearch.WordTrace]
  refine ⟨58344411621205077474093545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155585097656546873264249453 58344411621205077474093545)
  ·
    refine ⟨43758308715903808105570159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58344411621205077474093545 43758308715903808105570159)
    ·
      refine ⟨65637463073855712158355239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43758308715903808105570159 65637463073855712158355239)
      ·
        refine ⟨98456194610783568237532859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65637463073855712158355239 98456194610783568237532859)
        ·
          refine ⟨147684291916175352356299289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98456194610783568237532859 147684291916175352356299289)
          ·
            refine ⟨110763218937131514267224467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147684291916175352356299289 110763218937131514267224467)
            ·
              refine ⟨166144828405697271400836701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110763218937131514267224467 166144828405697271400836701)
              ·
                refine ⟨62304310652136476775313763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166144828405697271400836701 62304310652136476775313763)
                ·
                  refine ⟨93456465978204715162970645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62304310652136476775313763 93456465978204715162970645)
                  ·
                    refine ⟨4380771842728346023264249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93456465978204715162970645 4380771842728346023264249)
                    ·
                      refine ⟨3285578882046259517448187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4380771842728346023264249 3285578882046259517448187)
                      ·
                        rfl

theorem cell23_6398642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_6398642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398642 prefixEnd_6398642 := by exact prefixLift 6398642
  have htrace : WordTrace (prefixWord ++ tailWord_6398642) baseStart_6398642 baseEnd_6398642 := by
    simpa [prefixWord, tailWord_6398642, baseEnd_6398642] using wordTrace_append hprefix tailTrace_6398642
  have hstable : (prefixWord ++ tailWord_6398642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398642).length < 2 ^ (prefixWord ++ tailWord_6398642).sum := by decide
  have hdescent : baseEnd_6398642 < baseStart_6398642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398652 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 5, 4]
def baseStart_6398652 : Nat := 118140960795 + 6398652 * 2 ^ 59
def prefixEnd_6398652 : Nat := 4983230072969 + 3 ^ 40 * 6398652 * 2
def baseEnd_6398652 : Nat := 1095194672284268159441047

theorem tailTrace_6398652 : CollatzResearch.WordTrace tailWord_6398652 prefixEnd_6398652 1095194672284268159441047 := by
  unfold tailWord_6398652
  simp only [CollatzResearch.WordTrace]
  refine ⟨116689005607392040802119105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155585340809856054402825473 116689005607392040802119105)
  ·
    refine ⟨87516754205544030601589329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116689005607392040802119105 87516754205544030601589329)
    ·
      refine ⟨65637565654158022951191997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87516754205544030601589329 65637565654158022951191997)
      ·
        refine ⟨24614087120309258606696999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65637565654158022951191997 24614087120309258606696999)
        ·
          refine ⟨36921130680463887910045499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24614087120309258606696999 36921130680463887910045499)
          ·
            refine ⟨55381696020695831865068249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36921130680463887910045499 55381696020695831865068249)
            ·
              refine ⟨41536272015521873898801187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55381696020695831865068249 41536272015521873898801187)
              ·
                refine ⟨62304408023282810848201781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41536272015521873898801187 62304408023282810848201781)
                ·
                  refine ⟨5841038252182763517018917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62304408023282810848201781 5841038252182763517018917)
                  ·
                    refine ⟨1095194672284268159441047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5841038252182763517018917 1095194672284268159441047)
                    ·
                      rfl

theorem cell23_6398652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_6398652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398652 prefixEnd_6398652 := by exact prefixLift 6398652
  have htrace : WordTrace (prefixWord ++ tailWord_6398652) baseStart_6398652 baseEnd_6398652 := by
    simpa [prefixWord, tailWord_6398652, baseEnd_6398652] using wordTrace_append hprefix tailTrace_6398652
  have hstable : (prefixWord ++ tailWord_6398652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398652).length < 2 ^ (prefixWord ++ tailWord_6398652).sum := by decide
  have hdescent : baseEnd_6398652 < baseStart_6398652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398682 : List Nat := [3, 1, 1, 2, 2, 2, 4, 2, 6]
def baseStart_6398682 : Nat := 118140960795 + 6398682 * 2 ^ 59
def prefixEnd_6398682 : Nat := 4983230072969 + 3 ^ 40 * 6398682 * 2
def baseEnd_6398682 : Nat := 365066602363604373438667

theorem tailTrace_6398682 : CollatzResearch.WordTrace tailWord_6398682 prefixEnd_6398682 365066602363604373438667 := by
  unfold tailWord_6398682
  simp only [CollatzResearch.WordTrace]
  refine ⟨58344776351168849181957575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155586070269783597818553533 58344776351168849181957575)
  ·
    refine ⟨87517164526753273772936363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58344776351168849181957575 87517164526753273772936363)
    ·
      refine ⟨131275746790129910659404545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87517164526753273772936363 131275746790129910659404545)
      ·
        refine ⟨98456810092597432994553409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131275746790129910659404545 98456810092597432994553409)
        ·
          refine ⟨73842607569448074745915057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98456810092597432994553409 73842607569448074745915057)
          ·
            refine ⟨55381955677086056059436293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73842607569448074745915057 55381955677086056059436293)
            ·
              refine ⟨10384116689453635511144305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55381955677086056059436293 10384116689453635511144305)
              ·
                refine ⟨7788087517090226633358229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10384116689453635511144305 7788087517090226633358229)
                ·
                  refine ⟨365066602363604373438667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7788087517090226633358229 365066602363604373438667)
                  ·
                    rfl

theorem cell23_6398682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 6].length) (baseStart_6398682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398682 prefixEnd_6398682 := by exact prefixLift 6398682
  have htrace : WordTrace (prefixWord ++ tailWord_6398682) baseStart_6398682 baseEnd_6398682 := by
    simpa [prefixWord, tailWord_6398682, baseEnd_6398682] using wordTrace_append hprefix tailTrace_6398682
  have hstable : (prefixWord ++ tailWord_6398682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398682).length < 2 ^ (prefixWord ++ tailWord_6398682).sum := by decide
  have hdescent : baseEnd_6398682 < baseStart_6398682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398705 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 7]
def baseStart_6398705 : Nat := 118140960795 + 6398705 * 2 ^ 59
def prefixEnd_6398705 : Nat := 4983230072969 + 3 ^ 40 * 6398705 * 2
def baseEnd_6398705 : Nat := 3285611231327492770960397

theorem tailTrace_6398705 : CollatzResearch.WordTrace tailWord_6398705 prefixEnd_6398705 3285611231327492770960397 := by
  unfold tailWord_6398705
  simp only [CollatzResearch.WordTrace]
  refine ⟨233379944283592071655917569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155586629522394714437278379 233379944283592071655917569)
  ·
    refine ⟨175034958212694053741938177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233379944283592071655917569 175034958212694053741938177)
    ·
      refine ⟨131276218659520540306453633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175034958212694053741938177 131276218659520540306453633)
      ·
        refine ⟨98457163994640405229840225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131276218659520540306453633 98457163994640405229840225)
        ·
          refine ⟨73842872995980303922380169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98457163994640405229840225 73842872995980303922380169)
          ·
            refine ⟨55382154746985227941785127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73842872995980303922380169 55382154746985227941785127)
            ·
              refine ⟨83073232120477841912677691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55382154746985227941785127 83073232120477841912677691)
              ·
                refine ⟨124609848180716762869016537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83073232120477841912677691 124609848180716762869016537)
                ·
                  refine ⟨93457386135537572151762403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124609848180716762869016537 93457386135537572151762403)
                  ·
                    refine ⟨140186079203306358227643605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93457386135537572151762403 140186079203306358227643605)
                    ·
                      refine ⟨3285611231327492770960397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140186079203306358227643605 3285611231327492770960397)
                      ·
                        rfl

theorem cell23_6398705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_6398705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398705 prefixEnd_6398705 := by exact prefixLift 6398705
  have htrace : WordTrace (prefixWord ++ tailWord_6398705) baseStart_6398705 baseEnd_6398705 := by
    simpa [prefixWord, tailWord_6398705, baseEnd_6398705] using wordTrace_append hprefix tailTrace_6398705
  have hstable : (prefixWord ++ tailWord_6398705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398705).length < 2 ^ (prefixWord ++ tailWord_6398705).sum := by decide
  have hdescent : baseEnd_6398705 < baseStart_6398705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398712 : List Nat := [2, 1, 2, 1, 1, 2, 4, 4, 1, 5]
def baseStart_6398712 : Nat := 118140960795 + 6398712 * 2 ^ 59
def prefixEnd_6398712 : Nat := 4983230072969 + 3 ^ 40 * 6398712 * 2
def baseEnd_6398712 : Nat := 1095204941897358081190955

theorem tailTrace_6398712 : CollatzResearch.WordTrace tailWord_6398712 prefixEnd_6398712 1095204941897358081190955 := by
  unfold tailWord_6398712
  simp only [CollatzResearch.WordTrace]
  refine ⟨116690099797283355925711195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155586799729711141234281593 116690099797283355925711195)
  ·
    refine ⟨175035149695925033888566793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116690099797283355925711195 175035149695925033888566793)
    ·
      refine ⟨131276362271943775416425095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175035149695925033888566793 131276362271943775416425095)
      ·
        refine ⟨196914543407915663124637643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131276362271943775416425095 196914543407915663124637643)
        ·
          refine ⟨295371815111873494686956465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196914543407915663124637643 295371815111873494686956465)
          ·
            refine ⟨221528861333905121015217349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295371815111873494686956465 221528861333905121015217349)
            ·
              refine ⟨41536661500107210190353253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 221528861333905121015217349 41536661500107210190353253)
              ·
                refine ⟨7788124031270101910691235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41536661500107210190353253 7788124031270101910691235)
                ·
                  refine ⟨11682186046905152866036853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7788124031270101910691235 11682186046905152866036853)
                  ·
                    refine ⟨1095204941897358081190955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11682186046905152866036853 1095204941897358081190955)
                    ·
                      rfl

theorem cell23_6398712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_6398712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398712 prefixEnd_6398712 := by exact prefixLift 6398712
  have htrace : WordTrace (prefixWord ++ tailWord_6398712) baseStart_6398712 baseEnd_6398712 := by
    simpa [prefixWord, tailWord_6398712, baseEnd_6398712] using wordTrace_append hprefix tailTrace_6398712
  have hstable : (prefixWord ++ tailWord_6398712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398712).length < 2 ^ (prefixWord ++ tailWord_6398712).sum := by decide
  have hdescent : baseEnd_6398712 < baseStart_6398712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398729 : List Nat := [1, 2, 1, 1, 3, 2, 6, 1, 1, 5]
def baseStart_6398729 : Nat := 118140960795 + 6398729 * 2 ^ 59
def prefixEnd_6398729 : Nat := 4983230072969 + 3 ^ 40 * 6398729 * 2
def baseEnd_6398729 : Nat := 1095207851621066892353429

theorem tailTrace_6398729 : CollatzResearch.WordTrace tailWord_6398729 prefixEnd_6398729 1095207851621066892353429 := by
  unfold tailWord_6398729
  simp only [CollatzResearch.WordTrace]
  refine ⟨233380819635505123754791241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155587213090336749169860827 233380819635505123754791241)
  ·
    refine ⟨175035614726628842816093431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233380819635505123754791241 175035614726628842816093431)
    ·
      refine ⟨262553422089943264224140147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175035614726628842816093431 262553422089943264224140147)
      ·
        refine ⟨393830133134914896336210221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262553422089943264224140147 393830133134914896336210221)
        ·
          refine ⟨147686299925593086126078833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 393830133134914896336210221 147686299925593086126078833)
          ·
            refine ⟨110764724944194814594559125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147686299925593086126078833 110764724944194814594559125)
            ·
              refine ⟨5192096481759131934119959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110764724944194814594559125 5192096481759131934119959)
              ·
                refine ⟨7788144722638697901179939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5192096481759131934119959 7788144722638697901179939)
                ·
                  refine ⟨11682217083958046851769909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7788144722638697901179939 11682217083958046851769909)
                  ·
                    refine ⟨1095207851621066892353429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11682217083958046851769909 1095207851621066892353429)
                    ·
                      rfl

theorem cell23_6398729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 1, 5].length) (baseStart_6398729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398729 prefixEnd_6398729 := by exact prefixLift 6398729
  have htrace : WordTrace (prefixWord ++ tailWord_6398729) baseStart_6398729 baseEnd_6398729 := by
    simpa [prefixWord, tailWord_6398729, baseEnd_6398729] using wordTrace_append hprefix tailTrace_6398729
  have hstable : (prefixWord ++ tailWord_6398729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398729).length < 2 ^ (prefixWord ++ tailWord_6398729).sum := by decide
  have hdescent : baseEnd_6398729 < baseStart_6398729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398752 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 5]
def baseStart_6398752 : Nat := 118140960795 + 6398752 * 2 ^ 59
def prefixEnd_6398752 : Nat := 4983230072969 + 3 ^ 40 * 6398752 * 2
def baseEnd_6398752 : Nat := 3285635364918254087072681

theorem tailTrace_6398752 : CollatzResearch.WordTrace tailWord_6398752 prefixEnd_6398752 3285635364918254087072681 := by
  unfold tailWord_6398752
  simp only [CollatzResearch.WordTrace]
  refine ⟨116690829257210899341439255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155587772342947865788585673 116690829257210899341439255)
  ·
    refine ⟨175036243885816349012158883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116690829257210899341439255 175036243885816349012158883)
    ·
      refine ⟨262554365828724523518238325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175036243885816349012158883 262554365828724523518238325)
      ·
        refine ⟨24614471796442924079834843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 262554365828724523518238325 24614471796442924079834843)
        ·
          refine ⟨36921707694664386119752265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24614471796442924079834843 36921707694664386119752265)
          ·
            refine ⟨27691280770998289589814199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36921707694664386119752265 27691280770998289589814199)
            ·
              refine ⟨41536921156497434384721299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27691280770998289589814199 41536921156497434384721299)
              ·
                refine ⟨62305381734746151577081949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41536921156497434384721299 62305381734746151577081949)
                ·
                  refine ⟨23364518150529806841405731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62305381734746151577081949 23364518150529806841405731)
                  ·
                    refine ⟨35046777225794710262108597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23364518150529806841405731 35046777225794710262108597)
                    ·
                      refine ⟨3285635364918254087072681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35046777225794710262108597 3285635364918254087072681)
                      ·
                        rfl

theorem cell23_6398752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_6398752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398752 prefixEnd_6398752 := by exact prefixLift 6398752
  have htrace : WordTrace (prefixWord ++ tailWord_6398752) baseStart_6398752 baseEnd_6398752 := by
    simpa [prefixWord, tailWord_6398752, baseEnd_6398752] using wordTrace_append hprefix tailTrace_6398752
  have hstable : (prefixWord ++ tailWord_6398752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398752).length < 2 ^ (prefixWord ++ tailWord_6398752).sum := by decide
  have hdescent : baseEnd_6398752 < baseStart_6398752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398755 : List Nat := [1, 1, 1, 4, 2, 1, 1, 12]
def baseStart_6398755 : Nat := 118140960795 + 6398755 * 2 ^ 59
def prefixEnd_6398755 : Nat := 4983230072969 + 3 ^ 40 * 6398755 * 2
def baseEnd_6398755 : Nat := 121690255754082132419821

theorem tailTrace_6398755 : CollatzResearch.WordTrace tailWord_6398755 prefixEnd_6398755 121690255754082132419821 := by
  unfold tailWord_6398755
  simp only [CollatzResearch.WordTrace]
  refine ⟨233381767933410930195237719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155587845288940620130158479 233381767933410930195237719)
  ·
    refine ⟨350072651900116395292856579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233381767933410930195237719 350072651900116395292856579)
    ·
      refine ⟨525108977850174592939284869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350072651900116395292856579 525108977850174592939284869)
      ·
        refine ⟨98457933346907736176115913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 525108977850174592939284869 98457933346907736176115913)
        ·
          refine ⟨73843450010180802132086935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98457933346907736176115913 73843450010180802132086935)
          ·
            refine ⟨110765175015271203198130403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73843450010180802132086935 110765175015271203198130403)
            ·
              refine ⟨166147762522906804797195605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110765175015271203198130403 166147762522906804797195605)
              ·
                refine ⟨121690255754082132419821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 166147762522906804797195605 121690255754082132419821)
                ·
                  rfl

theorem cell23_6398755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 12].length) (baseStart_6398755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398755 prefixEnd_6398755 := by exact prefixLift 6398755
  have htrace : WordTrace (prefixWord ++ tailWord_6398755) baseStart_6398755 baseEnd_6398755 := by
    simpa [prefixWord, tailWord_6398755, baseEnd_6398755] using wordTrace_append hprefix tailTrace_6398755
  have hstable : (prefixWord ++ tailWord_6398755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398755).length < 2 ^ (prefixWord ++ tailWord_6398755).sum := by decide
  have hdescent : baseEnd_6398755 < baseStart_6398755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398766 : List Nat := [4, 1, 3, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_6398766 : Nat := 118140960795 + 6398766 * 2 ^ 59
def prefixEnd_6398766 : Nat := 4983230072969 + 3 ^ 40 * 6398766 * 2
def baseEnd_6398766 : Nat := 3285642553647417032297617

theorem tailTrace_6398766 : CollatzResearch.WordTrace tailWord_6398766 prefixEnd_6398766 3285642553647417032297617 := by
  unfold tailWord_6398766
  simp only [CollatzResearch.WordTrace]
  refine ⟨29172771142046384884236019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155588112757580719382592101 29172771142046384884236019)
  ·
    refine ⟨43759156713069577326354029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29172771142046384884236019 43759156713069577326354029)
    ·
      refine ⟨16409683767401091497382761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43759156713069577326354029 16409683767401091497382761)
      ·
        refine ⟨12307262825550818623037071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16409683767401091497382761 12307262825550818623037071)
        ·
          refine ⟨18460894238326227934555607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12307262825550818623037071 18460894238326227934555607)
          ·
            refine ⟨27691341357489341901833411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18460894238326227934555607 27691341357489341901833411)
            ·
              refine ⟨41537012036234012852750117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27691341357489341901833411 41537012036234012852750117)
              ·
                refine ⟨7788189756793877409890647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41537012036234012852750117 7788189756793877409890647)
                ·
                  refine ⟨11682284635190816114835971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7788189756793877409890647 11682284635190816114835971)
                  ·
                    refine ⟨17523426952786224172253957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11682284635190816114835971 17523426952786224172253957)
                    ·
                      refine ⟨3285642553647417032297617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17523426952786224172253957 3285642553647417032297617)
                      ·
                        rfl

theorem cell23_6398766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_6398766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398766 prefixEnd_6398766 := by exact prefixLift 6398766
  have htrace : WordTrace (prefixWord ++ tailWord_6398766) baseStart_6398766 baseEnd_6398766 := by
    simpa [prefixWord, tailWord_6398766, baseEnd_6398766] using wordTrace_append hprefix tailTrace_6398766
  have hstable : (prefixWord ++ tailWord_6398766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398766).length < 2 ^ (prefixWord ++ tailWord_6398766).sum := by decide
  have hdescent : baseEnd_6398766 < baseStart_6398766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398802 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 2, 7]
def baseStart_6398802 : Nat := 118140960795 + 6398802 * 2 ^ 59
def prefixEnd_6398802 : Nat := 4983230072969 + 3 ^ 40 * 6398802 * 2
def baseEnd_6398802 : Nat := 1095220346316992963815817

theorem tailTrace_6398802 : CollatzResearch.WordTrace tailWord_6398802 prefixEnd_6398802 1095220346316992963815817 := by
  unfold tailWord_6398802
  simp only [CollatzResearch.WordTrace]
  refine ⟨58345870541060164305549665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155588988109493771481465773 58345870541060164305549665)
  ·
    refine ⟨43759402905795123229162249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58345870541060164305549665 43759402905795123229162249)
    ·
      refine ⟨32819552179346342421871687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43759402905795123229162249 32819552179346342421871687)
      ·
        refine ⟨49229328269019513632807531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32819552179346342421871687 49229328269019513632807531)
        ·
          refine ⟨73843992403529270449211297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49229328269019513632807531 73843992403529270449211297)
          ·
            refine ⟨55382994302646952836908473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73843992403529270449211297 55382994302646952836908473)
            ·
              refine ⟨41537245726985214627681355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55382994302646952836908473 41537245726985214627681355)
              ·
                refine ⟨62305868590477821941522033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41537245726985214627681355 62305868590477821941522033)
                ·
                  refine ⟨46729401442858366456141525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62305868590477821941522033 46729401442858366456141525)
                  ·
                    refine ⟨1095220346316992963815817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46729401442858366456141525 1095220346316992963815817)
                    ·
                      rfl

theorem cell23_6398802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_6398802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398802 prefixEnd_6398802 := by exact prefixLift 6398802
  have htrace : WordTrace (prefixWord ++ tailWord_6398802) baseStart_6398802 baseEnd_6398802 := by
    simpa [prefixWord, tailWord_6398802, baseEnd_6398802] using wordTrace_append hprefix tailTrace_6398802
  have hstable : (prefixWord ++ tailWord_6398802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398802).length < 2 ^ (prefixWord ++ tailWord_6398802).sum := by decide
  have hdescent : baseEnd_6398802 < baseStart_6398802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398816 : List Nat := [2, 1, 1, 3, 3, 1, 3, 3, 2, 1, 3]
def baseStart_6398816 : Nat := 118140960795 + 6398816 * 2 ^ 59
def prefixEnd_6398816 : Nat := 4983230072969 + 3 ^ 40 * 6398816 * 2
def baseEnd_6398816 : Nat := 3285668227680141836672387

theorem tailTrace_6398816 : CollatzResearch.WordTrace tailWord_6398816 prefixEnd_6398816 3285668227680141836672387 := by
  unfold tailWord_6398816
  simp only [CollatzResearch.WordTrace]
  refine ⟨116691996393094968806604151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155589328524126625075472201 116691996393094968806604151)
  ·
    refine ⟨175037994589642453209906227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116691996393094968806604151 175037994589642453209906227)
    ·
      refine ⟨262556991884463679814859341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175037994589642453209906227 262556991884463679814859341)
      ·
        refine ⟨98458871956673879930572253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262556991884463679814859341 98458871956673879930572253)
        ·
          refine ⟨36922076983752704973964595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98458871956673879930572253 36922076983752704973964595)
          ·
            refine ⟨55383115475629057460946893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36922076983752704973964595 55383115475629057460946893)
            ·
              refine ⟨20768668303360896547855085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55383115475629057460946893 20768668303360896547855085)
              ·
                refine ⟨7788250613760336205445657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20768668303360896547855085 7788250613760336205445657)
                ·
                  refine ⟨5841187960320252154084243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7788250613760336205445657 5841187960320252154084243)
                  ·
                    refine ⟨8761781940480378231126365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5841187960320252154084243 8761781940480378231126365)
                    ·
                      refine ⟨3285668227680141836672387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8761781940480378231126365 3285668227680141836672387)
                      ·
                        rfl

theorem cell23_6398816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_6398816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398816 prefixEnd_6398816 := by exact prefixLift 6398816
  have htrace : WordTrace (prefixWord ++ tailWord_6398816) baseStart_6398816 baseEnd_6398816 := by
    simpa [prefixWord, tailWord_6398816, baseEnd_6398816] using wordTrace_append hprefix tailTrace_6398816
  have hstable : (prefixWord ++ tailWord_6398816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398816).length < 2 ^ (prefixWord ++ tailWord_6398816).sum := by decide
  have hdescent : baseEnd_6398816 < baseStart_6398816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398852 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_6398852 : Nat := 118140960795 + 6398852 * 2 ^ 59
def prefixEnd_6398852 : Nat := 4983230072969 + 3 ^ 40 * 6398852 * 2
def baseEnd_6398852 : Nat := 3285686712983703695822221

theorem tailTrace_6398852 : CollatzResearch.WordTrace tailWord_6398852 prefixEnd_6398852 3285686712983703695822221 := by
  unfold tailWord_6398852
  simp only [CollatzResearch.WordTrace]
  refine ⟨116692652907029757880759405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155590203876039677174345873 116692652907029757880759405)
  ·
    refine ⟨43759744840136159205284777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116692652907029757880759405 43759744840136159205284777)
    ·
      refine ⟨32819808630102119403963583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43759744840136159205284777 32819808630102119403963583)
      ·
        refine ⟨49229712945153179105945375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32819808630102119403963583 49229712945153179105945375)
        ·
          refine ⟨73844569417729768658918063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49229712945153179105945375 73844569417729768658918063)
          ·
            refine ⟨110766854126594652988377095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73844569417729768658918063 110766854126594652988377095)
            ·
              refine ⟨166150281189891979482565643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110766854126594652988377095 166150281189891979482565643)
              ·
                refine ⟨249225421784837969223848465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166150281189891979482565643 249225421784837969223848465)
                ·
                  refine ⟨186919066338628476917886349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249225421784837969223848465 186919066338628476917886349)
                  ·
                    refine ⟨70094649876985678844207381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 186919066338628476917886349 70094649876985678844207381)
                    ·
                      refine ⟨3285686712983703695822221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70094649876985678844207381 3285686712983703695822221)
                      ·
                        rfl

theorem cell23_6398852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_6398852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398852 prefixEnd_6398852 := by exact prefixLift 6398852
  have htrace : WordTrace (prefixWord ++ tailWord_6398852) baseStart_6398852 baseEnd_6398852 := by
    simpa [prefixWord, tailWord_6398852, baseEnd_6398852] using wordTrace_append hprefix tailTrace_6398852
  have hstable : (prefixWord ++ tailWord_6398852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398852).length < 2 ^ (prefixWord ++ tailWord_6398852).sum := by decide
  have hdescent : baseEnd_6398852 < baseStart_6398852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398866 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 2, 6]
def baseStart_6398866 : Nat := 118140960795 + 6398866 * 2 ^ 59
def prefixEnd_6398866 : Nat := 4983230072969 + 3 ^ 40 * 6398866 * 2
def baseEnd_6398866 : Nat := 1095231300570955547015719

theorem tailTrace_6398866 : CollatzResearch.WordTrace tailWord_6398866 prefixEnd_6398866 1095231300570955547015719 := by
  unfold tailWord_6398866
  simp only [CollatzResearch.WordTrace]
  refine ⟨58346454109002199038132113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155590544290672530768352301 58346454109002199038132113)
  ·
    refine ⟨43759840581751649278599085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58346454109002199038132113 43759840581751649278599085)
    ·
      refine ⟨16409940218156868479474657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43759840581751649278599085 16409940218156868479474657)
      ·
        refine ⟨12307455163617651359605993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16409940218156868479474657 12307455163617651359605993)
        ·
          refine ⟨9230591372713238519704495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12307455163617651359605993 9230591372713238519704495)
          ·
            refine ⟨13845887059069857779556743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9230591372713238519704495 13845887059069857779556743)
            ·
              refine ⟨20768830588604786669335115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13845887059069857779556743 20768830588604786669335115)
              ·
                refine ⟨31153245882907180004002673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20768830588604786669335115 31153245882907180004002673)
                ·
                  refine ⟨23364934412180385003002005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31153245882907180004002673 23364934412180385003002005)
                  ·
                    refine ⟨1095231300570955547015719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23364934412180385003002005 1095231300570955547015719)
                    ·
                      rfl

theorem cell23_6398866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_6398866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398866 prefixEnd_6398866 := by exact prefixLift 6398866
  have htrace : WordTrace (prefixWord ++ tailWord_6398866) baseStart_6398866 baseEnd_6398866 := by
    simpa [prefixWord, tailWord_6398866, baseEnd_6398866] using wordTrace_append hprefix tailTrace_6398866
  have hstable : (prefixWord ++ tailWord_6398866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398866).length < 2 ^ (prefixWord ++ tailWord_6398866).sum := by decide
  have hdescent : baseEnd_6398866 < baseStart_6398866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398869 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_6398869 : Nat := 118140960795 + 6398869 * 2 ^ 59
def prefixEnd_6398869 : Nat := 4983230072969 + 3 ^ 40 * 6398869 * 2
def baseEnd_6398869 : Nat := 3285695442154830129309643

theorem tailTrace_6398869 : CollatzResearch.WordTrace tailWord_6398869 prefixEnd_6398869 3285695442154830129309643 := by
  unfold tailWord_6398869
  simp only [CollatzResearch.WordTrace]
  refine ⟨233385925854997927664887661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155590617236665285109925107 233385925854997927664887661)
  ·
    refine ⟨87519722195624222874332873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233385925854997927664887661 87519722195624222874332873)
    ·
      refine ⟨65639791646718167155749655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87519722195624222874332873 65639791646718167155749655)
      ·
        refine ⟨98459687470077250733624483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65639791646718167155749655 98459687470077250733624483)
        ·
          refine ⟨147689531205115876100436725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98459687470077250733624483 147689531205115876100436725)
          ·
            refine ⟨13845893550479613384415943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147689531205115876100436725 13845893550479613384415943)
            ·
              refine ⟨20768840325719420076623915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13845893550479613384415943 20768840325719420076623915)
              ·
                refine ⟨31153260488579130114935873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20768840325719420076623915 31153260488579130114935873)
                ·
                  refine ⟨23364945366434347586201905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31153260488579130114935873 23364945366434347586201905)
                  ·
                    refine ⟨17523709024825760689651429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23364945366434347586201905 17523709024825760689651429)
                    ·
                      refine ⟨3285695442154830129309643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17523709024825760689651429 3285695442154830129309643)
                      ·
                        rfl

theorem cell23_6398869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_6398869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398869 prefixEnd_6398869 := by exact prefixLift 6398869
  have htrace : WordTrace (prefixWord ++ tailWord_6398869) baseStart_6398869 baseEnd_6398869 := by
    simpa [prefixWord, tailWord_6398869, baseEnd_6398869] using wordTrace_append hprefix tailTrace_6398869
  have hstable : (prefixWord ++ tailWord_6398869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398869).length < 2 ^ (prefixWord ++ tailWord_6398869).sum := by decide
  have hdescent : baseEnd_6398869 < baseStart_6398869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398879 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 7]
def baseStart_6398879 : Nat := 118140960795 + 6398879 * 2 ^ 59
def prefixEnd_6398879 : Nat := 4983230072969 + 3 ^ 40 * 6398879 * 2
def baseEnd_6398879 : Nat := 365077841884597232242733

theorem tailTrace_6398879 : CollatzResearch.WordTrace tailWord_6398879 prefixEnd_6398879 365077841884597232242733 := by
  unfold tailWord_6398879
  simp only [CollatzResearch.WordTrace]
  refine ⟨233386290584961699372751691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155590860389974466248501127 233386290584961699372751691)
  ·
    refine ⟨350079435877442549059127537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233386290584961699372751691 350079435877442549059127537)
    ·
      refine ⟨262559576908081911794345653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350079435877442549059127537 262559576908081911794345653)
      ·
        refine ⟨24614960335132679230719905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 262559576908081911794345653 24614960335132679230719905)
        ·
          refine ⟨18461220251349509423039929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24614960335132679230719905 18461220251349509423039929)
          ·
            refine ⟨13845915188512132067279947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18461220251349509423039929 13845915188512132067279947)
            ·
              refine ⟨20768872782768198100919921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13845915188512132067279947 20768872782768198100919921)
              ·
                refine ⟨15576654587076148575689941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20768872782768198100919921 15576654587076148575689941)
                ·
                  refine ⟨365077841884597232242733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15576654587076148575689941 365077841884597232242733)
                  ·
                    rfl

theorem cell23_6398879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 7].length) (baseStart_6398879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398879 prefixEnd_6398879 := by exact prefixLift 6398879
  have htrace : WordTrace (prefixWord ++ tailWord_6398879) baseStart_6398879 baseEnd_6398879 := by
    simpa [prefixWord, tailWord_6398879, baseEnd_6398879] using wordTrace_append hprefix tailTrace_6398879
  have hstable : (prefixWord ++ tailWord_6398879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398879).length < 2 ^ (prefixWord ++ tailWord_6398879).sum := by decide
  have hdescent : baseEnd_6398879 < baseStart_6398879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398892 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 1, 7]
def baseStart_6398892 : Nat := 118140960795 + 6398892 * 2 ^ 59
def prefixEnd_6398892 : Nat := 4983230072969 + 3 ^ 40 * 6398892 * 2
def baseEnd_6398892 : Nat := 1095235750736627846440679

theorem tailTrace_6398892 : CollatzResearch.WordTrace tailWord_6398892 prefixEnd_6398892 1095235750736627846440679 := by
  unfold tailWord_6398892
  simp only [CollatzResearch.WordTrace]
  refine ⟨116693382366957301296487465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155591176489276401728649953 116693382366957301296487465)
  ·
    refine ⟨87520036775217975972365599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116693382366957301296487465 87520036775217975972365599)
    ·
      refine ⟨131280055162826963958548399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87520036775217975972365599 131280055162826963958548399)
      ·
        refine ⟨196920082744240445937822599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131280055162826963958548399 196920082744240445937822599)
        ·
          refine ⟨295380124116360668906733899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196920082744240445937822599 295380124116360668906733899)
          ·
            refine ⟨443070186174541003360100849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295380124116360668906733899 443070186174541003360100849)
            ·
              refine ⟨332302639630905752520075637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443070186174541003360100849 332302639630905752520075637)
              ·
                refine ⟨31153372465397414298757091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 332302639630905752520075637 31153372465397414298757091)
                ·
                  refine ⟨46730058698096121448135637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31153372465397414298757091 46730058698096121448135637)
                  ·
                    refine ⟨1095235750736627846440679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46730058698096121448135637 1095235750736627846440679)
                    ·
                      rfl

theorem cell23_6398892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_6398892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398892 prefixEnd_6398892 := by exact prefixLift 6398892
  have htrace : WordTrace (prefixWord ++ tailWord_6398892) baseStart_6398892 baseEnd_6398892 := by
    simpa [prefixWord, tailWord_6398892, baseEnd_6398892] using wordTrace_append hprefix tailTrace_6398892
  have hstable : (prefixWord ++ tailWord_6398892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398892).length < 2 ^ (prefixWord ++ tailWord_6398892).sum := by decide
  have hdescent : baseEnd_6398892 < baseStart_6398892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398899 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 1, 7, 2]
def baseStart_6398899 : Nat := 118140960795 + 6398899 * 2 ^ 59
def prefixEnd_6398899 : Nat := 4983230072969 + 3 ^ 40 * 6398899 * 2
def baseEnd_6398899 : Nat := 3285710846574465011934505

theorem tailTrace_6398899 : CollatzResearch.WordTrace tailWord_6398899 prefixEnd_6398899 3285710846574465011934505 := by
  unfold tailWord_6398899
  simp only [CollatzResearch.WordTrace]
  refine ⟨233387020044889242788479751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155591346696592828525653167 233387020044889242788479751)
  ·
    refine ⟨350080530067333864182719627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233387020044889242788479751 350080530067333864182719627)
    ·
      refine ⟨525120795101000796274079441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350080530067333864182719627 525120795101000796274079441)
      ·
        refine ⟨393840596325750597205559581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 525120795101000796274079441 393840596325750597205559581)
        ·
          refine ⟨147690223622156473952084843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 393840596325750597205559581 147690223622156473952084843)
          ·
            refine ⟨221535335433234710928127265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147690223622156473952084843 221535335433234710928127265)
            ·
              refine ⟨166151501574926033196095449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221535335433234710928127265 166151501574926033196095449)
              ·
                refine ⟨124613626181194524897071587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166151501574926033196095449 124613626181194524897071587)
                ·
                  refine ⟨186920439271791787345607381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124613626181194524897071587 186920439271791787345607381)
                  ·
                    refine ⟨4380947795432620015912673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 186920439271791787345607381 4380947795432620015912673)
                    ·
                      refine ⟨3285710846574465011934505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4380947795432620015912673 3285710846574465011934505)
                      ·
                        rfl

theorem cell23_6398899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 7, 2].length) (baseStart_6398899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398899 prefixEnd_6398899 := by exact prefixLift 6398899
  have htrace : WordTrace (prefixWord ++ tailWord_6398899) baseStart_6398899 baseEnd_6398899 := by
    simpa [prefixWord, tailWord_6398899, baseEnd_6398899] using wordTrace_append hprefix tailTrace_6398899
  have hstable : (prefixWord ++ tailWord_6398899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398899).length < 2 ^ (prefixWord ++ tailWord_6398899).sum := by decide
  have hdescent : baseEnd_6398899 < baseStart_6398899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398964 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 7]
def baseStart_6398964 : Nat := 118140960795 + 6398964 * 2 ^ 59
def prefixEnd_6398964 : Nat := 4983230072969 + 3 ^ 40 * 6398964 * 2
def baseEnd_6398964 : Nat := 365082691424111917513523

theorem tailTrace_6398964 : CollatzResearch.WordTrace tailWord_6398964 prefixEnd_6398964 365082691424111917513523 := by
  unfold tailWord_6398964
  simp only [CollatzResearch.WordTrace]
  refine ⟨116694695394826879444797973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155592927193102505926397297 116694695394826879444797973)
  ·
    refine ⟨5470063846632509973974905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 116694695394826879444797973 5470063846632509973974905)
    ·
      refine ⟨4102547884974382480481179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5470063846632509973974905 4102547884974382480481179)
      ·
        refine ⟨6153821827461573720721769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4102547884974382480481179 6153821827461573720721769)
        ·
          refine ⟨4615366370596180290541327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6153821827461573720721769 4615366370596180290541327)
          ·
            refine ⟨6923049555894270435811991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4615366370596180290541327 6923049555894270435811991)
            ·
              refine ⟨10384574333841405653717987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6923049555894270435811991 10384574333841405653717987)
              ·
                refine ⟨15576861500762108480576981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10384574333841405653717987 15576861500762108480576981)
                ·
                  refine ⟨365082691424111917513523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15576861500762108480576981 365082691424111917513523)
                  ·
                    rfl

theorem cell23_6398964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_6398964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398964 prefixEnd_6398964 := by exact prefixLift 6398964
  have htrace : WordTrace (prefixWord ++ tailWord_6398964) baseStart_6398964 baseEnd_6398964 := by
    simpa [prefixWord, tailWord_6398964, baseEnd_6398964] using wordTrace_append hprefix tailTrace_6398964
  have hstable : (prefixWord ++ tailWord_6398964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398964).length < 2 ^ (prefixWord ++ tailWord_6398964).sum := by decide
  have hdescent : baseEnd_6398964 < baseStart_6398964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398969 : List Nat := [1, 2, 1, 3, 1, 3, 2, 4, 6]
def baseStart_6398969 : Nat := 118140960795 + 6398969 * 2 ^ 59
def prefixEnd_6398969 : Nat := 4983230072969 + 3 ^ 40 * 6398969 * 2
def baseEnd_6398969 : Nat := 365082976691142193117687

theorem tailTrace_6398969 : CollatzResearch.WordTrace tailWord_6398969 prefixEnd_6398969 365082976691142193117687 := by
  unfold tailWord_6398969
  simp only [CollatzResearch.WordTrace]
  refine ⟨233389573154635644743527961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155593048769757096495685307 233389573154635644743527961)
  ·
    refine ⟨175042179865976733557645971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233389573154635644743527961 175042179865976733557645971)
    ·
      refine ⟨262563269798965100336468957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175042179865976733557645971 262563269798965100336468957)
      ·
        refine ⟨98461226174611912626175859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262563269798965100336468957 98461226174611912626175859)
        ·
          refine ⟨147691839261917868939263789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98461226174611912626175859 147691839261917868939263789)
          ·
            refine ⟨55384439723219200852223921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147691839261917868939263789 55384439723219200852223921)
            ·
              refine ⟨41538329792414400639167941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55384439723219200852223921 41538329792414400639167941)
              ·
                refine ⟨7788436836077700119843989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41538329792414400639167941 7788436836077700119843989)
                ·
                  refine ⟨365082976691142193117687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7788436836077700119843989 365082976691142193117687)
                  ·
                    rfl

theorem cell23_6398969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 6].length) (baseStart_6398969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398969 prefixEnd_6398969 := by exact prefixLift 6398969
  have htrace : WordTrace (prefixWord ++ tailWord_6398969) baseStart_6398969 baseEnd_6398969 := by
    simpa [prefixWord, tailWord_6398969, baseEnd_6398969] using wordTrace_append hprefix tailTrace_6398969
  have hstable : (prefixWord ++ tailWord_6398969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398969).length < 2 ^ (prefixWord ++ tailWord_6398969).sum := by decide
  have hdescent : baseEnd_6398969 < baseStart_6398969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6398986 : List Nat := [3, 1, 2, 2, 3, 2, 1, 3, 6]
def baseStart_6398986 : Nat := 118140960795 + 6398986 * 2 ^ 59
def prefixEnd_6398986 : Nat := 4983230072969 + 3 ^ 40 * 6398986 * 2
def baseEnd_6398986 : Nat := 365083946599045130171845

theorem tailTrace_6398986 : CollatzResearch.WordTrace tailWord_6398986 prefixEnd_6398986 365083946599045130171845 := by
  unfold tailWord_6398986
  simp only [CollatzResearch.WordTrace]
  refine ⟨58347548298893514161724203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155593462130382704431264541 58347548298893514161724203)
  ·
    refine ⟨87521322448340271242586305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58347548298893514161724203 87521322448340271242586305)
    ·
      refine ⟨65640991836255203431939729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87521322448340271242586305 65640991836255203431939729)
      ·
        refine ⟨49230743877191402573954797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65640991836255203431939729 49230743877191402573954797)
        ·
          refine ⟨18461528953946775965233049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49230743877191402573954797 18461528953946775965233049)
          ·
            refine ⟨13846146715460081973924787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18461528953946775965233049 13846146715460081973924787)
            ·
              refine ⟨20769220073190122960887181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13846146715460081973924787 20769220073190122960887181)
              ·
                refine ⟨7788457527446296110332693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20769220073190122960887181 7788457527446296110332693)
                ·
                  refine ⟨365083946599045130171845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7788457527446296110332693 365083946599045130171845)
                  ·
                    rfl

theorem cell23_6398986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 6].length) (baseStart_6398986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6398986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6398986 prefixEnd_6398986 := by exact prefixLift 6398986
  have htrace : WordTrace (prefixWord ++ tailWord_6398986) baseStart_6398986 baseEnd_6398986 := by
    simpa [prefixWord, tailWord_6398986, baseEnd_6398986] using wordTrace_append hprefix tailTrace_6398986
  have hstable : (prefixWord ++ tailWord_6398986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6398986).length < 2 ^ (prefixWord ++ tailWord_6398986).sum := by decide
  have hdescent : baseEnd_6398986 < baseStart_6398986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6398986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399029 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 5, 6]
def baseStart_6399029 : Nat := 118140960795 + 6399029 * 2 ^ 59
def prefixEnd_6399029 : Nat := 4983230072969 + 3 ^ 40 * 6399029 * 2
def baseEnd_6399029 : Nat := 1095259199686516501102969

theorem tailTrace_6399029 : CollatzResearch.WordTrace tailWord_6399029 prefixEnd_6399029 1095259199686516501102969 := by
  unfold tailWord_6399029
  simp only [CollatzResearch.WordTrace]
  refine ⟨233391761534418274990712141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155594507689612183327141427 233391761534418274990712141)
  ·
    refine ⟨87521910575406853121517053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233391761534418274990712141 87521910575406853121517053)
    ·
      refine ⟨32820716465777569920568895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87521910575406853121517053 32820716465777569920568895)
      ·
        refine ⟨49231074698666354880853343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32820716465777569920568895 49231074698666354880853343)
        ·
          refine ⟨73846612047999532321280015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49231074698666354880853343 73846612047999532321280015)
          ·
            refine ⟨110769918071999298481920023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73846612047999532321280015 110769918071999298481920023)
            ·
              refine ⟨166154877107998947722880035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110769918071999298481920023 166154877107998947722880035)
              ·
                refine ⟨249232315661998421584320053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166154877107998947722880035 249232315661998421584320053)
                ·
                  refine ⟨23365529593312352023530005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 249232315661998421584320053 23365529593312352023530005)
                  ·
                    refine ⟨1095259199686516501102969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23365529593312352023530005 1095259199686516501102969)
                    ·
                      rfl

theorem cell23_6399029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_6399029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399029 prefixEnd_6399029 := by exact prefixLift 6399029
  have htrace : WordTrace (prefixWord ++ tailWord_6399029) baseStart_6399029 baseEnd_6399029 := by
    simpa [prefixWord, tailWord_6399029, baseEnd_6399029] using wordTrace_append hprefix tailTrace_6399029
  have hstable : (prefixWord ++ tailWord_6399029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399029).length < 2 ^ (prefixWord ++ tailWord_6399029).sum := by decide
  have hdescent : baseEnd_6399029 < baseStart_6399029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399036 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_6399036 : Nat := 118140960795 + 6399036 * 2 ^ 59
def prefixEnd_6399036 : Nat := 4983230072969 + 3 ^ 40 * 6399036 * 2
def baseEnd_6399036 : Nat := 3285781193424130975921375

theorem tailTrace_6399036 : CollatzResearch.WordTrace tailWord_6399036 prefixEnd_6399036 3285781193424130975921375 := by
  unfold tailWord_6399036
  simp only [CollatzResearch.WordTrace]
  refine ⟨116696008422696457593108481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155594677896928610124144641 116696008422696457593108481)
  ·
    refine ⟨87522006317022343194831361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116696008422696457593108481 87522006317022343194831361)
    ·
      refine ⟨65641504737766757396123521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87522006317022343194831361 65641504737766757396123521)
      ·
        refine ⟨49231128553325068047092641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65641504737766757396123521 49231128553325068047092641)
        ·
          refine ⟨36923346414993801035319481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49231128553325068047092641 36923346414993801035319481)
          ·
            refine ⟨27692509811245350776489611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36923346414993801035319481 27692509811245350776489611)
            ·
              refine ⟨41538764716868026164734417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27692509811245350776489611 41538764716868026164734417)
              ·
                refine ⟨31154073537651019623550813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41538764716868026164734417 31154073537651019623550813)
                ·
                  refine ⟨11682777576619132358831555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31154073537651019623550813 11682777576619132358831555)
                  ·
                    refine ⟨17524166364928698538247333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11682777576619132358831555 17524166364928698538247333)
                    ·
                      refine ⟨3285781193424130975921375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17524166364928698538247333 3285781193424130975921375)
                      ·
                        rfl

theorem cell23_6399036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_6399036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399036 prefixEnd_6399036 := by exact prefixLift 6399036
  have htrace : WordTrace (prefixWord ++ tailWord_6399036) baseStart_6399036 baseEnd_6399036 := by
    simpa [prefixWord, tailWord_6399036, baseEnd_6399036] using wordTrace_append hprefix tailTrace_6399036
  have hstable : (prefixWord ++ tailWord_6399036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399036).length < 2 ^ (prefixWord ++ tailWord_6399036).sum := by decide
  have hdescent : baseEnd_6399036 < baseStart_6399036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399039 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 5]
def baseStart_6399039 : Nat := 118140960795 + 6399039 * 2 ^ 59
def prefixEnd_6399039 : Nat := 4983230072969 + 3 ^ 40 * 6399039 * 2
def baseEnd_6399039 : Nat := 3285782733866094464183861

theorem tailTrace_6399039 : CollatzResearch.WordTrace tailWord_6399039 prefixEnd_6399039 3285782733866094464183861 := by
  unfold tailWord_6399039
  simp only [CollatzResearch.WordTrace]
  refine ⟨233392126264382046698576171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155594750842921364465717447 233392126264382046698576171)
  ·
    refine ⟨350088189396573070047864257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233392126264382046698576171 350088189396573070047864257)
    ·
      refine ⟨262566142047429802535898193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350088189396573070047864257 262566142047429802535898193)
      ·
        refine ⟨196924606535572351901923645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262566142047429802535898193 196924606535572351901923645)
        ·
          refine ⟨73846727450839631963221367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196924606535572351901923645 73846727450839631963221367)
          ·
            refine ⟨110770091176259447944832051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73846727450839631963221367 110770091176259447944832051)
            ·
              refine ⟨166155136764389171917248077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110770091176259447944832051 166155136764389171917248077)
              ·
                refine ⟨62308176286645939468968029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166155136764389171917248077 62308176286645939468968029)
                ·
                  refine ⟨23365566107492227300863011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62308176286645939468968029 23365566107492227300863011)
                  ·
                    refine ⟨35048349161238340951294517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23365566107492227300863011 35048349161238340951294517)
                    ·
                      refine ⟨3285782733866094464183861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35048349161238340951294517 3285782733866094464183861)
                      ·
                        rfl

theorem cell23_6399039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_6399039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399039 prefixEnd_6399039 := by exact prefixLift 6399039
  have htrace : WordTrace (prefixWord ++ tailWord_6399039) baseStart_6399039 baseEnd_6399039 := by
    simpa [prefixWord, tailWord_6399039, baseEnd_6399039] using wordTrace_append hprefix tailTrace_6399039
  have hstable : (prefixWord ++ tailWord_6399039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399039).length < 2 ^ (prefixWord ++ tailWord_6399039).sum := by decide
  have hdescent : baseEnd_6399039 < baseStart_6399039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399053 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_6399053 : Nat := 118140960795 + 6399053 * 2 ^ 59
def prefixEnd_6399053 : Nat := 4983230072969 + 3 ^ 40 * 6399053 * 2
def baseEnd_6399053 : Nat := 3285789922595257409408797

theorem tailTrace_6399053 : CollatzResearch.WordTrace tailWord_6399053 prefixEnd_6399053 3285789922595257409408797 := by
  unfold tailWord_6399053
  simp only [CollatzResearch.WordTrace]
  refine ⟨233392636886331327089585813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155595091257554218059723875 233392636886331327089585813)
  ·
    refine ⟨10940279854046780957324335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 233392636886331327089585813 10940279854046780957324335)
    ·
      refine ⟨16410419781070171435986503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10940279854046780957324335 16410419781070171435986503)
      ·
        refine ⟨24615629671605257153979755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16410419781070171435986503 24615629671605257153979755)
        ·
          refine ⟨36923444507407885730969633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24615629671605257153979755 36923444507407885730969633)
          ·
            refine ⟨27692583380555914298227225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36923444507407885730969633 27692583380555914298227225)
            ·
              refine ⟨20769437535416935723670419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27692583380555914298227225 20769437535416935723670419)
              ·
                refine ⟨31154156303125403585505629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20769437535416935723670419 31154156303125403585505629)
                ·
                  refine ⟨11682808613672026344564611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31154156303125403585505629 11682808613672026344564611)
                  ·
                    refine ⟨17524212920508039516846917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11682808613672026344564611 17524212920508039516846917)
                    ·
                      refine ⟨3285789922595257409408797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17524212920508039516846917 3285789922595257409408797)
                      ·
                        rfl

theorem cell23_6399053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_6399053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399053 prefixEnd_6399053 := by exact prefixLift 6399053
  have htrace : WordTrace (prefixWord ++ tailWord_6399053) baseStart_6399053 baseEnd_6399053 := by
    simpa [prefixWord, tailWord_6399053, baseEnd_6399053] using wordTrace_append hprefix tailTrace_6399053
  have hstable : (prefixWord ++ tailWord_6399053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399053).length < 2 ^ (prefixWord ++ tailWord_6399053).sum := by decide
  have hdescent : baseEnd_6399053 < baseStart_6399053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399080 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 4, 4]
def baseStart_6399080 : Nat := 118140960795 + 6399080 * 2 ^ 59
def prefixEnd_6399080 : Nat := 4983230072969 + 3 ^ 40 * 6399080 * 2
def baseEnd_6399080 : Nat := 1095267928857642934590391

theorem tailTrace_6399080 : CollatzResearch.WordTrace tailWord_6399080 prefixEnd_6399080 1095267928857642934590391 := by
  unfold tailWord_6399080
  simp only [CollatzResearch.WordTrace]
  refine ⟨116696810828616755350409347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155595747771489007133879129 116696810828616755350409347)
  ·
    refine ⟨175045216242925133025614021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116696810828616755350409347 175045216242925133025614021)
    ·
      refine ⟨32820978045548462442302629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175045216242925133025614021 32820978045548462442302629)
      ·
        refine ⟨6153933383540336707931743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32820978045548462442302629 6153933383540336707931743)
        ·
          refine ⟨9230900075310505061897615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6153933383540336707931743 9230900075310505061897615)
          ·
            refine ⟨13846350112965757592846423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9230900075310505061897615 13846350112965757592846423)
            ·
              refine ⟨20769525169448636389269635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13846350112965757592846423 20769525169448636389269635)
              ·
                refine ⟨31154287754172954583904453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20769525169448636389269635 31154287754172954583904453)
                ·
                  refine ⟨5841428953907428984482085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31154287754172954583904453 5841428953907428984482085)
                  ·
                    refine ⟨1095267928857642934590391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5841428953907428984482085 1095267928857642934590391)
                    ·
                      rfl

theorem cell23_6399080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_6399080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399080 prefixEnd_6399080 := by exact prefixLift 6399080
  have htrace : WordTrace (prefixWord ++ tailWord_6399080) baseStart_6399080 baseEnd_6399080 := by
    simpa [prefixWord, tailWord_6399080, baseEnd_6399080] using wordTrace_append hprefix tailTrace_6399080
  have hstable : (prefixWord ++ tailWord_6399080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399080).length < 2 ^ (prefixWord ++ tailWord_6399080).sum := by decide
  have hdescent : baseEnd_6399080 < baseStart_6399080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399089 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 2, 7]
def baseStart_6399089 : Nat := 118140960795 + 6399089 * 2 ^ 59
def prefixEnd_6399089 : Nat := 4983230072969 + 3 ^ 40 * 6399089 * 2
def baseEnd_6399089 : Nat := 1095269469299606422852877

theorem tailTrace_6399089 : CollatzResearch.WordTrace tailWord_6399089 prefixEnd_6399089 1095269469299606422852877 := by
  unfold tailWord_6399089
  simp only [CollatzResearch.WordTrace]
  refine ⟨233393949914200905237896321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155595966609467270158597547 233393949914200905237896321)
  ·
    refine ⟨175045462435650678928422241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233393949914200905237896321 175045462435650678928422241)
    ·
      refine ⟨131284096826738009196316681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175045462435650678928422241 131284096826738009196316681)
      ·
        refine ⟨98463072620053506897237511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131284096826738009196316681 98463072620053506897237511)
        ·
          refine ⟨147694608930080260345856267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98463072620053506897237511 147694608930080260345856267)
          ·
            refine ⟨221541913395120390518784401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147694608930080260345856267 221541913395120390518784401)
            ·
              refine ⟨166156435046340292889088301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221541913395120390518784401 166156435046340292889088301)
              ·
                refine ⟨62308663142377609833408113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166156435046340292889088301 62308663142377609833408113)
                ·
                  refine ⟨46731497356783207375056085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62308663142377609833408113 46731497356783207375056085)
                  ·
                    refine ⟨1095269469299606422852877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46731497356783207375056085 1095269469299606422852877)
                    ·
                      rfl

theorem cell23_6399089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_6399089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399089 prefixEnd_6399089 := by exact prefixLift 6399089
  have htrace : WordTrace (prefixWord ++ tailWord_6399089) baseStart_6399089 baseEnd_6399089 := by
    simpa [prefixWord, tailWord_6399089, baseEnd_6399089] using wordTrace_append hprefix tailTrace_6399089
  have hstable : (prefixWord ++ tailWord_6399089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399089).length < 2 ^ (prefixWord ++ tailWord_6399089).sum := by decide
  have hdescent : baseEnd_6399089 < baseStart_6399089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399099 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 5]
def baseStart_6399099 : Nat := 118140960795 + 6399099 * 2 ^ 59
def prefixEnd_6399099 : Nat := 4983230072969 + 3 ^ 40 * 6399099 * 2
def baseEnd_6399099 : Nat := 3285813542705364229433585

theorem tailTrace_6399099 : CollatzResearch.WordTrace tailWord_6399099 prefixEnd_6399099 3285813542705364229433585 := by
  unfold tailWord_6399099
  simp only [CollatzResearch.WordTrace]
  refine ⟨233394314644164676945760351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155596209762776451297173567 233394314644164676945760351)
  ·
    refine ⟨350091471966247015418640527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233394314644164676945760351 350091471966247015418640527)
    ·
      refine ⟨525137207949370523127960791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350091471966247015418640527 525137207949370523127960791)
      ·
        refine ⟨787705811924055784691941187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525137207949370523127960791 787705811924055784691941187)
        ·
          refine ⟨1181558717886083677037911781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787705811924055784691941187 1181558717886083677037911781)
          ·
            refine ⟨221542259603640689444608459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1181558717886083677037911781 221542259603640689444608459)
            ·
              refine ⟨332313389405461034166912689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221542259603640689444608459 332313389405461034166912689)
              ·
                refine ⟨249235042054095775625184517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 332313389405461034166912689 249235042054095775625184517)
                ·
                  refine ⟨46731570385142957929722097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 249235042054095775625184517 46731570385142957929722097)
                  ·
                    refine ⟨35048677788857218447291573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46731570385142957929722097 35048677788857218447291573)
                    ·
                      refine ⟨3285813542705364229433585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35048677788857218447291573 3285813542705364229433585)
                      ·
                        rfl

theorem cell23_6399099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 5].length) (baseStart_6399099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399099 prefixEnd_6399099 := by exact prefixLift 6399099
  have htrace : WordTrace (prefixWord ++ tailWord_6399099) baseStart_6399099 baseEnd_6399099 := by
    simpa [prefixWord, tailWord_6399099, baseEnd_6399099] using wordTrace_append hprefix tailTrace_6399099
  have hstable : (prefixWord ++ tailWord_6399099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399099).length < 2 ^ (prefixWord ++ tailWord_6399099).sum := by decide
  have hdescent : baseEnd_6399099 < baseStart_6399099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399200 : List Nat := [2, 1, 1, 3, 1, 4, 4, 2, 5]
def baseStart_6399200 : Nat := 118140960795 + 6399200 * 2 ^ 59
def prefixEnd_6399200 : Nat := 4983230072969 + 3 ^ 40 * 6399200 * 2
def baseEnd_6399200 : Nat := 365096156027940926030069

theorem tailTrace_6399200 : CollatzResearch.WordTrace tailWord_6399200 prefixEnd_6399200 365096156027940926030069 := by
  unfold tailWord_6399200
  simp only [CollatzResearch.WordTrace]
  refine ⟨116698999208399385597593527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155598665611199180796791369 116698999208399385597593527)
  ·
    refine ⟨175048498812599078396390291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116698999208399385597593527 175048498812599078396390291)
    ·
      refine ⟨262572748218898617594585437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175048498812599078396390291 262572748218898617594585437)
      ·
        refine ⟨98464780582086981597969539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262572748218898617594585437 98464780582086981597969539)
        ·
          refine ⟨147697170873130472396954309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98464780582086981597969539 147697170873130472396954309)
          ·
            refine ⟨27693219538711963574428933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147697170873130472396954309 27693219538711963574428933)
            ·
              refine ⟨5192478663508493170205425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27693219538711963574428933 5192478663508493170205425)
              ·
                refine ⟨3894358997631369877654069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5192478663508493170205425 3894358997631369877654069)
                ·
                  refine ⟨365096156027940926030069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3894358997631369877654069 365096156027940926030069)
                  ·
                    rfl

theorem cell23_6399200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 5].length) (baseStart_6399200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399200 prefixEnd_6399200 := by exact prefixLift 6399200
  have htrace : WordTrace (prefixWord ++ tailWord_6399200) baseStart_6399200 baseEnd_6399200 := by
    simpa [prefixWord, tailWord_6399200, baseEnd_6399200] using wordTrace_append hprefix tailTrace_6399200
  have hstable : (prefixWord ++ tailWord_6399200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399200).length < 2 ^ (prefixWord ++ tailWord_6399200).sum := by decide
  have hdescent : baseEnd_6399200 < baseStart_6399200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399230 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_6399230 : Nat := 118140960795 + 6399230 * 2 ^ 59
def prefixEnd_6399230 : Nat := 4983230072969 + 3 ^ 40 * 6399230 * 2
def baseEnd_6399230 : Nat := 1095293602890367738965161

theorem tailTrace_6399230 : CollatzResearch.WordTrace tailWord_6399230 prefixEnd_6399230 1095293602890367738965161 := by
  unfold tailWord_6399230
  simp only [CollatzResearch.WordTrace]
  refine ⟨29174886575836260789847393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155599395071126724212519429 29174886575836260789847393)
  ·
    refine ⟨21881164931877195592385545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29174886575836260789847393 21881164931877195592385545)
    ·
      refine ⟨16410873698907896694289159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21881164931877195592385545 16410873698907896694289159)
      ·
        refine ⟨24616310548361845041433739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16410873698907896694289159 24616310548361845041433739)
        ·
          refine ⟨36924465822542767562150609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24616310548361845041433739 36924465822542767562150609)
          ·
            refine ⟨27693349366907075671612957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36924465822542767562150609 27693349366907075671612957)
            ·
              refine ⟨10385006012590153376854859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27693349366907075671612957 10385006012590153376854859)
              ·
                refine ⟨15577509018885230065282289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10385006012590153376854859 15577509018885230065282289)
                ·
                  refine ⟨11683131764163922548961717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15577509018885230065282289 11683131764163922548961717)
                  ·
                    refine ⟨1095293602890367738965161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11683131764163922548961717 1095293602890367738965161)
                    ·
                      rfl

theorem cell23_6399230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_6399230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399230 prefixEnd_6399230 := by exact prefixLift 6399230
  have htrace : WordTrace (prefixWord ++ tailWord_6399230) baseStart_6399230 baseEnd_6399230 := by
    simpa [prefixWord, tailWord_6399230, baseEnd_6399230] using wordTrace_append hprefix tailTrace_6399230
  have hstable : (prefixWord ++ tailWord_6399230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399230).length < 2 ^ (prefixWord ++ tailWord_6399230).sum := by decide
  have hdescent : baseEnd_6399230 < baseStart_6399230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399233 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_6399233 : Nat := 118140960795 + 6399233 * 2 ^ 59
def prefixEnd_6399233 : Nat := 4983230072969 + 3 ^ 40 * 6399233 * 2
def baseEnd_6399233 : Nat := 3285882349113066705157969

theorem tailTrace_6399233 : CollatzResearch.WordTrace tailWord_6399233 prefixEnd_6399233 3285882349113066705157969 := by
  unfold tailWord_6399233
  simp only [CollatzResearch.WordTrace]
  refine ⟨233399202025679217831138353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155599468017119478554092235 233399202025679217831138353)
  ·
    refine ⟨175049401519259413373353765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233399202025679217831138353 175049401519259413373353765)
    ·
      refine ⟨32821762784861140007503831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175049401519259413373353765 32821762784861140007503831)
      ·
        refine ⟨49232644177291710011255747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32821762784861140007503831 49232644177291710011255747)
        ·
          refine ⟨73848966265937565016883621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49232644177291710011255747 73848966265937565016883621)
          ·
            refine ⟨13846681174863293440665679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73848966265937565016883621 13846681174863293440665679)
            ·
              refine ⟨20770021762294940160998519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13846681174863293440665679 20770021762294940160998519)
              ·
                refine ⟨31155032643442410241497779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20770021762294940160998519 31155032643442410241497779)
                ·
                  refine ⟨46732548965163615362246669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31155032643442410241497779 46732548965163615362246669)
                  ·
                    refine ⟨17524705861936355760842501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46732548965163615362246669 17524705861936355760842501)
                    ·
                      refine ⟨3285882349113066705157969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17524705861936355760842501 3285882349113066705157969)
                      ·
                        rfl

theorem cell23_6399233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_6399233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399233 prefixEnd_6399233 := by exact prefixLift 6399233
  have htrace : WordTrace (prefixWord ++ tailWord_6399233) baseStart_6399233 baseEnd_6399233 := by
    simpa [prefixWord, tailWord_6399233, baseEnd_6399233] using wordTrace_append hprefix tailTrace_6399233
  have hstable : (prefixWord ++ tailWord_6399233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399233).length < 2 ^ (prefixWord ++ tailWord_6399233).sum := by decide
  have hdescent : baseEnd_6399233 < baseStart_6399233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399253 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 4, 2, 3]
def baseStart_6399253 : Nat := 118140960795 + 6399253 * 2 ^ 59
def prefixEnd_6399253 : Nat := 4983230072969 + 3 ^ 40 * 6399253 * 2
def baseEnd_6399253 : Nat := 3285892618726156626907877

theorem tailTrace_6399253 : CollatzResearch.WordTrace tailWord_6399253 prefixEnd_6399253 3285892618726156626907877 := by
  unfold tailWord_6399253
  simp only [CollatzResearch.WordTrace]
  refine ⟨233399931485606761246866413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155599954323737840831244275 233399931485606761246866413)
  ·
    refine ⟨87524974307102535467574905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233399931485606761246866413 87524974307102535467574905)
    ·
      refine ⟨65643730730326901600681179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87524974307102535467574905 65643730730326901600681179)
      ·
        refine ⟨98465596095490352401021769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65643730730326901600681179 98465596095490352401021769)
        ·
          refine ⟨73849197071617764300766327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98465596095490352401021769 73849197071617764300766327)
          ·
            refine ⟨110773795607426646451149491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73849197071617764300766327 110773795607426646451149491)
            ·
              refine ⟨166160693411139969676724237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110773795607426646451149491 166160693411139969676724237)
              ·
                refine ⟨62310260029177488628771589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166160693411139969676724237 62310260029177488628771589)
                ·
                  refine ⟨11683173755470779117894673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62310260029177488628771589 11683173755470779117894673)
                  ·
                    refine ⟨8762380316603084338421005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11683173755470779117894673 8762380316603084338421005)
                    ·
                      refine ⟨3285892618726156626907877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8762380316603084338421005 3285892618726156626907877)
                      ·
                        rfl

theorem cell23_6399253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_6399253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399253 prefixEnd_6399253 := by exact prefixLift 6399253
  have htrace : WordTrace (prefixWord ++ tailWord_6399253) baseStart_6399253 baseEnd_6399253 := by
    simpa [prefixWord, tailWord_6399253, baseEnd_6399253] using wordTrace_append hprefix tailTrace_6399253
  have hstable : (prefixWord ++ tailWord_6399253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399253).length < 2 ^ (prefixWord ++ tailWord_6399253).sum := by decide
  have hdescent : baseEnd_6399253 < baseStart_6399253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399276 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 6]
def baseStart_6399276 : Nat := 118140960795 + 6399276 * 2 ^ 59
def prefixEnd_6399276 : Nat := 4983230072969 + 3 ^ 40 * 6399276 * 2
def baseEnd_6399276 : Nat := 3285904428781210036920271

theorem tailTrace_6399276 : CollatzResearch.WordTrace tailWord_6399276 prefixEnd_6399276 3285904428781210036920271 := by
  unfold tailWord_6399276
  simp only [CollatzResearch.WordTrace]
  refine ⟨116700385182261718087476841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155600513576348957449969121 116700385182261718087476841)
  ·
    refine ⟨87525288886696288565607631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116700385182261718087476841 87525288886696288565607631)
    ·
      refine ⟨131287933330044432848411447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87525288886696288565607631 131287933330044432848411447)
      ·
        refine ⟨196931899995066649272617171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131287933330044432848411447 196931899995066649272617171)
        ·
          refine ⟨295397849992599973908925757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196931899995066649272617171 295397849992599973908925757)
          ·
            refine ⟨110774193747224990215847159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295397849992599973908925757 110774193747224990215847159)
            ·
              refine ⟨166161290620837485323770739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110774193747224990215847159 166161290620837485323770739)
              ·
                refine ⟨249241935931256227985656109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166161290620837485323770739 249241935931256227985656109)
                ·
                  refine ⟨93465725974221085494621041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249241935931256227985656109 93465725974221085494621041)
                  ·
                    refine ⟨70099294480665814120965781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93465725974221085494621041 70099294480665814120965781)
                    ·
                      refine ⟨3285904428781210036920271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70099294480665814120965781 3285904428781210036920271)
                      ·
                        rfl

theorem cell23_6399276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_6399276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399276 prefixEnd_6399276 := by exact prefixLift 6399276
  have htrace : WordTrace (prefixWord ++ tailWord_6399276) baseStart_6399276 baseEnd_6399276 := by
    simpa [prefixWord, tailWord_6399276, baseEnd_6399276] using wordTrace_append hprefix tailTrace_6399276
  have hstable : (prefixWord ++ tailWord_6399276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399276).length < 2 ^ (prefixWord ++ tailWord_6399276).sum := by decide
  have hdescent : baseEnd_6399276 < baseStart_6399276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399277 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_6399277 : Nat := 118140960795 + 6399277 * 2 ^ 59
def prefixEnd_6399277 : Nat := 4983230072969 + 3 ^ 40 * 6399277 * 2
def baseEnd_6399277 : Nat := 1095301647420621511002589

theorem tailTrace_6399277 : CollatzResearch.WordTrace tailWord_6399277 prefixEnd_6399277 1095301647420621511002589 := by
  unfold tailWord_6399277
  simp only [CollatzResearch.WordTrace]
  refine ⟨233400806837519813345740085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155600537891679875563826723 233400806837519813345740085)
  ·
    refine ⟨21881325641017482501163133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 233400806837519813345740085 21881325641017482501163133)
    ·
      refine ⟨8205497115381555937936175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21881325641017482501163133 8205497115381555937936175)
      ·
        refine ⟨12308245673072333906904263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8205497115381555937936175 12308245673072333906904263)
        ·
          refine ⟨18462368509608500860356395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12308245673072333906904263 18462368509608500860356395)
          ·
            refine ⟨27693552764412751290534593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18462368509608500860356395 27693552764412751290534593)
            ·
              refine ⟨20770164573309563467900945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27693552764412751290534593 20770164573309563467900945)
              ·
                refine ⟨15577623429982172600925709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20770164573309563467900945 15577623429982172600925709)
                ·
                  refine ⟨5841608786243314725347141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15577623429982172600925709 5841608786243314725347141)
                  ·
                    refine ⟨1095301647420621511002589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5841608786243314725347141 1095301647420621511002589)
                    ·
                      rfl

theorem cell23_6399277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_6399277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399277 prefixEnd_6399277 := by exact prefixLift 6399277
  have htrace : WordTrace (prefixWord ++ tailWord_6399277) baseStart_6399277 baseEnd_6399277 := by
    simpa [prefixWord, tailWord_6399277, baseEnd_6399277] using wordTrace_append hprefix tailTrace_6399277
  have hstable : (prefixWord ++ tailWord_6399277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399277).length < 2 ^ (prefixWord ++ tailWord_6399277).sum := by decide
  have hdescent : baseEnd_6399277 < baseStart_6399277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399317 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 3, 1, 3]
def baseStart_6399317 : Nat := 118140960795 + 6399317 * 2 ^ 59
def prefixEnd_6399317 : Nat := 4983230072969 + 3 ^ 40 * 6399317 * 2
def baseEnd_6399317 : Nat := 3285925481488044376507583

theorem tailTrace_6399317 : CollatzResearch.WordTrace tailWord_6399317 prefixEnd_6399317 3285925481488044376507583 := by
  unfold tailWord_6399317
  simp only [CollatzResearch.WordTrace]
  refine ⟨233402265757374900177196205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155601510504916600118130803 233402265757374900177196205)
  ·
    refine ⟨87525849659015587566448577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233402265757374900177196205 87525849659015587566448577)
    ·
      refine ⟨65644387244261690674836433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87525849659015587566448577 65644387244261690674836433)
      ·
        refine ⟨49233290433196268006127325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65644387244261690674836433 49233290433196268006127325)
        ·
          refine ⟨18462483912448600502297747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49233290433196268006127325 18462483912448600502297747)
          ·
            refine ⟨27693725868672900753446621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18462483912448600502297747 27693725868672900753446621)
            ·
              refine ⟨10385147200752337782542483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27693725868672900753446621 10385147200752337782542483)
              ·
                refine ⟨15577720801128506673813725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10385147200752337782542483 15577720801128506673813725)
                ·
                  refine ⟨5841645300423190002680147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15577720801128506673813725 5841645300423190002680147)
                  ·
                    refine ⟨8762467950634785004020221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5841645300423190002680147 8762467950634785004020221)
                    ·
                      refine ⟨3285925481488044376507583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8762467950634785004020221 3285925481488044376507583)
                      ·
                        rfl

theorem cell23_6399317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_6399317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399317 prefixEnd_6399317 := by exact prefixLift 6399317
  have htrace : WordTrace (prefixWord ++ tailWord_6399317) baseStart_6399317 baseEnd_6399317 := by
    simpa [prefixWord, tailWord_6399317, baseEnd_6399317] using wordTrace_append hprefix tailTrace_6399317
  have hstable : (prefixWord ++ tailWord_6399317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399317).length < 2 ^ (prefixWord ++ tailWord_6399317).sum := by decide
  have hdescent : baseEnd_6399317 < baseStart_6399317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399333 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 1, 6]
def baseStart_6399333 : Nat := 118140960795 + 6399333 * 2 ^ 59
def prefixEnd_6399333 : Nat := 4983230072969 + 3 ^ 40 * 6399333 * 2
def baseEnd_6399333 : Nat := 1095311232392838771302503

theorem tailTrace_6399333 : CollatzResearch.WordTrace tailWord_6399333 prefixEnd_6399333 1095311232392838771302503 := by
  unfold tailWord_6399333
  simp only [CollatzResearch.WordTrace]
  refine ⟨233402849325316934909778653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155601899550211289939852435 233402849325316934909778653)
  ·
    refine ⟨87526068496993850591166995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233402849325316934909778653 87526068496993850591166995)
    ·
      refine ⟨131289102745490775886750493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87526068496993850591166995 131289102745490775886750493)
      ·
        refine ⟨49233413529559040957531435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131289102745490775886750493 49233413529559040957531435)
        ·
          refine ⟨73850120294338561436297153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49233413529559040957531435 73850120294338561436297153)
          ·
            refine ⟨55387590220753921077222865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73850120294338561436297153 55387590220753921077222865)
            ·
              refine ⟨41540692665565440807917149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55387590220753921077222865 41540692665565440807917149)
              ·
                refine ⟨15577759749587040302968931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41540692665565440807917149 15577759749587040302968931)
                ·
                  refine ⟨23366639624380560454453397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15577759749587040302968931 23366639624380560454453397)
                  ·
                    refine ⟨1095311232392838771302503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23366639624380560454453397 1095311232392838771302503)
                    ·
                      rfl

theorem cell23_6399333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_6399333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399333 prefixEnd_6399333 := by exact prefixLift 6399333
  have htrace : WordTrace (prefixWord ++ tailWord_6399333) baseStart_6399333 baseEnd_6399333 := by
    simpa [prefixWord, tailWord_6399333, baseEnd_6399333] using wordTrace_append hprefix tailTrace_6399333
  have hstable : (prefixWord ++ tailWord_6399333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399333).length < 2 ^ (prefixWord ++ tailWord_6399333).sum := by decide
  have hdescent : baseEnd_6399333 < baseStart_6399333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399340 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 4]
def baseStart_6399340 : Nat := 118140960795 + 6399340 * 2 ^ 59
def prefixEnd_6399340 : Nat := 4983230072969 + 3 ^ 40 * 6399340 * 2
def baseEnd_6399340 : Nat := 3285937291543097786519977

theorem tailTrace_6399340 : CollatzResearch.WordTrace tailWord_6399340 prefixEnd_6399340 3285937291543097786519977 := by
  unfold tailWord_6399340
  simp only [CollatzResearch.WordTrace]
  refine ⟨116701552318145787552641737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155602069757527716736855649 116701552318145787552641737)
  ·
    refine ⟨87526164238609340664481303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116701552318145787552641737 87526164238609340664481303)
    ·
      refine ⟨131289246357914010996721955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87526164238609340664481303 131289246357914010996721955)
      ·
        refine ⟨196933869536871016495082933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131289246357914010996721955 196933869536871016495082933)
        ·
          refine ⟨18462550269081657796414025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196933869536871016495082933 18462550269081657796414025)
          ·
            refine ⟨13846912701811243347310519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18462550269081657796414025 13846912701811243347310519)
            ·
              refine ⟨20770369052716865020965779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13846912701811243347310519 20770369052716865020965779)
              ·
                refine ⟨31155553579075297531448669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20770369052716865020965779 31155553579075297531448669)
                ·
                  refine ⟨11683332592153236574293251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31155553579075297531448669 11683332592153236574293251)
                  ·
                    refine ⟨17524998888229854861439877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11683332592153236574293251 17524998888229854861439877)
                    ·
                      refine ⟨3285937291543097786519977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17524998888229854861439877 3285937291543097786519977)
                      ·
                        rfl

theorem cell23_6399340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_6399340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399340 prefixEnd_6399340 := by exact prefixLift 6399340
  have htrace : WordTrace (prefixWord ++ tailWord_6399340) baseStart_6399340 baseEnd_6399340 := by
    simpa [prefixWord, tailWord_6399340, baseEnd_6399340] using wordTrace_append hprefix tailTrace_6399340
  have hstable : (prefixWord ++ tailWord_6399340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399340).length < 2 ^ (prefixWord ++ tailWord_6399340).sum := by decide
  have hdescent : baseEnd_6399340 < baseStart_6399340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399353 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 3, 2, 4]
def baseStart_6399353 : Nat := 118140960795 + 6399353 * 2 ^ 59
def prefixEnd_6399353 : Nat := 4983230072969 + 3 ^ 40 * 6399353 * 2
def baseEnd_6399353 : Nat := 3285943966791606235657417

theorem tailTrace_6399353 : CollatzResearch.WordTrace tailWord_6399353 prefixEnd_6399353 3285943966791606235657417 := by
  unfold tailWord_6399353
  simp only [CollatzResearch.WordTrace]
  refine ⟨233403578785244478325506713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155602385856829652217004475 233403578785244478325506713)
  ·
    refine ⟨175052684088933358744130035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233403578785244478325506713 175052684088933358744130035)
    ·
      refine ⟨262579026133400038116195053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175052684088933358744130035 262579026133400038116195053)
      ·
        refine ⟨98467134800025014293573145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262579026133400038116195053 98467134800025014293573145)
        ·
          refine ⟨73850351100018760720179859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98467134800025014293573145 73850351100018760720179859)
          ·
            refine ⟨110775526650028141080269789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73850351100018760720179859 110775526650028141080269789)
            ·
              refine ⟨41540822493760552905101171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110775526650028141080269789 41540822493760552905101171)
              ·
                refine ⟨62311233740640829357651757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41540822493760552905101171 62311233740640829357651757)
                ·
                  refine ⟨23366712652740311009119409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62311233740640829357651757 23366712652740311009119409)
                  ·
                    refine ⟨17525034489555233256839557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23366712652740311009119409 17525034489555233256839557)
                    ·
                      refine ⟨3285943966791606235657417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17525034489555233256839557 3285943966791606235657417)
                      ·
                        rfl

theorem cell23_6399353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_6399353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399353 prefixEnd_6399353 := by exact prefixLift 6399353
  have htrace : WordTrace (prefixWord ++ tailWord_6399353) baseStart_6399353 baseEnd_6399353 := by
    simpa [prefixWord, tailWord_6399353, baseEnd_6399353] using wordTrace_append hprefix tailTrace_6399353
  have hstable : (prefixWord ++ tailWord_6399353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399353).length < 2 ^ (prefixWord ++ tailWord_6399353).sum := by decide
  have hdescent : baseEnd_6399353 < baseStart_6399353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399357 : List Nat := [1, 4, 1, 1, 2, 2, 5, 1, 1, 1, 4]
def baseStart_6399357 : Nat := 118140960795 + 6399357 * 2 ^ 59
def prefixEnd_6399357 : Nat := 4983230072969 + 3 ^ 40 * 6399357 * 2
def baseEnd_6399357 : Nat := 3285946020714224220007399

theorem tailTrace_6399357 : CollatzResearch.WordTrace tailWord_6399357 prefixEnd_6399357 3285946020714224220007399 := by
  unfold tailWord_6399357
  simp only [CollatzResearch.WordTrace]
  refine ⟨233403724677229987008652325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155602483118153324672434883 233403724677229987008652325)
  ·
    refine ⟨43763198376980622564122311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233403724677229987008652325 43763198376980622564122311)
    ·
      refine ⟨65644797565470933846183467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43763198376980622564122311 65644797565470933846183467)
      ·
        refine ⟨98467196348206400769275201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65644797565470933846183467 98467196348206400769275201)
        ·
          refine ⟨73850397261154800576956401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98467196348206400769275201 73850397261154800576956401)
          ·
            refine ⟨55387797945866100432717301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73850397261154800576956401 55387797945866100432717301)
            ·
              refine ⟨5192606057424946915567247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55387797945866100432717301 5192606057424946915567247)
              ·
                refine ⟨7788909086137420373350871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5192606057424946915567247 7788909086137420373350871)
                ·
                  refine ⟨11683363629206130560026307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7788909086137420373350871 11683363629206130560026307)
                  ·
                    refine ⟨17525045443809195840039461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11683363629206130560026307 17525045443809195840039461)
                    ·
                      refine ⟨3285946020714224220007399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17525045443809195840039461 3285946020714224220007399)
                      ·
                        rfl

theorem cell23_6399357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_6399357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399357 prefixEnd_6399357 := by exact prefixLift 6399357
  have htrace : WordTrace (prefixWord ++ tailWord_6399357) baseStart_6399357 baseEnd_6399357 := by
    simpa [prefixWord, tailWord_6399357, baseEnd_6399357] using wordTrace_append hprefix tailTrace_6399357
  have hstable : (prefixWord ++ tailWord_6399357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399357).length < 2 ^ (prefixWord ++ tailWord_6399357).sum := by decide
  have hdescent : baseEnd_6399357 < baseStart_6399357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399360 : List Nat := [2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 3]
def baseStart_6399360 : Nat := 118140960795 + 6399360 * 2 ^ 59
def prefixEnd_6399360 : Nat := 4983230072969 + 3 ^ 40 * 6399360 * 2
def baseEnd_6399360 : Nat := 3285947561156187708269885

theorem tailTrace_6399360 : CollatzResearch.WordTrace tailWord_6399360 prefixEnd_6399360 3285947561156187708269885 := by
  unfold tailWord_6399360
  simp only [CollatzResearch.WordTrace]
  refine ⟨116701917048109559260505767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155602556064146079014007689 116701917048109559260505767)
  ·
    refine ⟨175052875572164338890758651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116701917048109559260505767 175052875572164338890758651)
    ·
      refine ⟨262579313358246508336137977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175052875572164338890758651 262579313358246508336137977)
      ·
        refine ⟨196934485018684881252103483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262579313358246508336137977 196934485018684881252103483)
        ·
          refine ⟨295401727528027321878155225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196934485018684881252103483 295401727528027321878155225)
          ·
            refine ⟨221551295646020491408616419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295401727528027321878155225 221551295646020491408616419)
            ·
              refine ⟨332326943469030737112924629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221551295646020491408616419 332326943469030737112924629)
              ·
                refine ⟨7788912737555407901084171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 332326943469030737112924629 7788912737555407901084171)
                ·
                  refine ⟨11683369106333111851626257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7788912737555407901084171 11683369106333111851626257)
                  ·
                    refine ⟨8762526829749833888719693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11683369106333111851626257 8762526829749833888719693)
                    ·
                      refine ⟨3285947561156187708269885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8762526829749833888719693 3285947561156187708269885)
                      ·
                        rfl

theorem cell23_6399360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_6399360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399360 prefixEnd_6399360 := by exact prefixLift 6399360
  have htrace : WordTrace (prefixWord ++ tailWord_6399360) baseStart_6399360 baseEnd_6399360 := by
    simpa [prefixWord, tailWord_6399360, baseEnd_6399360] using wordTrace_append hprefix tailTrace_6399360
  have hstable : (prefixWord ++ tailWord_6399360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399360).length < 2 ^ (prefixWord ++ tailWord_6399360).sum := by decide
  have hdescent : baseEnd_6399360 < baseStart_6399360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399367 : List Nat := [1, 1, 4, 2, 2, 3, 2, 2, 2, 4]
def baseStart_6399367 : Nat := 118140960795 + 6399367 * 2 ^ 59
def prefixEnd_6399367 : Nat := 4983230072969 + 3 ^ 40 * 6399367 * 2
def baseEnd_6399367 : Nat := 1095317051840256393627451

theorem tailTrace_6399367 : CollatzResearch.WordTrace tailWord_6399367 prefixEnd_6399367 1095317051840256393627451 := by
  unfold tailWord_6399367
  simp only [CollatzResearch.WordTrace]
  refine ⟨233404089407193758716516355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155602726271462505811010903 233404089407193758716516355)
  ·
    refine ⟨350106134110790638074774533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233404089407193758716516355 350106134110790638074774533)
    ·
      refine ⟨65644900145773244639020225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 350106134110790638074774533 65644900145773244639020225)
      ·
        refine ⟨49233675109329933479265169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65644900145773244639020225 49233675109329933479265169)
        ·
          refine ⟨36925256331997450109448877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49233675109329933479265169 36925256331997450109448877)
          ·
            refine ⟨13846971124499043791043329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36925256331997450109448877 13846971124499043791043329)
            ·
              refine ⟨10385228343374282843282497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13846971124499043791043329 10385228343374282843282497)
              ·
                refine ⟨7788921257530712132461873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10385228343374282843282497 7788921257530712132461873)
                ·
                  refine ⟨5841690943148034099346405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7788921257530712132461873 5841690943148034099346405)
                  ·
                    refine ⟨1095317051840256393627451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5841690943148034099346405 1095317051840256393627451)
                    ·
                      rfl

theorem cell23_6399367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_6399367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399367 prefixEnd_6399367 := by exact prefixLift 6399367
  have htrace : WordTrace (prefixWord ++ tailWord_6399367) baseStart_6399367 baseEnd_6399367 := by
    simpa [prefixWord, tailWord_6399367, baseEnd_6399367] using wordTrace_append hprefix tailTrace_6399367
  have hstable : (prefixWord ++ tailWord_6399367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399367).length < 2 ^ (prefixWord ++ tailWord_6399367).sum := by decide
  have hdescent : baseEnd_6399367 < baseStart_6399367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399380 : List Nat := [2, 4, 2, 1, 2, 1, 3, 8]
def baseStart_6399380 : Nat := 118140960795 + 6399380 * 2 ^ 59
def prefixEnd_6399380 : Nat := 4983230072969 + 3 ^ 40 * 6399380 * 2
def baseEnd_6399380 : Nat := 121702141880343615926659

theorem tailTrace_6399380 : CollatzResearch.WordTrace tailWord_6399380 prefixEnd_6399380 121702141880343615926659 := by
  unfold tailWord_6399380
  simp only [CollatzResearch.WordTrace]
  refine ⟨116702281778073330968369797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155603042370764441291159729 116702281778073330968369797)
  ·
    refine ⟨21881677833388749556569337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116702281778073330968369797 21881677833388749556569337)
    ·
      refine ⟨16411258375041562167427003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21881677833388749556569337 16411258375041562167427003)
      ·
        refine ⟨24616887562562343251140505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16411258375041562167427003 24616887562562343251140505)
        ·
          refine ⟨18462665671921757438355379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24616887562562343251140505 18462665671921757438355379)
          ·
            refine ⟨27693998507882636157533069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18462665671921757438355379 27693998507882636157533069)
            ·
              refine ⟨10385249440455988559074901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27693998507882636157533069 10385249440455988559074901)
              ·
                refine ⟨121702141880343615926659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10385249440455988559074901 121702141880343615926659)
                ·
                  rfl

theorem cell23_6399380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 8].length) (baseStart_6399380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399380 prefixEnd_6399380 := by exact prefixLift 6399380
  have htrace : WordTrace (prefixWord ++ tailWord_6399380) baseStart_6399380 baseEnd_6399380 := by
    simpa [prefixWord, tailWord_6399380, baseEnd_6399380] using wordTrace_append hprefix tailTrace_6399380
  have hstable : (prefixWord ++ tailWord_6399380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399380).length < 2 ^ (prefixWord ++ tailWord_6399380).sum := by decide
  have hdescent : baseEnd_6399380 < baseStart_6399380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399433 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 4, 1, 5]
def baseStart_6399433 : Nat := 118140960795 + 6399433 * 2 ^ 59
def prefixEnd_6399433 : Nat := 4983230072969 + 3 ^ 40 * 6399433 * 2
def baseEnd_6399433 : Nat := 3285985045243965922657049

theorem tailTrace_6399433 : CollatzResearch.WordTrace tailWord_6399433 prefixEnd_6399433 3285985045243965922657049 := by
  unfold tailWord_6399433
  simp only [CollatzResearch.WordTrace]
  refine ⟨233406496624954651988418953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155604331083303101325612635 233406496624954651988418953)
  ·
    refine ⟨175054872468715988991314215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233406496624954651988418953 175054872468715988991314215)
    ·
      refine ⟨262582308703073983486971323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175054872468715988991314215 262582308703073983486971323)
      ·
        refine ⟨393873463054610975230456985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262582308703073983486971323 393873463054610975230456985)
        ·
          refine ⟨295405097290958231422842739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393873463054610975230456985 295405097290958231422842739)
          ·
            refine ⟨443107645936437347134264109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295405097290958231422842739 443107645936437347134264109)
            ·
              refine ⟨166165367226164005175349041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 443107645936437347134264109 166165367226164005175349041)
              ·
                refine ⟨124624025419623003881511781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166165367226164005175349041 124624025419623003881511781)
                ·
                  refine ⟨23367004766179313227783459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124624025419623003881511781 23367004766179313227783459)
                  ·
                    refine ⟨35050507149268969841675189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23367004766179313227783459 35050507149268969841675189)
                    ·
                      refine ⟨3285985045243965922657049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35050507149268969841675189 3285985045243965922657049)
                      ·
                        rfl

theorem cell23_6399433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_6399433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399433 prefixEnd_6399433 := by exact prefixLift 6399433
  have htrace : WordTrace (prefixWord ++ tailWord_6399433) baseStart_6399433 baseEnd_6399433 := by
    simpa [prefixWord, tailWord_6399433, baseEnd_6399433] using wordTrace_append hprefix tailTrace_6399433
  have hstable : (prefixWord ++ tailWord_6399433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399433).length < 2 ^ (prefixWord ++ tailWord_6399433).sum := by decide
  have hdescent : baseEnd_6399433 < baseStart_6399433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399498 : List Nat := [3, 1, 2, 2, 2, 4, 2, 1, 2, 2, 2]
def baseStart_6399498 : Nat := 118140960795 + 6399498 * 2 ^ 59
def prefixEnd_6399498 : Nat := 4983230072969 + 3 ^ 40 * 6399498 * 2
def baseEnd_6399498 : Nat := 3286018421486508168344251

theorem tailTrace_6399498 : CollatzResearch.WordTrace tailWord_6399498 prefixEnd_6399498 3286018421486508168344251 := by
  unfold tailWord_6399498
  simp only [CollatzResearch.WordTrace]
  refine ⟨58352216842429792022383787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155605911579812778726356765 58352216842429792022383787)
  ·
    refine ⟨87528325263644688033575681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58352216842429792022383787 87528325263644688033575681)
    ·
      refine ⟨65646243947733516025181761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87528325263644688033575681 65646243947733516025181761)
      ·
        refine ⟨49234682960800137018886321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65646243947733516025181761 49234682960800137018886321)
        ·
          refine ⟨36926012220600102764164741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49234682960800137018886321 36926012220600102764164741)
          ·
            refine ⟨6923627291362519268280889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36926012220600102764164741 6923627291362519268280889)
            ·
              refine ⟨5192720468521889451210667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6923627291362519268280889 5192720468521889451210667)
              ·
                refine ⟨7789080702782834176816001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5192720468521889451210667 7789080702782834176816001)
                ·
                  refine ⟨5841810527087125632612001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7789080702782834176816001 5841810527087125632612001)
                  ·
                    refine ⟨4381357895315344224459001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5841810527087125632612001 4381357895315344224459001)
                    ·
                      refine ⟨3286018421486508168344251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4381357895315344224459001 3286018421486508168344251)
                      ·
                        rfl

theorem cell23_6399498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_6399498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399498 prefixEnd_6399498 := by exact prefixLift 6399498
  have htrace : WordTrace (prefixWord ++ tailWord_6399498) baseStart_6399498 baseEnd_6399498 := by
    simpa [prefixWord, tailWord_6399498, baseEnd_6399498] using wordTrace_append hprefix tailTrace_6399498
  have hstable : (prefixWord ++ tailWord_6399498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399498).length < 2 ^ (prefixWord ++ tailWord_6399498).sum := by decide
  have hdescent : baseEnd_6399498 < baseStart_6399498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399517 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 2, 5]
def baseStart_6399517 : Nat := 118140960795 + 6399517 * 2 ^ 59
def prefixEnd_6399517 : Nat := 4983230072969 + 3 ^ 40 * 6399517 * 2
def baseEnd_6399517 : Nat := 1095342725872981198002221

theorem tailTrace_6399517 : CollatzResearch.WordTrace tailWord_6399517 prefixEnd_6399517 1095342725872981198002221 := by
  unfold tailWord_6399517
  simp only [CollatzResearch.WordTrace]
  refine ⟨233409560356650334334476805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155606373571100222889651203 233409560356650334334476805)
  ·
    refine ⟨43764292566871937687714401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 233409560356650334334476805 43764292566871937687714401)
    ·
      refine ⟨32823219425153953265785801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43764292566871937687714401 32823219425153953265785801)
      ·
        refine ⟨24617414568865464949339351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32823219425153953265785801 24617414568865464949339351)
        ·
          refine ⟨36926121853298197424009027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24617414568865464949339351 36926121853298197424009027)
          ·
            refine ⟨55389182779947296136013541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36926121853298197424009027 55389182779947296136013541)
            ·
              refine ⟨10385471771240118025502539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55389182779947296136013541 10385471771240118025502539)
              ·
                refine ⟨15578207656860177038253809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10385471771240118025502539 15578207656860177038253809)
                ·
                  refine ⟨11683655742645132778690357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15578207656860177038253809 11683655742645132778690357)
                  ·
                    refine ⟨1095342725872981198002221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11683655742645132778690357 1095342725872981198002221)
                    ·
                      rfl

theorem cell23_6399517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_6399517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399517 prefixEnd_6399517 := by exact prefixLift 6399517
  have htrace : WordTrace (prefixWord ++ tailWord_6399517) baseStart_6399517 baseEnd_6399517 := by
    simpa [prefixWord, tailWord_6399517, baseEnd_6399517] using wordTrace_append hprefix tailTrace_6399517
  have hstable : (prefixWord ++ tailWord_6399517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399517).length < 2 ^ (prefixWord ++ tailWord_6399517).sum := by decide
  have hdescent : baseEnd_6399517 < baseStart_6399517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399537 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 2, 4, 2]
def baseStart_6399537 : Nat := 118140960795 + 6399537 * 2 ^ 59
def prefixEnd_6399537 : Nat := 4983230072969 + 3 ^ 40 * 6399537 * 2
def baseEnd_6399537 : Nat := 3286038447232033515756571

theorem tailTrace_6399537 : CollatzResearch.WordTrace tailWord_6399537 prefixEnd_6399537 3286038447232033515756571 := by
  unfold tailWord_6399537
  simp only [CollatzResearch.WordTrace]
  refine ⟨233410289816577877750204865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155606859877718585166803243 233410289816577877750204865)
  ·
    refine ⟨175057717362433408312653649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 233410289816577877750204865 175057717362433408312653649)
    ·
      refine ⟨131293288021825056234490237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175057717362433408312653649 131293288021825056234490237)
      ·
        refine ⟨49234983008184396087933839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131293288021825056234490237 49234983008184396087933839)
        ·
          refine ⟨73852474512276594131900759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49234983008184396087933839 73852474512276594131900759)
          ·
            refine ⟨110778711768414891197851139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73852474512276594131900759 110778711768414891197851139)
            ·
              refine ⟨166168067652622336796776709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110778711768414891197851139 166168067652622336796776709)
              ·
                refine ⟨31156512684866688149395633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166168067652622336796776709 31156512684866688149395633)
                ·
                  refine ⟨23367384513650016112046725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31156512684866688149395633 23367384513650016112046725)
                  ·
                    refine ⟨4381384596309378021008761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23367384513650016112046725 4381384596309378021008761)
                    ·
                      refine ⟨3286038447232033515756571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4381384596309378021008761 3286038447232033515756571)
                      ·
                        rfl

theorem cell23_6399537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_6399537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399537 prefixEnd_6399537 := by exact prefixLift 6399537
  have htrace : WordTrace (prefixWord ++ tailWord_6399537) baseStart_6399537 baseEnd_6399537 := by
    simpa [prefixWord, tailWord_6399537, baseEnd_6399537] using wordTrace_append hprefix tailTrace_6399537
  have hstable : (prefixWord ++ tailWord_6399537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399537).length < 2 ^ (prefixWord ++ tailWord_6399537).sum := by decide
  have hdescent : baseEnd_6399537 < baseStart_6399537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399594 : List Nat := [3, 1, 3, 2, 1, 4, 1, 2, 6]
def baseStart_6399594 : Nat := 118140960795 + 6399594 * 2 ^ 59
def prefixEnd_6399594 : Nat := 4983230072969 + 3 ^ 40 * 6399594 * 2
def baseEnd_6399594 : Nat := 365118635069926643638201

theorem tailTrace_6399594 : CollatzResearch.WordTrace tailWord_6399594 prefixEnd_6399594 365118635069926643638201 := by
  unfold tailWord_6399594
  simp only [CollatzResearch.WordTrace]
  refine ⟨58353092194342844121257459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155608245851580917656686557 58353092194342844121257459)
  ·
    refine ⟨87529638291514266181886189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58353092194342844121257459 87529638291514266181886189)
    ·
      refine ⟨32823614359317849818207321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87529638291514266181886189 32823614359317849818207321)
      ·
        refine ⟨24617710769488387363655491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32823614359317849818207321 24617710769488387363655491)
        ·
          refine ⟨36926566154232581045483237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24617710769488387363655491 36926566154232581045483237)
          ·
            refine ⟨6923731153918608946028107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36926566154232581045483237 6923731153918608946028107)
            ·
              refine ⟨10385596730877913419042161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6923731153918608946028107 10385596730877913419042161)
              ·
                refine ⟨7789197548158435064281621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10385596730877913419042161 7789197548158435064281621)
                ·
                  refine ⟨365118635069926643638201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7789197548158435064281621 365118635069926643638201)
                  ·
                    rfl

theorem cell23_6399594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 6].length) (baseStart_6399594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399594 prefixEnd_6399594 := by exact prefixLift 6399594
  have htrace : WordTrace (prefixWord ++ tailWord_6399594) baseStart_6399594 baseEnd_6399594 := by
    simpa [prefixWord, tailWord_6399594, baseEnd_6399594] using wordTrace_append hprefix tailTrace_6399594
  have hstable : (prefixWord ++ tailWord_6399594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399594).length < 2 ^ (prefixWord ++ tailWord_6399594).sum := by decide
  have hdescent : baseEnd_6399594 < baseStart_6399594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399610 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4]
def baseStart_6399610 : Nat := 118140960795 + 6399610 * 2 ^ 59
def prefixEnd_6399610 : Nat := 4983230072969 + 3 ^ 40 * 6399610 * 2
def baseEnd_6399610 : Nat := 3286075931319811730143735

theorem tailTrace_6399610 : CollatzResearch.WordTrace tailWord_6399610 prefixEnd_6399610 3286075931319811730143735 := by
  unfold tailWord_6399610
  simp only [CollatzResearch.WordTrace]
  refine ⟨58353238086328352804403071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155608634896875607478408189 58353238086328352804403071)
  ·
    refine ⟨87529857129492529206604607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58353238086328352804403071 87529857129492529206604607)
    ·
      refine ⟨131294785694238793809906911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87529857129492529206604607 131294785694238793809906911)
      ·
        refine ⟨196942178541358190714860367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131294785694238793809906911 196942178541358190714860367)
        ·
          refine ⟨295413267812037286072290551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196942178541358190714860367 295413267812037286072290551)
          ·
            refine ⟨443119901718055929108435827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295413267812037286072290551 443119901718055929108435827)
            ·
              refine ⟨664679852577083893662653741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443119901718055929108435827 664679852577083893662653741)
              ·
                refine ⟨249254944716406460123495153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 664679852577083893662653741 249254944716406460123495153)
                ·
                  refine ⟨186941208537304845092621365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249254944716406460123495153 186941208537304845092621365)
                  ·
                    refine ⟨17525738300372329227433253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 186941208537304845092621365 17525738300372329227433253)
                    ·
                      refine ⟨3286075931319811730143735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17525738300372329227433253 3286075931319811730143735)
                      ·
                        rfl

theorem cell23_6399610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_6399610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399610 prefixEnd_6399610 := by exact prefixLift 6399610
  have htrace : WordTrace (prefixWord ++ tailWord_6399610) baseStart_6399610 baseEnd_6399610 := by
    simpa [prefixWord, tailWord_6399610, baseEnd_6399610] using wordTrace_append hprefix tailTrace_6399610
  have hstable : (prefixWord ++ tailWord_6399610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399610).length < 2 ^ (prefixWord ++ tailWord_6399610).sum := by decide
  have hdescent : baseEnd_6399610 < baseStart_6399610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399627 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 2, 6, 2]
def baseStart_6399627 : Nat := 118140960795 + 6399627 * 2 ^ 59
def prefixEnd_6399627 : Nat := 4983230072969 + 3 ^ 40 * 6399627 * 2
def baseEnd_6399627 : Nat := 3286084660490938163631157

theorem tailTrace_6399627 : CollatzResearch.WordTrace tailWord_6399627 prefixEnd_6399627 3286084660490938163631157 := by
  unfold tailWord_6399627
  simp only [CollatzResearch.WordTrace]
  refine ⟨233413572386251823120981135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155609048257501215413987423 233413572386251823120981135)
  ·
    refine ⟨350120358579377734681471703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233413572386251823120981135 350120358579377734681471703)
    ·
      refine ⟨525180537869066602022207555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350120358579377734681471703 525180537869066602022207555)
      ·
        refine ⟨787770806803599903033311333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525180537869066602022207555 787770806803599903033311333)
        ·
          refine ⟨147707026275674981818745875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 787770806803599903033311333 147707026275674981818745875)
          ·
            refine ⟨221560539413512472728118813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147707026275674981818745875 221560539413512472728118813)
            ·
              refine ⟨83085202280067177273044555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221560539413512472728118813 83085202280067177273044555)
              ·
                refine ⟨124627803420100765909566833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83085202280067177273044555 124627803420100765909566833)
                ·
                  refine ⟨93470852565075574432175125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124627803420100765909566833 93470852565075574432175125)
                  ·
                    refine ⟨4381446213987917551508209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93470852565075574432175125 4381446213987917551508209)
                    ·
                      refine ⟨3286084660490938163631157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4381446213987917551508209 3286084660490938163631157)
                      ·
                        rfl

theorem cell23_6399627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 6, 2].length) (baseStart_6399627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399627 prefixEnd_6399627 := by exact prefixLift 6399627
  have htrace : WordTrace (prefixWord ++ tailWord_6399627) baseStart_6399627 baseEnd_6399627 := by
    simpa [prefixWord, tailWord_6399627, baseEnd_6399627] using wordTrace_append hprefix tailTrace_6399627
  have hstable : (prefixWord ++ tailWord_6399627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399627).length < 2 ^ (prefixWord ++ tailWord_6399627).sum := by decide
  have hdescent : baseEnd_6399627 < baseStart_6399627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399671 : List Nat := [1, 1, 3, 1, 5, 1, 4, 1, 2, 4]
def baseStart_6399671 : Nat := 118140960795 + 6399671 * 2 ^ 59
def prefixEnd_6399671 : Nat := 4983230072969 + 3 ^ 40 * 6399671 * 2
def baseEnd_6399671 : Nat := 1095369084546578663826985

theorem tailTrace_6399671 : CollatzResearch.WordTrace tailWord_6399671 prefixEnd_6399671 1095369084546578663826985 := by
  unfold tailWord_6399671
  simp only [CollatzResearch.WordTrace]
  refine ⟨233415177198092418635582867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155610118132061612423721911 233415177198092418635582867)
  ·
    refine ⟨350122765797138627953374301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233415177198092418635582867 350122765797138627953374301)
    ·
      refine ⟨131296037173926985482515363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 350122765797138627953374301 131296037173926985482515363)
      ·
        refine ⟨196944055760890478223773045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131296037173926985482515363 196944055760890478223773045)
        ·
          refine ⟨18463505227583482333478723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196944055760890478223773045 18463505227583482333478723)
          ·
            refine ⟨27695257841375223500218085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18463505227583482333478723 27695257841375223500218085)
            ·
              refine ⟨5192860845257854406290891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27695257841375223500218085 5192860845257854406290891)
              ·
                refine ⟨7789291267886781609436337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5192860845257854406290891 7789291267886781609436337)
                ·
                  refine ⟨5841968450915086207077253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7789291267886781609436337 5841968450915086207077253)
                  ·
                    refine ⟨1095369084546578663826985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5841968450915086207077253 1095369084546578663826985)
                    ·
                      rfl

theorem cell23_6399671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 2, 4].length) (baseStart_6399671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399671 prefixEnd_6399671 := by exact prefixLift 6399671
  have htrace : WordTrace (prefixWord ++ tailWord_6399671) baseStart_6399671 baseEnd_6399671 := by
    simpa [prefixWord, tailWord_6399671, baseEnd_6399671] using wordTrace_append hprefix tailTrace_6399671
  have hstable : (prefixWord ++ tailWord_6399671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399671).length < 2 ^ (prefixWord ++ tailWord_6399671).sum := by decide
  have hdescent : baseEnd_6399671 < baseStart_6399671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399682 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_6399682 : Nat := 118140960795 + 6399682 * 2 ^ 59
def prefixEnd_6399682 : Nat := 4983230072969 + 3 ^ 40 * 6399682 * 2
def baseEnd_6399682 : Nat := 3286112901926935448443405

theorem tailTrace_6399682 : CollatzResearch.WordTrace tailWord_6399682 prefixEnd_6399682 3286112901926935448443405 := by
  unfold tailWord_6399682
  simp only [CollatzResearch.WordTrace]
  refine ⟨58353894600263141878558325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155610385600701711676155533 58353894600263141878558325)
  ·
    refine ⟨5470677618774669551114843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58353894600263141878558325 5470677618774669551114843)
    ·
      refine ⟨8206016428162004326672265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5470677618774669551114843 8206016428162004326672265)
      ·
        refine ⟨6154512321121503245004199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8206016428162004326672265 6154512321121503245004199)
        ·
          refine ⟨9231768481682254867506299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6154512321121503245004199 9231768481682254867506299)
          ·
            refine ⟨13847652722523382301259449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9231768481682254867506299 13847652722523382301259449)
            ·
              refine ⟨10385739541892536725944587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13847652722523382301259449 10385739541892536725944587)
              ·
                refine ⟨15578609312838805088916881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10385739541892536725944587 15578609312838805088916881)
                ·
                  refine ⟨11683956984629103816687661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15578609312838805088916881 11683956984629103816687661)
                  ·
                    refine ⟨4381483869235913931257873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11683956984629103816687661 4381483869235913931257873)
                    ·
                      refine ⟨3286112901926935448443405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4381483869235913931257873 3286112901926935448443405)
                      ·
                        rfl

theorem cell23_6399682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_6399682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399682 prefixEnd_6399682 := by exact prefixLift 6399682
  have htrace : WordTrace (prefixWord ++ tailWord_6399682) baseStart_6399682 baseEnd_6399682 := by
    simpa [prefixWord, tailWord_6399682, baseEnd_6399682] using wordTrace_append hprefix tailTrace_6399682
  have hstable : (prefixWord ++ tailWord_6399682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399682).length < 2 ^ (prefixWord ++ tailWord_6399682).sum := by decide
  have hdescent : baseEnd_6399682 < baseStart_6399682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399694 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3]
def baseStart_6399694 : Nat := 118140960795 + 6399694 * 2 ^ 59
def prefixEnd_6399694 : Nat := 4983230072969 + 3 ^ 40 * 6399694 * 2
def baseEnd_6399694 : Nat := 3286119063694789401493349

theorem tailTrace_6399694 : CollatzResearch.WordTrace tailWord_6399694 prefixEnd_6399694 3286119063694789401493349 := by
  unfold tailWord_6399694
  simp only [CollatzResearch.WordTrace]
  refine ⟨29177002009626136695458767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 155610677384672729042446757 29177002009626136695458767)
  ·
    refine ⟨43765503014439205043188151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29177002009626136695458767 43765503014439205043188151)
    ·
      refine ⟨65648254521658807564782227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43765503014439205043188151 65648254521658807564782227)
      ·
        refine ⟨98472381782488211347173341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65648254521658807564782227 98472381782488211347173341)
        ·
          refine ⟨36927143168433079255190003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98472381782488211347173341 36927143168433079255190003)
          ·
            refine ⟨55390714752649618882785005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36927143168433079255190003 55390714752649618882785005)
            ·
              refine ⟨20771518032243607081044377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55390714752649618882785005 20771518032243607081044377)
              ·
                refine ⟨15578638524182705310783283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20771518032243607081044377 15578638524182705310783283)
                ·
                  refine ⟨23367957786274057966174925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15578638524182705310783283 23367957786274057966174925)
                  ·
                    refine ⟨8762984169852771737315597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23367957786274057966174925 8762984169852771737315597)
                    ·
                      refine ⟨3286119063694789401493349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8762984169852771737315597 3286119063694789401493349)
                      ·
                        rfl

theorem cell23_6399694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_6399694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399694 prefixEnd_6399694 := by exact prefixLift 6399694
  have htrace : WordTrace (prefixWord ++ tailWord_6399694) baseStart_6399694 baseEnd_6399694 := by
    simpa [prefixWord, tailWord_6399694, baseEnd_6399694] using wordTrace_append hprefix tailTrace_6399694
  have hstable : (prefixWord ++ tailWord_6399694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399694).length < 2 ^ (prefixWord ++ tailWord_6399694).sum := by decide
  have hdescent : baseEnd_6399694 < baseStart_6399694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399698 : List Nat := [3, 2, 2, 2, 2, 2, 3, 1, 1, 2, 3]
def baseStart_6399698 : Nat := 118140960795 + 6399698 * 2 ^ 59
def prefixEnd_6399698 : Nat := 4983230072969 + 3 ^ 40 * 6399698 * 2
def baseEnd_6399698 : Nat := 3286121117617407385843331

theorem tailTrace_6399698 : CollatzResearch.WordTrace tailWord_6399698 prefixEnd_6399698 3286121117617407385843331 := by
  unfold tailWord_6399698
  simp only [CollatzResearch.WordTrace]
  refine ⟨58354040492248650561703937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 155610774645996401497877165 58354040492248650561703937)
  ·
    refine ⟨43765530369186487921277953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58354040492248650561703937 43765530369186487921277953)
    ·
      refine ⟨32824147776889865940958465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43765530369186487921277953 32824147776889865940958465)
      ·
        refine ⟨24618110832667399455718849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32824147776889865940958465 24618110832667399455718849)
        ·
          refine ⟨18463583124500549591789137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24618110832667399455718849 18463583124500549591789137)
          ·
            refine ⟨13847687343375412193841853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18463583124500549591789137 13847687343375412193841853)
            ·
              refine ⟨5192882753765779572690695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13847687343375412193841853 5192882753765779572690695)
              ·
                refine ⟨7789324130648669359036043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5192882753765779572690695 7789324130648669359036043)
                ·
                  refine ⟨11683986195973004038554065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7789324130648669359036043 11683986195973004038554065)
                  ·
                    refine ⟨8762989646979753028915549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11683986195973004038554065 8762989646979753028915549)
                    ·
                      refine ⟨3286121117617407385843331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8762989646979753028915549 3286121117617407385843331)
                      ·
                        rfl

theorem cell23_6399698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_6399698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399698 prefixEnd_6399698 := by exact prefixLift 6399698
  have htrace : WordTrace (prefixWord ++ tailWord_6399698) baseStart_6399698 baseEnd_6399698 := by
    simpa [prefixWord, tailWord_6399698, baseEnd_6399698] using wordTrace_append hprefix tailTrace_6399698
  have hstable : (prefixWord ++ tailWord_6399698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399698).length < 2 ^ (prefixWord ++ tailWord_6399698).sum := by decide
  have hdescent : baseEnd_6399698 < baseStart_6399698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399711 : List Nat := [1, 1, 2, 3, 2, 2, 4, 2, 2, 1, 3]
def baseStart_6399711 : Nat := 118140960795 + 6399711 * 2 ^ 59
def prefixEnd_6399711 : Nat := 4983230072969 + 3 ^ 40 * 6399711 * 2
def baseEnd_6399711 : Nat := 3286127792865915834980771

theorem tailTrace_6399711 : CollatzResearch.WordTrace tailWord_6399711 prefixEnd_6399711 3286127792865915834980771 := by
  unfold tailWord_6399711
  simp only [CollatzResearch.WordTrace]
  refine ⟨233416636117947505467038987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155611090745298336978025991 233416636117947505467038987)
  ·
    refine ⟨350124954176921258200558481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233416636117947505467038987 350124954176921258200558481)
    ·
      refine ⟨262593715632690943650418861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350124954176921258200558481 262593715632690943650418861)
      ·
        refine ⟨98472643362259103868907073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262593715632690943650418861 98472643362259103868907073)
        ·
          refine ⟨73854482521694327901680305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98472643362259103868907073 73854482521694327901680305)
          ·
            refine ⟨55390861891270745926260229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73854482521694327901680305 55390861891270745926260229)
            ·
              refine ⟨10385786604613264861173793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55390861891270745926260229 10385786604613264861173793)
              ·
                refine ⟨7789339953459948645880345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10385786604613264861173793 7789339953459948645880345)
                ·
                  refine ⟨5842004965094961484410259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7789339953459948645880345 5842004965094961484410259)
                  ·
                    refine ⟨8763007447642442226615389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5842004965094961484410259 8763007447642442226615389)
                    ·
                      refine ⟨3286127792865915834980771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8763007447642442226615389 3286127792865915834980771)
                      ·
                        rfl

theorem cell23_6399711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_6399711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399711 prefixEnd_6399711 := by exact prefixLift 6399711
  have htrace : WordTrace (prefixWord ++ tailWord_6399711) baseStart_6399711 baseEnd_6399711 := by
    simpa [prefixWord, tailWord_6399711, baseEnd_6399711] using wordTrace_append hprefix tailTrace_6399711
  have hstable : (prefixWord ++ tailWord_6399711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399711).length < 2 ^ (prefixWord ++ tailWord_6399711).sum := by decide
  have hdescent : baseEnd_6399711 < baseStart_6399711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399717 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 1, 5, 4]
def baseStart_6399717 : Nat := 118140960795 + 6399717 * 2 ^ 59
def prefixEnd_6399717 : Nat := 4983230072969 + 3 ^ 40 * 6399717 * 2
def baseEnd_6399717 : Nat := 3286130873749842811505743

theorem tailTrace_6399717 : CollatzResearch.WordTrace tailWord_6399717 prefixEnd_6399717 3286130873749842811505743 := by
  unfold tailWord_6399717
  simp only [CollatzResearch.WordTrace]
  refine ⟨233416854955925768491757405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155611236637283845661171603 233416854955925768491757405)
  ·
    refine ⟨87531320608472163184409027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 233416854955925768491757405 87531320608472163184409027)
    ·
      refine ⟨131296980912708244776613541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87531320608472163184409027 131296980912708244776613541)
      ·
        refine ⟨24618183921132795895615039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131296980912708244776613541 24618183921132795895615039)
        ·
          refine ⟨36927275881699193843422559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24618183921132795895615039 36927275881699193843422559)
          ·
            refine ⟨55390913822548790765133839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36927275881699193843422559 55390913822548790765133839)
            ·
              refine ⟨83086370733823186147700759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55390913822548790765133839 83086370733823186147700759)
              ·
                refine ⟨124629556100734779221551139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83086370733823186147700759 124629556100734779221551139)
                ·
                  refine ⟨186944334151102168832326709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124629556100734779221551139 186944334151102168832326709)
                  ·
                    refine ⟨17526031326665828328030629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 186944334151102168832326709 17526031326665828328030629)
                    ·
                      refine ⟨3286130873749842811505743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17526031326665828328030629 3286130873749842811505743)
                      ·
                        rfl

theorem cell23_6399717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_6399717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399717 prefixEnd_6399717 := by exact prefixLift 6399717
  have htrace : WordTrace (prefixWord ++ tailWord_6399717) baseStart_6399717 baseEnd_6399717 := by
    simpa [prefixWord, tailWord_6399717, baseEnd_6399717] using wordTrace_append hprefix tailTrace_6399717
  have hstable : (prefixWord ++ tailWord_6399717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399717).length < 2 ^ (prefixWord ++ tailWord_6399717).sum := by decide
  have hdescent : baseEnd_6399717 < baseStart_6399717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399727 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 2, 6]
def baseStart_6399727 : Nat := 118140960795 + 6399727 * 2 ^ 59
def prefixEnd_6399727 : Nat := 4983230072969 + 3 ^ 40 * 6399727 * 2
def baseEnd_6399727 : Nat := 1095378669518795924126899

theorem tailTrace_6399727 : CollatzResearch.WordTrace tailWord_6399727 prefixEnd_6399727 1095378669518795924126899 := by
  unfold tailWord_6399727
  simp only [CollatzResearch.WordTrace]
  refine ⟨233417219685889540199621435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155611479790593026799747623 233417219685889540199621435)
  ·
    refine ⟨350125829528834310299432153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233417219685889540199621435 350125829528834310299432153)
    ·
      refine ⟨262594372146625732724574115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350125829528834310299432153 262594372146625732724574115)
      ·
        refine ⟨393891558219938599086861173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262594372146625732724574115 393891558219938599086861173)
        ·
          refine ⟨36927333583119243664393235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 393891558219938599086861173 36927333583119243664393235)
          ·
            refine ⟨55391000374678865496589853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36927333583119243664393235 55391000374678865496589853)
            ·
              refine ⟨20771625140504574561221195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55391000374678865496589853 20771625140504574561221195)
              ·
                refine ⟨31157437710756861841831793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20771625140504574561221195 31157437710756861841831793)
                ·
                  refine ⟨23368078283067646381373845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31157437710756861841831793 23368078283067646381373845)
                  ·
                    refine ⟨1095378669518795924126899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23368078283067646381373845 1095378669518795924126899)
                    ·
                      rfl

theorem cell23_6399727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 6].length) (baseStart_6399727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399727 prefixEnd_6399727 := by exact prefixLift 6399727
  have htrace : WordTrace (prefixWord ++ tailWord_6399727) baseStart_6399727 baseEnd_6399727 := by
    simpa [prefixWord, tailWord_6399727, baseEnd_6399727] using wordTrace_append hprefix tailTrace_6399727
  have hstable : (prefixWord ++ tailWord_6399727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399727).length < 2 ^ (prefixWord ++ tailWord_6399727).sum := by decide
  have hdescent : baseEnd_6399727 < baseStart_6399727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399768 : List Nat := [2, 1, 2, 3, 1, 1, 5, 2, 2, 2, 2]
def baseStart_6399768 : Nat := 118140960795 + 6399768 * 2 ^ 59
def prefixEnd_6399768 : Nat := 4983230072969 + 3 ^ 40 * 6399768 * 2
def baseEnd_6399768 : Nat := 3286157061263222111968009

theorem tailTrace_6399768 : CollatzResearch.WordTrace tailWord_6399768 prefixEnd_6399768 3286157061263222111968009 := by
  unfold tailWord_6399768
  simp only [CollatzResearch.WordTrace]
  refine ⟨116709357539370502100931979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 155612476719160669467909305 116709357539370502100931979)
  ·
    refine ⟨175064036309055753151397969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116709357539370502100931979 175064036309055753151397969)
    ·
      refine ⟨131298027231791814863548477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175064036309055753151397969 131298027231791814863548477)
      ·
        refine ⟨49236760211921930573830679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131298027231791814863548477 49236760211921930573830679)
        ·
          refine ⟨73855140317882895860746019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49236760211921930573830679 73855140317882895860746019)
          ·
            refine ⟨110782710476824343791119029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73855140317882895860746019 110782710476824343791119029)
            ·
              refine ⟨10385879107202282230417409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110782710476824343791119029 10385879107202282230417409)
              ·
                refine ⟨7789409330401711672813057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10385879107202282230417409 7789409330401711672813057)
                ·
                  refine ⟨5842056997801283754609793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7789409330401711672813057 5842056997801283754609793)
                  ·
                    refine ⟨4381542748350962815957345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5842056997801283754609793 4381542748350962815957345)
                    ·
                      refine ⟨3286157061263222111968009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4381542748350962815957345 3286157061263222111968009)
                      ·
                        rfl

theorem cell23_6399768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_6399768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399768 prefixEnd_6399768 := by exact prefixLift 6399768
  have htrace : WordTrace (prefixWord ++ tailWord_6399768) baseStart_6399768 baseEnd_6399768 := by
    simpa [prefixWord, tailWord_6399768, baseEnd_6399768] using wordTrace_append hprefix tailTrace_6399768
  have hstable : (prefixWord ++ tailWord_6399768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399768).length < 2 ^ (prefixWord ++ tailWord_6399768).sum := by decide
  have hdescent : baseEnd_6399768 < baseStart_6399768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399821 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_6399821 : Nat := 118140960795 + 6399821 * 2 ^ 59
def prefixEnd_6399821 : Nat := 4983230072969 + 3 ^ 40 * 6399821 * 2
def baseEnd_6399821 : Nat := 1095394758579303468201755

theorem tailTrace_6399821 : CollatzResearch.WordTrace tailWord_6399821 prefixEnd_6399821 1095394758579303468201755 := by
  unfold tailWord_6399821
  simp only [CollatzResearch.WordTrace]
  refine ⟨233420648147548994253543317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155613765431699329502362211 233420648147548994253543317)
  ·
    refine ⟨10941592881916359105634843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 233420648147548994253543317 10941592881916359105634843)
    ·
      refine ⟨16412389322874538658452265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10941592881916359105634843 16412389322874538658452265)
      ·
        refine ⟨12309291992155903993839199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16412389322874538658452265 12309291992155903993839199)
        ·
          refine ⟨18463937988233855990758799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12309291992155903993839199 18463937988233855990758799)
          ·
            refine ⟨27695906982350783986138199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18463937988233855990758799 27695906982350783986138199)
            ·
              refine ⟨41543860473526175979207299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27695906982350783986138199 41543860473526175979207299)
              ·
                refine ⟨62315790710289263968810949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41543860473526175979207299 62315790710289263968810949)
                ·
                  refine ⟨11684210758179236994152053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62315790710289263968810949 11684210758179236994152053)
                  ·
                    refine ⟨1095394758579303468201755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11684210758179236994152053 1095394758579303468201755)
                    ·
                      rfl

theorem cell23_6399821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_6399821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399821 prefixEnd_6399821 := by exact prefixLift 6399821
  have htrace : WordTrace (prefixWord ++ tailWord_6399821) baseStart_6399821 baseEnd_6399821 := by
    simpa [prefixWord, tailWord_6399821, baseEnd_6399821] using wordTrace_append hprefix tailTrace_6399821
  have hstable : (prefixWord ++ tailWord_6399821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399821).length < 2 ^ (prefixWord ++ tailWord_6399821).sum := by decide
  have hdescent : baseEnd_6399821 < baseStart_6399821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6399867 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 8]
def baseStart_6399867 : Nat := 118140960795 + 6399867 * 2 ^ 59
def prefixEnd_6399867 : Nat := 4983230072969 + 3 ^ 40 * 6399867 * 2
def baseEnd_6399867 : Nat := 3286207895848017224630053

theorem tailTrace_6399867 : CollatzResearch.WordTrace tailWord_6399867 prefixEnd_6399867 3286207895848017224630053 := by
  unfold tailWord_6399867
  simp only [CollatzResearch.WordTrace]
  refine ⟨233422325905382344109717855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155614883936921562739811903 233422325905382344109717855)
  ·
    refine ⟨350133488858073516164576783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233422325905382344109717855 350133488858073516164576783)
    ·
      refine ⟨525200233287110274246865175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350133488858073516164576783 525200233287110274246865175)
      ·
        refine ⟨787800349930665411370297763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525200233287110274246865175 787800349930665411370297763)
        ·
          refine ⟨1181700524895998117055446645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787800349930665411370297763 1181700524895998117055446645)
          ·
            refine ⟨110784424208999823473948123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1181700524895998117055446645 110784424208999823473948123)
            ·
              refine ⟨166176636313499735210922185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110784424208999823473948123 166176636313499735210922185)
              ·
                refine ⟨124632477235124801408191639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166176636313499735210922185 124632477235124801408191639)
                ·
                  refine ⟨186948715852687202112287459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124632477235124801408191639 186948715852687202112287459)
                  ·
                    refine ⟨280423073779030803168431189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 186948715852687202112287459 280423073779030803168431189)
                    ·
                      refine ⟨3286207895848017224630053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 280423073779030803168431189 3286207895848017224630053)
                      ·
                        rfl

theorem cell23_6399867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 8].length) (baseStart_6399867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6399867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6399867 prefixEnd_6399867 := by exact prefixLift 6399867
  have htrace : WordTrace (prefixWord ++ tailWord_6399867) baseStart_6399867 baseEnd_6399867 := by
    simpa [prefixWord, tailWord_6399867, baseEnd_6399867] using wordTrace_append hprefix tailTrace_6399867
  have hstable : (prefixWord ++ tailWord_6399867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6399867).length < 2 ^ (prefixWord ++ tailWord_6399867).sum := by decide
  have hdescent : baseEnd_6399867 < baseStart_6399867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6399867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
