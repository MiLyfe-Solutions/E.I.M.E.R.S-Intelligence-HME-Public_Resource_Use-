import V185TrunkScan23Chunk1256

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7445697 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_7445697 : Nat := 118140960795 + 7445697 * 2 ^ 59
def prefixEnd_7445697 : Nat := 4983230072969 + 3 ^ 40 * 7445697 * 2
def baseEnd_7445697 : Nat := 3823221368739660409945369

theorem tailTrace_7445697 : CollatzResearch.WordTrace tailWord_7445697 prefixEnd_7445697 3823221368739660409945369 := by
  unfold tailWord_7445697
  simp only [CollatzResearch.WordTrace]
  refine ⟨271566879706518867653567345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181044586471012578435711563 271566879706518867653567345)
  ·
    refine ⟨203675159779889150740175509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271566879706518867653567345 203675159779889150740175509)
    ·
      refine ⟨9547273114682303940945727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 203675159779889150740175509 9547273114682303940945727)
      ·
        refine ⟨14320909672023455911418591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9547273114682303940945727 14320909672023455911418591)
        ·
          refine ⟨21481364508035183867127887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14320909672023455911418591 21481364508035183867127887)
          ·
            refine ⟨32222046762052775800691831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21481364508035183867127887 32222046762052775800691831)
            ·
              refine ⟨48333070143079163701037747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32222046762052775800691831 48333070143079163701037747)
              ·
                refine ⟨72499605214618745551556621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48333070143079163701037747 72499605214618745551556621)
                ·
                  refine ⟨27187351955482029581833733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72499605214618745551556621 27187351955482029581833733)
                  ·
                    refine ⟨5097628491652880546593825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27187351955482029581833733 5097628491652880546593825)
                    ·
                      refine ⟨3823221368739660409945369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5097628491652880546593825 3823221368739660409945369)
                      ·
                        rfl

theorem cell23_7445697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_7445697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445697 prefixEnd_7445697 := by exact prefixLift 7445697
  have htrace : WordTrace (prefixWord ++ tailWord_7445697) baseStart_7445697 baseEnd_7445697 := by
    simpa [prefixWord, tailWord_7445697, baseEnd_7445697] using wordTrace_append hprefix tailTrace_7445697
  have hstable : (prefixWord ++ tailWord_7445697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445697).length < 2 ^ (prefixWord ++ tailWord_7445697).sum := by decide
  have hdescent : baseEnd_7445697 < baseStart_7445697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445713 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 2, 3, 3]
def baseStart_7445713 : Nat := 118140960795 + 7445713 * 2 ^ 59
def prefixEnd_7445713 : Nat := 4983230072969 + 3 ^ 40 * 7445713 * 2
def baseEnd_7445713 : Nat := 3823229584430132347345295

theorem tailTrace_7445713 : CollatzResearch.WordTrace tailWord_7445713 prefixEnd_7445713 3823229584430132347345295 := by
  unfold tailWord_7445713
  simp only [CollatzResearch.WordTrace]
  refine ⟨271567463274460902386149793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181044975516307268257433195 271567463274460902386149793)
  ·
    refine ⟨203675597455845676789612345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271567463274460902386149793 203675597455845676789612345)
    ·
      refine ⟨152756698091884257592209259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203675597455845676789612345 152756698091884257592209259)
      ·
        refine ⟨229135047137826386388313889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152756698091884257592209259 229135047137826386388313889)
        ·
          refine ⟨171851285353369789791235417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229135047137826386388313889 171851285353369789791235417)
          ·
            refine ⟨128888464015027342343426563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171851285353369789791235417 128888464015027342343426563)
            ·
              refine ⟨193332696022541013515139845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128888464015027342343426563 193332696022541013515139845)
              ·
                refine ⟨36249880504226440034088721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193332696022541013515139845 36249880504226440034088721)
                ·
                  refine ⟨27187410378169830025566541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36249880504226440034088721 27187410378169830025566541)
                  ·
                    refine ⟨10195278891813686259587453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27187410378169830025566541 10195278891813686259587453)
                    ·
                      refine ⟨3823229584430132347345295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10195278891813686259587453 3823229584430132347345295)
                      ·
                        rfl

theorem cell23_7445713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_7445713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445713 prefixEnd_7445713 := by exact prefixLift 7445713
  have htrace : WordTrace (prefixWord ++ tailWord_7445713) baseStart_7445713 baseEnd_7445713 := by
    simpa [prefixWord, tailWord_7445713, baseEnd_7445713] using wordTrace_append hprefix tailTrace_7445713
  have hstable : (prefixWord ++ tailWord_7445713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445713).length < 2 ^ (prefixWord ++ tailWord_7445713).sum := by decide
  have hdescent : baseEnd_7445713 < baseStart_7445713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445714 : List Nat := [3, 2, 2, 2, 1, 1, 4, 2, 2, 2, 2]
def baseStart_7445714 : Nat := 118140960795 + 7445714 * 2 ^ 59
def prefixEnd_7445714 : Nat := 4983230072969 + 3 ^ 40 * 7445714 * 2
def baseEnd_7445714 : Nat := 3823230097910786843432791

theorem tailTrace_7445714 : CollatzResearch.WordTrace tailWord_7445714 prefixEnd_7445714 3823230097910786843432791 := by
  unfold tailWord_7445714
  simp only [CollatzResearch.WordTrace]
  refine ⟨67891874936864319889234049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181044999831638186371290797 67891874936864319889234049)
  ·
    refine ⟨50918906202648239916925537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67891874936864319889234049 50918906202648239916925537)
    ·
      refine ⟨38189179651986179937694153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50918906202648239916925537 38189179651986179937694153)
      ·
        refine ⟨28641884738989634953270615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38189179651986179937694153 28641884738989634953270615)
        ·
          refine ⟨42962827108484452429905923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28641884738989634953270615 42962827108484452429905923)
          ·
            refine ⟨64444240662726678644858885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42962827108484452429905923 64444240662726678644858885)
            ·
              refine ⟨12083295124261252245911041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64444240662726678644858885 12083295124261252245911041)
              ·
                refine ⟨9062471343195939184433281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12083295124261252245911041 9062471343195939184433281)
                ·
                  refine ⟨6796853507396954388324961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9062471343195939184433281 6796853507396954388324961)
                  ·
                    refine ⟨5097640130547715791243721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6796853507396954388324961 5097640130547715791243721)
                    ·
                      refine ⟨3823230097910786843432791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5097640130547715791243721 3823230097910786843432791)
                      ·
                        rfl

theorem cell23_7445714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_7445714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445714 prefixEnd_7445714 := by exact prefixLift 7445714
  have htrace : WordTrace (prefixWord ++ tailWord_7445714) baseStart_7445714 baseEnd_7445714 := by
    simpa [prefixWord, tailWord_7445714, baseEnd_7445714] using wordTrace_append hprefix tailTrace_7445714
  have hstable : (prefixWord ++ tailWord_7445714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445714).length < 2 ^ (prefixWord ++ tailWord_7445714).sum := by decide
  have hdescent : baseEnd_7445714 < baseStart_7445714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445753 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 1, 3, 4]
def baseStart_7445753 : Nat := 118140960795 + 7445753 * 2 ^ 59
def prefixEnd_7445753 : Nat := 4983230072969 + 3 ^ 40 * 7445753 * 2
def baseEnd_7445753 : Nat := 3823250123656312190845111

theorem tailTrace_7445753 : CollatzResearch.WordTrace tailWord_7445753 prefixEnd_7445753 3823250123656312190845111 := by
  unfold tailWord_7445753
  simp only [CollatzResearch.WordTrace]
  refine ⟨271568922194315989217605913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181045948129543992811737275 271568922194315989217605913)
  ·
    refine ⟨203676691645736991913204435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271568922194315989217605913 203676691645736991913204435)
    ·
      refine ⟨305515037468605487869806653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203676691645736991913204435 305515037468605487869806653)
      ·
        refine ⟨114568139050727057951177495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305515037468605487869806653 114568139050727057951177495)
        ·
          refine ⟨171852208576090586926766243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114568139050727057951177495 171852208576090586926766243)
          ·
            refine ⟨257778312864135880390149365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171852208576090586926766243 257778312864135880390149365)
            ·
              refine ⟨24166716831012738786576503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 257778312864135880390149365 24166716831012738786576503)
              ·
                refine ⟨36250075246519108179864755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24166716831012738786576503 36250075246519108179864755)
                ·
                  refine ⟨54375112869778662269797133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36250075246519108179864755 54375112869778662269797133)
                  ·
                    refine ⟨20390667326166998351173925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54375112869778662269797133 20390667326166998351173925)
                    ·
                      refine ⟨3823250123656312190845111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20390667326166998351173925 3823250123656312190845111)
                      ·
                        rfl

theorem cell23_7445753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_7445753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445753 prefixEnd_7445753 := by exact prefixLift 7445753
  have htrace : WordTrace (prefixWord ++ tailWord_7445753) baseStart_7445753 baseEnd_7445753 := by
    simpa [prefixWord, tailWord_7445753, baseEnd_7445753] using wordTrace_append hprefix tailTrace_7445753
  have hstable : (prefixWord ++ tailWord_7445753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445753).length < 2 ^ (prefixWord ++ tailWord_7445753).sum := by decide
  have hdescent : baseEnd_7445753 < baseStart_7445753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445783 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 6]
def baseStart_7445783 : Nat := 118140960795 + 7445783 * 2 ^ 59
def prefixEnd_7445783 : Nat := 4983230072969 + 3 ^ 40 * 7445783 * 2
def baseEnd_7445783 : Nat := 3823265528075947073469973

theorem tailTrace_7445783 : CollatzResearch.WordTrace tailWord_7445783 prefixEnd_7445783 3823265528075947073469973 := by
  unfold tailWord_7445783
  simp only [CollatzResearch.WordTrace]
  refine ⟨271570016384207304341198003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181046677589471536227465335 271570016384207304341198003)
  ·
    refine ⟨407355024576310956511797005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271570016384207304341198003 407355024576310956511797005)
    ·
      refine ⟨152758134216116608691923877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407355024576310956511797005 152758134216116608691923877)
      ·
        refine ⟨28642150165521864129735727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152758134216116608691923877 28642150165521864129735727)
        ·
          refine ⟨42963225248282796194603591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28642150165521864129735727 42963225248282796194603591)
          ·
            refine ⟨64444837872424194291905387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42963225248282796194603591 64444837872424194291905387)
            ·
              refine ⟨96667256808636291437858081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64444837872424194291905387 96667256808636291437858081)
              ·
                refine ⟨72500442606477218578393561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96667256808636291437858081 72500442606477218578393561)
                ·
                  refine ⟨54375331954857913933795171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72500442606477218578393561 54375331954857913933795171)
                  ·
                    refine ⟨81562997932286870900692757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54375331954857913933795171 81562997932286870900692757)
                    ·
                      refine ⟨3823265528075947073469973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81562997932286870900692757 3823265528075947073469973)
                      ·
                        rfl

theorem cell23_7445783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_7445783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445783 prefixEnd_7445783 := by exact prefixLift 7445783
  have htrace : WordTrace (prefixWord ++ tailWord_7445783) baseStart_7445783 baseEnd_7445783 := by
    simpa [prefixWord, tailWord_7445783, baseEnd_7445783] using wordTrace_append hprefix tailTrace_7445783
  have hstable : (prefixWord ++ tailWord_7445783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445783).length < 2 ^ (prefixWord ++ tailWord_7445783).sum := by decide
  have hdescent : baseEnd_7445783 < baseStart_7445783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445917 : List Nat := [1, 4, 2, 1, 3, 2, 3, 7]
def baseStart_7445917 : Nat := 118140960795 + 7445917 * 2 ^ 59
def prefixEnd_7445917 : Nat := 4983230072969 + 3 ^ 40 * 7445917 * 2
def baseEnd_7445917 : Nat := 141604975351246279599791

theorem tailTrace_7445917 : CollatzResearch.WordTrace tailWord_7445917 prefixEnd_7445917 141604975351246279599791 := by
  unfold tailWord_7445917
  simp only [CollatzResearch.WordTrace]
  refine ⟨271574903765721845226576005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181049935843814563484384003 271574903765721845226576005)
  ·
    refine ⟨50920294456072845979983001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271574903765721845226576005 50920294456072845979983001)
    ·
      refine ⟨38190220842054634484987251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50920294456072845979983001 38190220842054634484987251)
      ·
        refine ⟨57285331263081951727480877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38190220842054634484987251 57285331263081951727480877)
        ·
          refine ⟨21481999223655731897805329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57285331263081951727480877 21481999223655731897805329)
          ·
            refine ⟨16111499417741798923353997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21481999223655731897805329 16111499417741798923353997)
            ·
              refine ⟨6041812281653174596257749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16111499417741798923353997 6041812281653174596257749)
              ·
                refine ⟨141604975351246279599791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6041812281653174596257749 141604975351246279599791)
                ·
                  rfl

theorem cell23_7445917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 7].length) (baseStart_7445917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445917 prefixEnd_7445917 := by exact prefixLift 7445917
  have htrace : WordTrace (prefixWord ++ tailWord_7445917) baseStart_7445917 baseEnd_7445917 := by
    simpa [prefixWord, tailWord_7445917, baseEnd_7445917] using wordTrace_append hprefix tailTrace_7445917
  have hstable : (prefixWord ++ tailWord_7445917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445917).length < 2 ^ (prefixWord ++ tailWord_7445917).sum := by decide
  have hdescent : baseEnd_7445917 < baseStart_7445917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445927 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_7445927 : Nat := 118140960795 + 7445927 * 2 ^ 59
def prefixEnd_7445927 : Nat := 4983230072969 + 3 ^ 40 * 7445927 * 2
def baseEnd_7445927 : Nat := 3823339469290194510069311

theorem tailTrace_7445927 : CollatzResearch.WordTrace tailWord_7445927 prefixEnd_7445927 3823339469290194510069311 := by
  unfold tailWord_7445927
  simp only [CollatzResearch.WordTrace]
  refine ⟨271575268495685616934440035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181050178997123744622960023 271575268495685616934440035)
  ·
    refine ⟨407362902743528425401660053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271575268495685616934440035 407362902743528425401660053)
    ·
      refine ⟨19095136066102894940702815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 407362902743528425401660053 19095136066102894940702815)
      ·
        refine ⟨28642704099154342411054223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19095136066102894940702815 28642704099154342411054223)
        ·
          refine ⟨42964056148731513616581335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28642704099154342411054223 42964056148731513616581335)
          ·
            refine ⟨64446084223097270424872003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42964056148731513616581335 64446084223097270424872003)
            ·
              refine ⟨96669126334645905637308005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64446084223097270424872003 96669126334645905637308005)
              ·
                refine ⟨18125461187746107306995251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96669126334645905637308005 18125461187746107306995251)
                ·
                  refine ⟨27188191781619160960492877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18125461187746107306995251 27188191781619160960492877)
                  ·
                    refine ⟨10195571918107185360184829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27188191781619160960492877 10195571918107185360184829)
                    ·
                      refine ⟨3823339469290194510069311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10195571918107185360184829 3823339469290194510069311)
                      ·
                        rfl

theorem cell23_7445927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_7445927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445927 prefixEnd_7445927 := by exact prefixLift 7445927
  have htrace : WordTrace (prefixWord ++ tailWord_7445927) baseStart_7445927 baseEnd_7445927 := by
    simpa [prefixWord, tailWord_7445927, baseEnd_7445927] using wordTrace_append hprefix tailTrace_7445927
  have hstable : (prefixWord ++ tailWord_7445927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445927).length < 2 ^ (prefixWord ++ tailWord_7445927).sum := by decide
  have hdescent : baseEnd_7445927 < baseStart_7445927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445928 : List Nat := [2, 1, 6, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_7445928 : Nat := 118140960795 + 7445928 * 2 ^ 59
def prefixEnd_7445928 : Nat := 4983230072969 + 3 ^ 40 * 7445928 * 2
def baseEnd_7445928 : Nat := 3823339982770849006156807

theorem tailTrace_7445928 : CollatzResearch.WordTrace tailWord_7445928 prefixEnd_7445928 3823339982770849006156807 := by
  unfold tailWord_7445928
  simp only [CollatzResearch.WordTrace]
  refine ⟨135787652484340997052613219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181050203312454662736817625 135787652484340997052613219)
  ·
    refine ⟨203681478726511495578919829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135787652484340997052613219 203681478726511495578919829)
    ·
      refine ⟨9547569315305226355261867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 203681478726511495578919829 9547569315305226355261867)
      ·
        refine ⟨14321353972957839532892801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9547569315305226355261867 14321353972957839532892801)
        ·
          refine ⟨10741015479718379649669601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14321353972957839532892801 10741015479718379649669601)
          ·
            refine ⟨8055761609788784737252201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10741015479718379649669601 8055761609788784737252201)
            ·
              refine ⟨6041821207341588552939151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8055761609788784737252201 6041821207341588552939151)
              ·
                refine ⟨9062731811012382829408727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6041821207341588552939151 9062731811012382829408727)
                ·
                  refine ⟨13594097716518574244113091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9062731811012382829408727 13594097716518574244113091)
                  ·
                    refine ⟨20391146574777861366169637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13594097716518574244113091 20391146574777861366169637)
                    ·
                      refine ⟨3823339982770849006156807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20391146574777861366169637 3823339982770849006156807)
                      ·
                        rfl

theorem cell23_7445928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_7445928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445928 prefixEnd_7445928 := by exact prefixLift 7445928
  have htrace : WordTrace (prefixWord ++ tailWord_7445928) baseStart_7445928 baseEnd_7445928 := by
    simpa [prefixWord, tailWord_7445928, baseEnd_7445928] using wordTrace_append hprefix tailTrace_7445928
  have hstable : (prefixWord ++ tailWord_7445928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445928).length < 2 ^ (prefixWord ++ tailWord_7445928).sum := by decide
  have hdescent : baseEnd_7445928 < baseStart_7445928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445944 : List Nat := [2, 1, 2, 1, 2, 2, 5, 2, 2, 1, 3]
def baseStart_7445944 : Nat := 118140960795 + 7445944 * 2 ^ 59
def prefixEnd_7445944 : Nat := 4983230072969 + 3 ^ 40 * 7445944 * 2
def baseEnd_7445944 : Nat := 3823348198461320943556733

theorem tailTrace_7445944 : CollatzResearch.WordTrace tailWord_7445944 prefixEnd_7445944 3823348198461320943556733 := by
  unfold tailWord_7445944
  simp only [CollatzResearch.WordTrace]
  refine ⟨135787944268312014418904443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181050592357749352558539257 135787944268312014418904443)
  ·
    refine ⟨203681916402468021628356665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135787944268312014418904443 203681916402468021628356665)
    ·
      refine ⟨152761437301851016221267499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203681916402468021628356665 152761437301851016221267499)
      ·
        refine ⟨229142155952776524331901249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152761437301851016221267499 229142155952776524331901249)
        ·
          refine ⟨171856616964582393248925937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229142155952776524331901249 171856616964582393248925937)
          ·
            refine ⟨128892462723436794936694453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171856616964582393248925937 128892462723436794936694453)
            ·
              refine ⟨12083668380322199525315105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128892462723436794936694453 12083668380322199525315105)
              ·
                refine ⟨9062751285241649643986329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12083668380322199525315105 9062751285241649643986329)
                ·
                  refine ⟨6797063463931237232989747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9062751285241649643986329 6797063463931237232989747)
                  ·
                    refine ⟨10195595195896855849484621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6797063463931237232989747 10195595195896855849484621)
                    ·
                      refine ⟨3823348198461320943556733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10195595195896855849484621 3823348198461320943556733)
                      ·
                        rfl

theorem cell23_7445944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 2, 1, 3].length) (baseStart_7445944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445944 prefixEnd_7445944 := by exact prefixLift 7445944
  have htrace : WordTrace (prefixWord ++ tailWord_7445944) baseStart_7445944 baseEnd_7445944 := by
    simpa [prefixWord, tailWord_7445944, baseEnd_7445944] using wordTrace_append hprefix tailTrace_7445944
  have hstable : (prefixWord ++ tailWord_7445944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445944).length < 2 ^ (prefixWord ++ tailWord_7445944).sum := by decide
  have hdescent : baseEnd_7445944 < baseStart_7445944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445960 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 2, 6]
def baseStart_7445960 : Nat := 118140960795 + 7445960 * 2 ^ 59
def prefixEnd_7445960 : Nat := 4983230072969 + 3 ^ 40 * 7445960 * 2
def baseEnd_7445960 : Nat := 1274452138050597626985553

theorem tailTrace_7445960 : CollatzResearch.WordTrace tailWord_7445960 prefixEnd_7445960 1274452138050597626985553 := by
  unfold tailWord_7445960
  simp only [CollatzResearch.WordTrace]
  refine ⟨135788236052283031785195667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181050981403044042380260889 135788236052283031785195667)
  ·
    refine ⟨203682354078424547677793501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135788236052283031785195667 203682354078424547677793501)
    ·
      refine ⟨76380882779409205379172563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203682354078424547677793501 76380882779409205379172563)
      ·
        refine ⟨114571324169113808068758845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76380882779409205379172563 114571324169113808068758845)
        ·
          refine ⟨42964246563417678025784567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114571324169113808068758845 42964246563417678025784567)
          ·
            refine ⟨64446369845126517038676851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42964246563417678025784567 64446369845126517038676851)
            ·
              refine ⟨96669554767689775558015277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64446369845126517038676851 96669554767689775558015277)
              ·
                refine ⟨36251083037883665834255729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96669554767689775558015277 36251083037883665834255729)
                ·
                  refine ⟨27188312278412749375691797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36251083037883665834255729 27188312278412749375691797)
                  ·
                    refine ⟨1274452138050597626985553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27188312278412749375691797 1274452138050597626985553)
                    ·
                      rfl

theorem cell23_7445960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_7445960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445960 prefixEnd_7445960 := by exact prefixLift 7445960
  have htrace : WordTrace (prefixWord ++ tailWord_7445960) baseStart_7445960 baseEnd_7445960 := by
    simpa [prefixWord, tailWord_7445960, baseEnd_7445960] using wordTrace_append hprefix tailTrace_7445960
  have hstable : (prefixWord ++ tailWord_7445960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445960).length < 2 ^ (prefixWord ++ tailWord_7445960).sum := by decide
  have hdescent : baseEnd_7445960 < baseStart_7445960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7445987 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 5]
def baseStart_7445987 : Nat := 118140960795 + 7445987 * 2 ^ 59
def prefixEnd_7445987 : Nat := 4983230072969 + 3 ^ 40 * 7445987 * 2
def baseEnd_7445987 : Nat := 3823370278129464275319035

theorem tailTrace_7445987 : CollatzResearch.WordTrace tailWord_7445987 prefixEnd_7445987 3823370278129464275319035 := by
  unfold tailWord_7445987
  simp only [CollatzResearch.WordTrace]
  refine ⟨271577456875468247181624215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181051637916978831454416143 271577456875468247181624215)
  ·
    refine ⟨407366185313202370772436323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271577456875468247181624215 407366185313202370772436323)
    ·
      refine ⟨611049277969803556158654485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407366185313202370772436323 611049277969803556158654485)
      ·
        refine ⟨28642934904834541694936929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 611049277969803556158654485 28642934904834541694936929)
        ·
          refine ⟨21482201178625906271202697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28642934904834541694936929 21482201178625906271202697)
          ·
            refine ⟨16111650883969429703402023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21482201178625906271202697 16111650883969429703402023)
            ·
              refine ⟨24167476325954144555103035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16111650883969429703402023 24167476325954144555103035)
              ·
                refine ⟨36251214488931216832654553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24167476325954144555103035 36251214488931216832654553)
                ·
                  refine ⟨27188410866698412624490915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36251214488931216832654553 27188410866698412624490915)
                  ·
                    refine ⟨40782616300047618936736373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27188410866698412624490915 40782616300047618936736373)
                    ·
                      refine ⟨3823370278129464275319035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40782616300047618936736373 3823370278129464275319035)
                      ·
                        rfl

theorem cell23_7445987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_7445987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7445987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7445987 prefixEnd_7445987 := by exact prefixLift 7445987
  have htrace : WordTrace (prefixWord ++ tailWord_7445987) baseStart_7445987 baseEnd_7445987 := by
    simpa [prefixWord, tailWord_7445987, baseEnd_7445987] using wordTrace_append hprefix tailTrace_7445987
  have hstable : (prefixWord ++ tailWord_7445987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7445987).length < 2 ^ (prefixWord ++ tailWord_7445987).sum := by decide
  have hdescent : baseEnd_7445987 < baseStart_7445987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7445987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446037 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 2, 5]
def baseStart_7446037 : Nat := 118140960795 + 7446037 * 2 ^ 59
def prefixEnd_7446037 : Nat := 4983230072969 + 3 ^ 40 * 7446037 * 2
def baseEnd_7446037 : Nat := 1274465317387396359897935

theorem tailTrace_7446037 : CollatzResearch.WordTrace tailWord_7446037 prefixEnd_7446037 1274465317387396359897935 := by
  unfold tailWord_7446037
  simp only [CollatzResearch.WordTrace]
  refine ⟨271579280525287105720944365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181052853683524737147296243 271579280525287105720944365)
  ·
    refine ⟨101842230196982664645354137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271579280525287105720944365 101842230196982664645354137)
    ·
      refine ⟨76381672647736998484015603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101842230196982664645354137 76381672647736998484015603)
      ·
        refine ⟨114572508971605497726023405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76381672647736998484015603 114572508971605497726023405)
        ·
          refine ⟨42964690864352061647258777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114572508971605497726023405 42964690864352061647258777)
          ·
            refine ⟨32223518148264046235444083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42964690864352061647258777 32223518148264046235444083)
            ·
              refine ⟨48335277222396069353166125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32223518148264046235444083 48335277222396069353166125)
              ·
                refine ⟨18125728958398526007437297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48335277222396069353166125 18125728958398526007437297)
                ·
                  refine ⟨13594296718798894505577973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18125728958398526007437297 13594296718798894505577973)
                  ·
                    refine ⟨1274465317387396359897935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13594296718798894505577973 1274465317387396359897935)
                    ·
                      rfl

theorem cell23_7446037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_7446037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446037 prefixEnd_7446037 := by exact prefixLift 7446037
  have htrace : WordTrace (prefixWord ++ tailWord_7446037) baseStart_7446037 baseEnd_7446037 := by
    simpa [prefixWord, tailWord_7446037, baseEnd_7446037] using wordTrace_append hprefix tailTrace_7446037
  have hstable : (prefixWord ++ tailWord_7446037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446037).length < 2 ^ (prefixWord ++ tailWord_7446037).sum := by decide
  have hdescent : baseEnd_7446037 < baseStart_7446037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446074 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2]
def baseStart_7446074 : Nat := 118140960795 + 7446074 * 2 ^ 59
def prefixEnd_7446074 : Nat := 4983230072969 + 3 ^ 40 * 7446074 * 2
def baseEnd_7446074 : Nat := 3823414950946405434931135

theorem tailTrace_7446074 : CollatzResearch.WordTrace tailWord_7446074 prefixEnd_7446074 3823414950946405434931135 := by
  unfold tailWord_7446074
  simp only [CollatzResearch.WordTrace]
  refine ⟨67895157506538265260010319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181053753350768707360027517 67895157506538265260010319)
  ·
    refine ⟨101842736259807397890015479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67895157506538265260010319 101842736259807397890015479)
    ·
      refine ⟨152764104389711096835023219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101842736259807397890015479 152764104389711096835023219)
      ·
        refine ⟨229146156584566645252534829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152764104389711096835023219 229146156584566645252534829)
        ·
          refine ⟨85929808719212491969700561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229146156584566645252534829 85929808719212491969700561)
          ·
            refine ⟨64447356539409368977275421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85929808719212491969700561 64447356539409368977275421)
            ·
              refine ⟨24167758702278513366478283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64447356539409368977275421 24167758702278513366478283)
              ·
                refine ⟨36251638053417770049717425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24167758702278513366478283 36251638053417770049717425)
                ·
                  refine ⟨27188728540063327537288069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36251638053417770049717425 27188728540063327537288069)
                  ·
                    refine ⟨5097886601261873913241513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27188728540063327537288069 5097886601261873913241513)
                    ·
                      refine ⟨3823414950946405434931135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5097886601261873913241513 3823414950946405434931135)
                      ·
                        rfl

theorem cell23_7446074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2].length) (baseStart_7446074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446074 prefixEnd_7446074 := by exact prefixLift 7446074
  have htrace : WordTrace (prefixWord ++ tailWord_7446074) baseStart_7446074 baseEnd_7446074 := by
    simpa [prefixWord, tailWord_7446074, baseEnd_7446074] using wordTrace_append hprefix tailTrace_7446074
  have hstable : (prefixWord ++ tailWord_7446074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446074).length < 2 ^ (prefixWord ++ tailWord_7446074).sum := by decide
  have hdescent : baseEnd_7446074 < baseStart_7446074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446080 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 10]
def baseStart_7446080 : Nat := 118140960795 + 7446080 * 2 ^ 59
def prefixEnd_7446080 : Nat := 4983230072969 + 3 ^ 40 * 7446080 * 2
def baseEnd_7446080 : Nat := 424824225758925823495123

theorem tailTrace_7446080 : CollatzResearch.WordTrace tailWord_7446080 prefixEnd_7446080 424824225758925823495123 := by
  unfold tailWord_7446080
  simp only [CollatzResearch.WordTrace]
  refine ⟨135790424432065662032379847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181053899242754216043173129 135790424432065662032379847)
  ·
    refine ⟨203685636648098493048569771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135790424432065662032379847 203685636648098493048569771)
    ·
      refine ⟨305528454972147739572854657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203685636648098493048569771 305528454972147739572854657)
      ·
        refine ⟨229146341229110804679640993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305528454972147739572854657 229146341229110804679640993)
        ·
          refine ⟨171859755921833103509730745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229146341229110804679640993 171859755921833103509730745)
          ·
            refine ⟨128894816941374827632298059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171859755921833103509730745 128894816941374827632298059)
            ·
              refine ⟨193342225412062241448447089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128894816941374827632298059 193342225412062241448447089)
              ·
                refine ⟨145006669059046681086335317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193342225412062241448447089 145006669059046681086335317)
                ·
                  refine ⟨424824225758925823495123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 145006669059046681086335317 424824225758925823495123)
                  ·
                    rfl

theorem cell23_7446080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 10].length) (baseStart_7446080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446080 prefixEnd_7446080 := by exact prefixLift 7446080
  have htrace : WordTrace (prefixWord ++ tailWord_7446080) baseStart_7446080 baseEnd_7446080 := by
    simpa [prefixWord, tailWord_7446080, baseEnd_7446080] using wordTrace_append hprefix tailTrace_7446080
  have hstable : (prefixWord ++ tailWord_7446080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446080).length < 2 ^ (prefixWord ++ tailWord_7446080).sum := by decide
  have hdescent : baseEnd_7446080 < baseStart_7446080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446117 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 1, 2, 6]
def baseStart_7446117 : Nat := 118140960795 + 7446117 * 2 ^ 59
def prefixEnd_7446117 : Nat := 4983230072969 + 3 ^ 40 * 7446117 * 2
def baseEnd_7446117 : Nat := 3823437030614548766693437

theorem tailTrace_7446117 : CollatzResearch.WordTrace tailWord_7446117 prefixEnd_7446117 3823437030614548766693437 := by
  unfold tailWord_7446117
  simp only [CollatzResearch.WordTrace]
  refine ⟨271582198364997279383856605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181054798909998186255904403 271582198364997279383856605)
  ·
    refine ⟨101843324386873979768946227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271582198364997279383856605 101843324386873979768946227)
    ·
      refine ⟨152764986580310969653419341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101843324386873979768946227 152764986580310969653419341)
      ·
        refine ⟨57286869967616613620032253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152764986580310969653419341 57286869967616613620032253)
        ·
          refine ⟨21482576237856230107512095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57286869967616613620032253 21482576237856230107512095)
          ·
            refine ⟨32223864356784345161268143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21482576237856230107512095 32223864356784345161268143)
            ·
              refine ⟨48335796535176517741902215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32223864356784345161268143 48335796535176517741902215)
              ·
                refine ⟨72503694802764776612853323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48335796535176517741902215 72503694802764776612853323)
                ·
                  refine ⟨108755542204147164919279985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72503694802764776612853323 108755542204147164919279985)
                  ·
                    refine ⟨81566656653110373689459989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108755542204147164919279985 81566656653110373689459989)
                    ·
                      refine ⟨3823437030614548766693437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81566656653110373689459989 3823437030614548766693437)
                      ·
                        rfl

theorem cell23_7446117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_7446117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446117 prefixEnd_7446117 := by exact prefixLift 7446117
  have htrace : WordTrace (prefixWord ++ tailWord_7446117) baseStart_7446117 baseEnd_7446117 := by
    simpa [prefixWord, tailWord_7446117, baseEnd_7446117] using wordTrace_append hprefix tailTrace_7446117
  have hstable : (prefixWord ++ tailWord_7446117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446117).length < 2 ^ (prefixWord ++ tailWord_7446117).sum := by decide
  have hdescent : baseEnd_7446117 < baseStart_7446117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446141 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 3, 1, 3]
def baseStart_7446141 : Nat := 118140960795 + 7446141 * 2 ^ 59
def prefixEnd_7446141 : Nat := 4983230072969 + 3 ^ 40 * 7446141 * 2
def baseEnd_7446141 : Nat := 3823449354150256672793327

theorem tailTrace_7446141 : CollatzResearch.WordTrace tailWord_7446141 prefixEnd_7446141 3823449354150256672793327 := by
  unfold tailWord_7446141
  simp only [CollatzResearch.WordTrace]
  refine ⟨271583073716910331482730277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181055382477940220988486851 271583073716910331482730277)
  ·
    refine ⟨50921826321920687153011927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271583073716910331482730277 50921826321920687153011927)
    ·
      refine ⟨76382739482881030729517891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50921826321920687153011927 76382739482881030729517891)
      ·
        refine ⟨114574109224321546094276837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76382739482881030729517891 114574109224321546094276837)
        ·
          refine ⟨21482645479560289892676907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114574109224321546094276837 21482645479560289892676907)
          ·
            refine ⟨32223968219340434839015361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21482645479560289892676907 32223968219340434839015361)
            ·
              refine ⟨24167976164505326129261521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32223968219340434839015361 24167976164505326129261521)
              ·
                refine ⟨18125982123378994596946141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24167976164505326129261521 18125982123378994596946141)
                ·
                  refine ⟨6797243296267122973854803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18125982123378994596946141 6797243296267122973854803)
                  ·
                    refine ⟨10195864944400684460782205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6797243296267122973854803 10195864944400684460782205)
                    ·
                      refine ⟨3823449354150256672793327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10195864944400684460782205 3823449354150256672793327)
                      ·
                        rfl

theorem cell23_7446141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_7446141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446141 prefixEnd_7446141 := by exact prefixLift 7446141
  have htrace : WordTrace (prefixWord ++ tailWord_7446141) baseStart_7446141 baseEnd_7446141 := by
    simpa [prefixWord, tailWord_7446141, baseEnd_7446141] using wordTrace_append hprefix tailTrace_7446141
  have hstable : (prefixWord ++ tailWord_7446141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446141).length < 2 ^ (prefixWord ++ tailWord_7446141).sum := by decide
  have hdescent : baseEnd_7446141 < baseStart_7446141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446144 : List Nat := [2, 1, 1, 2, 1, 4, 4, 2, 1, 5]
def baseStart_7446144 : Nat := 118140960795 + 7446144 * 2 ^ 59
def prefixEnd_7446144 : Nat := 4983230072969 + 3 ^ 40 * 7446144 * 2
def baseEnd_7446144 : Nat := 1274483631530740053685271

theorem tailTrace_7446144 : CollatzResearch.WordTrace tailWord_7446144 prefixEnd_7446144 1274483631530740053685271 := by
  unfold tailWord_7446144
  simp only [CollatzResearch.WordTrace]
  refine ⟨135791591567949731497544743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181055455423932975330059657 135791591567949731497544743)
  ·
    refine ⟨203687387351924597246317115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135791591567949731497544743 203687387351924597246317115)
    ·
      refine ⟨305531081027886895869475673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203687387351924597246317115 305531081027886895869475673)
      ·
        refine ⟨229148310770915171902106755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305531081027886895869475673 229148310770915171902106755)
        ·
          refine ⟨343722466156372757853160133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229148310770915171902106755 343722466156372757853160133)
          ·
            refine ⟨64447962404319892097467525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 343722466156372757853160133 64447962404319892097467525)
            ·
              refine ⟨12083992950809979768275161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64447962404319892097467525 12083992950809979768275161)
              ·
                refine ⟨9062994713107484826206371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12083992950809979768275161 9062994713107484826206371)
                ·
                  refine ⟨13594492069661227239309557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9062994713107484826206371 13594492069661227239309557)
                  ·
                    refine ⟨1274483631530740053685271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13594492069661227239309557 1274483631530740053685271)
                    ·
                      rfl

theorem cell23_7446144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 1, 5].length) (baseStart_7446144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446144 prefixEnd_7446144 := by exact prefixLift 7446144
  have htrace : WordTrace (prefixWord ++ tailWord_7446144) baseStart_7446144 baseEnd_7446144 := by
    simpa [prefixWord, tailWord_7446144, baseEnd_7446144] using wordTrace_append hprefix tailTrace_7446144
  have hstable : (prefixWord ++ tailWord_7446144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446144).length < 2 ^ (prefixWord ++ tailWord_7446144).sum := by decide
  have hdescent : baseEnd_7446144 < baseStart_7446144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446152 : List Nat := [2, 1, 3, 5, 2, 1, 1, 3, 1, 4]
def baseStart_7446152 : Nat := 118140960795 + 7446152 * 2 ^ 59
def prefixEnd_7446152 : Nat := 4983230072969 + 3 ^ 40 * 7446152 * 2
def baseEnd_7446152 : Nat := 1274485000812485376585259

theorem tailTrace_7446152 : CollatzResearch.WordTrace tailWord_7446152 prefixEnd_7446152 1274485000812485376585259 := by
  unfold tailWord_7446152
  simp only [CollatzResearch.WordTrace]
  refine ⟨135791737459935240180690355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181055649946580320240920473 135791737459935240180690355)
  ·
    refine ⟨203687606189902860271035533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135791737459935240180690355 203687606189902860271035533)
    ·
      refine ⟨76382852321213572601638325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203687606189902860271035533 76382852321213572601638325)
      ·
        refine ⟨7160892405113772431403593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76382852321213572601638325 7160892405113772431403593)
        ·
          refine ⟨5370669303835329323552695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7160892405113772431403593 5370669303835329323552695)
          ·
            refine ⟨8056003955752993985329043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5370669303835329323552695 8056003955752993985329043)
            ·
              refine ⟨12084005933629490977993565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8056003955752993985329043 12084005933629490977993565)
              ·
                refine ⟨4531502225111059116747587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12084005933629490977993565 4531502225111059116747587)
                ·
                  refine ⟨6797253337666588675121381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4531502225111059116747587 6797253337666588675121381)
                  ·
                    refine ⟨1274485000812485376585259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6797253337666588675121381 1274485000812485376585259)
                    ·
                      rfl

theorem cell23_7446152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_7446152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446152 prefixEnd_7446152 := by exact prefixLift 7446152
  have htrace : WordTrace (prefixWord ++ tailWord_7446152) baseStart_7446152 baseEnd_7446152 := by
    simpa [prefixWord, tailWord_7446152, baseEnd_7446152] using wordTrace_append hprefix tailTrace_7446152
  have hstable : (prefixWord ++ tailWord_7446152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446152).length < 2 ^ (prefixWord ++ tailWord_7446152).sum := by decide
  have hdescent : baseEnd_7446152 < baseStart_7446152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446175 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 3, 1, 3]
def baseStart_7446175 : Nat := 118140960795 + 7446175 * 2 ^ 59
def prefixEnd_7446175 : Nat := 4983230072969 + 3 ^ 40 * 7446175 * 2
def baseEnd_7446175 : Nat := 3823466812492509539768171

theorem tailTrace_7446175 : CollatzResearch.WordTrace tailWord_7446175 prefixEnd_7446175 3823466812492509539768171 := by
  unfold tailWord_7446175
  simp only [CollatzResearch.WordTrace]
  refine ⟨271584313798787155289467979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181056209199191436859645319 271584313798787155289467979)
  ·
    refine ⟨407376470698180732934201969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271584313798787155289467979 407376470698180732934201969)
    ·
      refine ⟨305532353023635549700651477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407376470698180732934201969 305532353023635549700651477)
      ·
        refine ⟨7160914523991458196109019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 305532353023635549700651477 7160914523991458196109019)
        ·
          refine ⟨10741371785987187294163529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7160914523991458196109019 10741371785987187294163529)
          ·
            refine ⟨8056028839490390470622647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10741371785987187294163529 8056028839490390470622647)
            ·
              refine ⟨12084043259235585705933971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8056028839490390470622647 12084043259235585705933971)
              ·
                refine ⟨18126064888853378558900957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12084043259235585705933971 18126064888853378558900957)
                ·
                  refine ⟨6797274333320016959587859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18126064888853378558900957 6797274333320016959587859)
                  ·
                    refine ⟨10195911499980025439381789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6797274333320016959587859 10195911499980025439381789)
                    ·
                      refine ⟨3823466812492509539768171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10195911499980025439381789 3823466812492509539768171)
                      ·
                        rfl

theorem cell23_7446175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_7446175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446175 prefixEnd_7446175 := by exact prefixLift 7446175
  have htrace : WordTrace (prefixWord ++ tailWord_7446175) baseStart_7446175 baseEnd_7446175 := by
    simpa [prefixWord, tailWord_7446175, baseEnd_7446175] using wordTrace_append hprefix tailTrace_7446175
  have hstable : (prefixWord ++ tailWord_7446175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446175).length < 2 ^ (prefixWord ++ tailWord_7446175).sum := by decide
  have hdescent : baseEnd_7446175 < baseStart_7446175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446198 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_7446198 : Nat := 118140960795 + 7446198 * 2 ^ 59
def prefixEnd_7446198 : Nat := 4983230072969 + 3 ^ 40 * 7446198 * 2
def baseEnd_7446198 : Nat := 3823478622547562949780565

theorem tailTrace_7446198 : CollatzResearch.WordTrace tailWord_7446198 prefixEnd_7446198 3823478622547562949780565 := by
  unfold tailWord_7446198
  simp only [CollatzResearch.WordTrace]
  refine ⟨16974072042356489388597203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181056768451802553478370165 16974072042356489388597203)
  ·
    refine ⟨25461108063534734082895805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16974072042356489388597203 25461108063534734082895805)
    ·
      refine ⟨9547915523825525281085927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25461108063534734082895805 9547915523825525281085927)
      ·
        refine ⟨14321873285738287921628891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9547915523825525281085927 14321873285738287921628891)
        ·
          refine ⟨21482809928607431882443337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14321873285738287921628891 21482809928607431882443337)
          ·
            refine ⟨16112107446455573911832503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21482809928607431882443337 16112107446455573911832503)
            ·
              refine ⟨24168161169683360867748755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16112107446455573911832503 24168161169683360867748755)
              ·
                refine ⟨36252241754525041301623133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24168161169683360867748755 36252241754525041301623133)
                ·
                  refine ⟨13594590657946890488108675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36252241754525041301623133 13594590657946890488108675)
                  ·
                    refine ⟨20391885986920335732163013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13594590657946890488108675 20391885986920335732163013)
                    ·
                      refine ⟨3823478622547562949780565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20391885986920335732163013 3823478622547562949780565)
                      ·
                        rfl

theorem cell23_7446198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_7446198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446198 prefixEnd_7446198 := by exact prefixLift 7446198
  have htrace : WordTrace (prefixWord ++ tailWord_7446198) baseStart_7446198 baseEnd_7446198 := by
    simpa [prefixWord, tailWord_7446198, baseEnd_7446198] using wordTrace_append hprefix tailTrace_7446198
  have hstable : (prefixWord ++ tailWord_7446198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446198).length < 2 ^ (prefixWord ++ tailWord_7446198).sum := by decide
  have hdescent : baseEnd_7446198 < baseStart_7446198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446201 : List Nat := [1, 2, 1, 4, 1, 1, 5, 2, 1, 2, 3]
def baseStart_7446201 : Nat := 118140960795 + 7446201 * 2 ^ 59
def prefixEnd_7446201 : Nat := 4983230072969 + 3 ^ 40 * 7446201 * 2
def baseEnd_7446201 : Nat := 3823480162989526438043051

theorem tailTrace_7446201 : CollatzResearch.WordTrace tailWord_7446201 prefixEnd_7446201 3823480162989526438043051 := by
  unfold tailWord_7446201
  simp only [CollatzResearch.WordTrace]
  refine ⟨271585262096692961729914457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181056841397795307819942971 271585262096692961729914457)
  ·
    refine ⟨203688946572519721297435843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271585262096692961729914457 203688946572519721297435843)
    ·
      refine ⟨305533419858779581946153765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203688946572519721297435843 305533419858779581946153765)
      ·
        refine ⟨57287516223521171614903831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305533419858779581946153765 57287516223521171614903831)
        ·
          refine ⟨85931274335281757422355747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57287516223521171614903831 85931274335281757422355747)
          ·
            refine ⟨128896911502922636133533621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85931274335281757422355747 128896911502922636133533621)
            ·
              refine ⟨12084085453398997137518777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128896911502922636133533621 12084085453398997137518777)
              ·
                refine ⟨9063064090049247853139083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12084085453398997137518777 9063064090049247853139083)
                ·
                  refine ⟨13594596135073871779708625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9063064090049247853139083 13594596135073871779708625)
                  ·
                    refine ⟨10195947101305403834781469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13594596135073871779708625 10195947101305403834781469)
                    ·
                      refine ⟨3823480162989526438043051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10195947101305403834781469 3823480162989526438043051)
                      ·
                        rfl

theorem cell23_7446201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_7446201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446201 prefixEnd_7446201 := by exact prefixLift 7446201
  have htrace : WordTrace (prefixWord ++ tailWord_7446201) baseStart_7446201 baseEnd_7446201 := by
    simpa [prefixWord, tailWord_7446201, baseEnd_7446201] using wordTrace_append hprefix tailTrace_7446201
  have hstable : (prefixWord ++ tailWord_7446201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446201).length < 2 ^ (prefixWord ++ tailWord_7446201).sum := by decide
  have hdescent : baseEnd_7446201 < baseStart_7446201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446218 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 1, 1, 5]
def baseStart_7446218 : Nat := 118140960795 + 7446218 * 2 ^ 59
def prefixEnd_7446218 : Nat := 4983230072969 + 3 ^ 40 * 7446218 * 2
def baseEnd_7446218 : Nat := 3823488892160652871530473

theorem tailTrace_7446218 : CollatzResearch.WordTrace tailWord_7446218 prefixEnd_7446218 3823488892160652871530473 := by
  unfold tailWord_7446218
  simp only [CollatzResearch.WordTrace]
  refine ⟨67896470534407843408320827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181057254758420915755522205 67896470534407843408320827)
  ·
    refine ⟨101844705801611765112481241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67896470534407843408320827 101844705801611765112481241)
    ·
      refine ⟨76383529351208823834360931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101844705801611765112481241 76383529351208823834360931)
      ·
        refine ⟨114575294026813235751541397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76383529351208823834360931 114575294026813235751541397)
        ·
          refine ⟨5370716907506870425853503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114575294026813235751541397 5370716907506870425853503)
          ·
            refine ⟨8056075361260305638780255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5370716907506870425853503 8056075361260305638780255)
            ·
              refine ⟨12084113041890458458170383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8056075361260305638780255 12084113041890458458170383)
              ·
                refine ⟨18126169562835687687255575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12084113041890458458170383 18126169562835687687255575)
                ·
                  refine ⟨27189254344253531530883363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18126169562835687687255575 27189254344253531530883363)
                  ·
                    refine ⟨40783881516380297296325045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27189254344253531530883363 40783881516380297296325045)
                    ·
                      refine ⟨3823488892160652871530473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40783881516380297296325045 3823488892160652871530473)
                      ·
                        rfl

theorem cell23_7446218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_7446218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446218 prefixEnd_7446218 := by exact prefixLift 7446218
  have htrace : WordTrace (prefixWord ++ tailWord_7446218) baseStart_7446218 baseEnd_7446218 := by
    simpa [prefixWord, tailWord_7446218, baseEnd_7446218] using wordTrace_append hprefix tailTrace_7446218
  have hstable : (prefixWord ++ tailWord_7446218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446218).length < 2 ^ (prefixWord ++ tailWord_7446218).sum := by decide
  have hdescent : baseEnd_7446218 < baseStart_7446218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446248 : List Nat := [2, 1, 4, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_7446248 : Nat := 118140960795 + 7446248 * 2 ^ 59
def prefixEnd_7446248 : Nat := 4983230072969 + 3 ^ 40 * 7446248 * 2
def baseEnd_7446248 : Nat := 3823504296580287754155335

theorem tailTrace_7446248 : CollatzResearch.WordTrace tailWord_7446248 prefixEnd_7446248 3823504296580287754155335 := by
  unfold tailWord_7446248
  simp only [CollatzResearch.WordTrace]
  refine ⟨135793488163761344378437699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181057984218348459171250265 135793488163761344378437699)
  ·
    refine ⟨203690232245642016567656549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135793488163761344378437699 203690232245642016567656549)
    ·
      refine ⟨38191918546057878106435603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203690232245642016567656549 38191918546057878106435603)
      ·
        refine ⟨57287877819086817159653405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38191918546057878106435603 57287877819086817159653405)
        ·
          refine ⟨21482954182157556434870027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57287877819086817159653405 21482954182157556434870027)
          ·
            refine ⟨32224431273236334652305041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21482954182157556434870027 32224431273236334652305041)
            ·
              refine ⟨24168323454927250989228781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32224431273236334652305041 24168323454927250989228781)
              ·
                refine ⟨9063121295597719120960793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24168323454927250989228781 9063121295597719120960793)
                ·
                  refine ⟨6797340971698289340720595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9063121295597719120960793 6797340971698289340720595)
                  ·
                    refine ⟨10196011457547434011080893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6797340971698289340720595 10196011457547434011080893)
                    ·
                      refine ⟨3823504296580287754155335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10196011457547434011080893 3823504296580287754155335)
                      ·
                        rfl

theorem cell23_7446248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_7446248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446248 prefixEnd_7446248 := by exact prefixLift 7446248
  have htrace : WordTrace (prefixWord ++ tailWord_7446248) baseStart_7446248 baseEnd_7446248 := by
    simpa [prefixWord, tailWord_7446248, baseEnd_7446248] using wordTrace_append hprefix tailTrace_7446248
  have hstable : (prefixWord ++ tailWord_7446248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446248).length < 2 ^ (prefixWord ++ tailWord_7446248).sum := by decide
  have hdescent : baseEnd_7446248 < baseStart_7446248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446254 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_7446254 : Nat := 118140960795 + 7446254 * 2 ^ 59
def prefixEnd_7446254 : Nat := 4983230072969 + 3 ^ 40 * 7446254 * 2
def baseEnd_7446254 : Nat := 3823507377464214730680307

theorem tailTrace_7446254 : CollatzResearch.WordTrace tailWord_7446254 prefixEnd_7446254 3823507377464214730680307 := by
  unfold tailWord_7446254
  simp only [CollatzResearch.WordTrace]
  refine ⟨33948399395687618972699227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181058130110333967854395877 33948399395687618972699227)
  ·
    refine ⟨50922599093531428459048841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33948399395687618972699227 50922599093531428459048841)
    ·
      refine ⟨38191949320148571344286631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50922599093531428459048841 38191949320148571344286631)
      ·
        refine ⟨57287923980222857016429947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38191949320148571344286631 57287923980222857016429947)
        ·
          refine ⟨85931885970334285524644921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57287923980222857016429947 85931885970334285524644921)
          ·
            refine ⟨64448914477750714143483691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85931885970334285524644921 64448914477750714143483691)
            ·
              refine ⟨96673371716626071215225537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64448914477750714143483691 96673371716626071215225537)
              ·
                refine ⟨72505028787469553411419153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96673371716626071215225537 72505028787469553411419153)
                ·
                  refine ⟨54378771590602165058564365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72505028787469553411419153 54378771590602165058564365)
                  ·
                    refine ⟨20392039346475811896961637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54378771590602165058564365 20392039346475811896961637)
                    ·
                      refine ⟨3823507377464214730680307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20392039346475811896961637 3823507377464214730680307)
                      ·
                        rfl

theorem cell23_7446254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_7446254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446254 prefixEnd_7446254 := by exact prefixLift 7446254
  have htrace : WordTrace (prefixWord ++ tailWord_7446254) baseStart_7446254 baseEnd_7446254 := by
    simpa [prefixWord, tailWord_7446254, baseEnd_7446254] using wordTrace_append hprefix tailTrace_7446254
  have hstable : (prefixWord ++ tailWord_7446254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446254).length < 2 ^ (prefixWord ++ tailWord_7446254).sum := by decide
  have hdescent : baseEnd_7446254 < baseStart_7446254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446258 : List Nat := [3, 2, 1, 3, 1, 1, 2, 4, 1, 3, 2]
def baseStart_7446258 : Nat := 118140960795 + 7446258 * 2 ^ 59
def prefixEnd_7446258 : Nat := 4983230072969 + 3 ^ 40 * 7446258 * 2
def baseEnd_7446258 : Nat := 3823509431386832715030289

theorem tailTrace_7446258 : CollatzResearch.WordTrace tailWord_7446258 prefixEnd_7446258 3823509431386832715030289 := by
  unfold tailWord_7446258
  simp only [CollatzResearch.WordTrace]
  refine ⟨67896835264371615116184857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181058227371657640309826285 67896835264371615116184857)
  ·
    refine ⟨50922626448278711337138643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67896835264371615116184857 50922626448278711337138643)
    ·
      refine ⟨76383939672418067005707965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50922626448278711337138643 76383939672418067005707965)
      ·
        refine ⟨28643977377156775127140487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76383939672418067005707965 28643977377156775127140487)
        ·
          refine ⟨42965966065735162690710731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28643977377156775127140487 42965966065735162690710731)
          ·
            refine ⟨64448949098602744036066097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42965966065735162690710731 64448949098602744036066097)
            ·
              refine ⟨48336711823952058027049573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64448949098602744036066097 48336711823952058027049573)
              ·
                refine ⟨9063133466991010880071795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48336711823952058027049573 9063133466991010880071795)
                ·
                  refine ⟨13594700200486516320107693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9063133466991010880071795 13594700200486516320107693)
                  ·
                    refine ⟨5098012575182443620040385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13594700200486516320107693 5098012575182443620040385)
                    ·
                      refine ⟨3823509431386832715030289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5098012575182443620040385 3823509431386832715030289)
                      ·
                        rfl

theorem cell23_7446258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_7446258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446258 prefixEnd_7446258 := by exact prefixLift 7446258
  have htrace : WordTrace (prefixWord ++ tailWord_7446258) baseStart_7446258 baseEnd_7446258 := by
    simpa [prefixWord, tailWord_7446258, baseEnd_7446258] using wordTrace_append hprefix tailTrace_7446258
  have hstable : (prefixWord ++ tailWord_7446258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446258).length < 2 ^ (prefixWord ++ tailWord_7446258).sum := by decide
  have hdescent : baseEnd_7446258 < baseStart_7446258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446271 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 1, 4, 2]
def baseStart_7446271 : Nat := 118140960795 + 7446271 * 2 ^ 59
def prefixEnd_7446271 : Nat := 4983230072969 + 3 ^ 40 * 7446271 * 2
def baseEnd_7446271 : Nat := 3823516106635341164167729

theorem tailTrace_7446271 : CollatzResearch.WordTrace tailWord_7446271 prefixEnd_7446271 3823516106635341164167729 := by
  unfold tailWord_7446271
  simp only [CollatzResearch.WordTrace]
  refine ⟨271587815206439363684962667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181058543470959575789975111 271587815206439363684962667)
  ·
    refine ⟨407381722809659045527444001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271587815206439363684962667 407381722809659045527444001)
    ·
      refine ⟨305536292107244284145583001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407381722809659045527444001 305536292107244284145583001)
      ·
        refine ⟨229152219080433213109187251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305536292107244284145583001 229152219080433213109187251)
        ·
          refine ⟨343728328620649819663780877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229152219080433213109187251 343728328620649819663780877)
          ·
            refine ⟨128898123232743682373917829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343728328620649819663780877 128898123232743682373917829)
            ·
              refine ⟨24168398106139440445109593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128898123232743682373917829 24168398106139440445109593)
              ·
                refine ⟨18126298579604580333832195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24168398106139440445109593 18126298579604580333832195)
                ·
                  refine ⟨27189447869406870500748293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18126298579604580333832195 27189447869406870500748293)
                  ·
                    refine ⟨5098021475513788218890305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27189447869406870500748293 5098021475513788218890305)
                    ·
                      refine ⟨3823516106635341164167729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5098021475513788218890305 3823516106635341164167729)
                      ·
                        rfl

theorem cell23_7446271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 4, 2].length) (baseStart_7446271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446271 prefixEnd_7446271 := by exact prefixLift 7446271
  have htrace : WordTrace (prefixWord ++ tailWord_7446271) baseStart_7446271 baseEnd_7446271 := by
    simpa [prefixWord, tailWord_7446271, baseEnd_7446271] using wordTrace_append hprefix tailTrace_7446271
  have hstable : (prefixWord ++ tailWord_7446271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446271).length < 2 ^ (prefixWord ++ tailWord_7446271).sum := by decide
  have hdescent : baseEnd_7446271 < baseStart_7446271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446284 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 2, 2, 4]
def baseStart_7446284 : Nat := 118140960795 + 7446284 * 2 ^ 59
def prefixEnd_7446284 : Nat := 4983230072969 + 3 ^ 40 * 7446284 * 2
def baseEnd_7446284 : Nat := 3823522781883849613305169

theorem tailTrace_7446284 : CollatzResearch.WordTrace tailWord_7446284 prefixEnd_7446284 3823522781883849613305169 := by
  unfold tailWord_7446284
  simp only [CollatzResearch.WordTrace]
  refine ⟨135794144677696133452592953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181058859570261511270123937 135794144677696133452592953)
  ·
    refine ⟨101845608508272100089444715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135794144677696133452592953 101845608508272100089444715)
    ·
      refine ⟨152768412762408150134167073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101845608508272100089444715 152768412762408150134167073)
      ·
        refine ⟨114576309571806112600625305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152768412762408150134167073 114576309571806112600625305)
        ·
          refine ⟨85932232178854584450468979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114576309571806112600625305 85932232178854584450468979)
          ·
            refine ⟨128898348268281876675703469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85932232178854584450468979 128898348268281876675703469)
            ·
              refine ⟨48336880600605703753388801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128898348268281876675703469 48336880600605703753388801)
              ·
                refine ⟨36252660450454277815041601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48336880600605703753388801 36252660450454277815041601)
                ·
                  refine ⟨27189495337840708361281201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36252660450454277815041601 27189495337840708361281201)
                  ·
                    refine ⟨20392121503380531270960901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27189495337840708361281201 20392121503380531270960901)
                    ·
                      refine ⟨3823522781883849613305169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20392121503380531270960901 3823522781883849613305169)
                      ·
                        rfl

theorem cell23_7446284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_7446284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446284 prefixEnd_7446284 := by exact prefixLift 7446284
  have htrace : WordTrace (prefixWord ++ tailWord_7446284) baseStart_7446284 baseEnd_7446284 := by
    simpa [prefixWord, tailWord_7446284, baseEnd_7446284] using wordTrace_append hprefix tailTrace_7446284
  have hstable : (prefixWord ++ tailWord_7446284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446284).length < 2 ^ (prefixWord ++ tailWord_7446284).sum := by decide
  have hdescent : baseEnd_7446284 < baseStart_7446284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446287 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 9]
def baseStart_7446287 : Nat := 118140960795 + 7446287 * 2 ^ 59
def prefixEnd_7446287 : Nat := 4983230072969 + 3 ^ 40 * 7446287 * 2
def baseEnd_7446287 : Nat := 3823524322325813101567655

theorem tailTrace_7446287 : CollatzResearch.WordTrace tailWord_7446287 prefixEnd_7446287 3823524322325813101567655 := by
  unfold tailWord_7446287
  simp only [CollatzResearch.WordTrace]
  refine ⟨271588398774381398417545115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181058932516254265611696743 271588398774381398417545115)
  ·
    refine ⟨407382598161572097626317673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271588398774381398417545115 407382598161572097626317673)
    ·
      refine ⟨305536948621179073219738255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407382598161572097626317673 305536948621179073219738255)
      ·
        refine ⟨458305422931768609829607383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305536948621179073219738255 458305422931768609829607383)
        ·
          refine ⟨687458134397652914744411075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458305422931768609829607383 687458134397652914744411075)
          ·
            refine ⟨1031187201596479372116616613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687458134397652914744411075 1031187201596479372116616613)
            ·
              refine ⟨193347600299339882271865615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1031187201596479372116616613 193347600299339882271865615)
              ·
                refine ⟨290021400449009823407798423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193347600299339882271865615 290021400449009823407798423)
                ·
                  refine ⟨435032100673514735111697635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 290021400449009823407798423 435032100673514735111697635)
                  ·
                    refine ⟨652548151010272102667546453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 435032100673514735111697635 652548151010272102667546453)
                    ·
                      refine ⟨3823524322325813101567655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 652548151010272102667546453 3823524322325813101567655)
                      ·
                        rfl

theorem cell23_7446287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_7446287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446287 prefixEnd_7446287 := by exact prefixLift 7446287
  have htrace : WordTrace (prefixWord ++ tailWord_7446287) baseStart_7446287 baseEnd_7446287 := by
    simpa [prefixWord, tailWord_7446287, baseEnd_7446287] using wordTrace_append hprefix tailTrace_7446287
  have hstable : (prefixWord ++ tailWord_7446287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446287).length < 2 ^ (prefixWord ++ tailWord_7446287).sum := by decide
  have hdescent : baseEnd_7446287 < baseStart_7446287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446328 : List Nat := [2, 1, 2, 1, 3, 5, 1, 3, 5]
def baseStart_7446328 : Nat := 118140960795 + 7446328 * 2 ^ 59
def prefixEnd_7446328 : Nat := 4983230072969 + 3 ^ 40 * 7446328 * 2
def baseEnd_7446328 : Nat := 424838375003627493461663

theorem tailTrace_7446328 : CollatzResearch.WordTrace tailWord_7446328 prefixEnd_7446328 424838375003627493461663 := by
  unfold tailWord_7446328
  simp only [CollatzResearch.WordTrace]
  refine ⟨135794947083616431209893819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181059929444821908279858425 135794947083616431209893819)
  ·
    refine ⟨203692420625424646814840729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135794947083616431209893819 203692420625424646814840729)
    ·
      refine ⟨152769315469068485111130547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203692420625424646814840729 152769315469068485111130547)
      ·
        refine ⟨229153973203602727666695821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152769315469068485111130547 229153973203602727666695821)
        ·
          refine ⟨85932739951351022875010933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229153973203602727666695821 85932739951351022875010933)
          ·
            refine ⟨8056194370439158394532275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85932739951351022875010933 8056194370439158394532275)
            ·
              refine ⟨12084291555658737591798413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8056194370439158394532275 12084291555658737591798413)
              ·
                refine ⟨4531609333372026596924405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12084291555658737591798413 4531609333372026596924405)
                ·
                  refine ⟨424838375003627493461663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4531609333372026596924405 424838375003627493461663)
                  ·
                    rfl

theorem cell23_7446328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 3, 5].length) (baseStart_7446328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446328 prefixEnd_7446328 := by exact prefixLift 7446328
  have htrace : WordTrace (prefixWord ++ tailWord_7446328) baseStart_7446328 baseEnd_7446328 := by
    simpa [prefixWord, tailWord_7446328, baseEnd_7446328] using wordTrace_append hprefix tailTrace_7446328
  have hstable : (prefixWord ++ tailWord_7446328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446328).length < 2 ^ (prefixWord ++ tailWord_7446328).sum := by decide
  have hdescent : baseEnd_7446328 < baseStart_7446328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446361 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 1, 6, 2]
def baseStart_7446361 : Nat := 118140960795 + 7446361 * 2 ^ 59
def prefixEnd_7446361 : Nat := 4983230072969 + 3 ^ 40 * 7446361 * 2
def baseEnd_7446361 : Nat := 3823562319894245812042315

theorem tailTrace_7446361 : CollatzResearch.WordTrace tailWord_7446361 prefixEnd_7446361 3823562319894245812042315 := by
  unfold tailWord_7446361
  simp only [CollatzResearch.WordTrace]
  refine ⟨271591097776113309055738937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181060731850742206037159291 271591097776113309055738937)
  ·
    refine ⟨203693323332084981791804203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271591097776113309055738937 203693323332084981791804203)
    ·
      refine ⟨305539984998127472687706305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203693323332084981791804203 305539984998127472687706305)
      ·
        refine ⟨229154988748595604515779729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305539984998127472687706305 229154988748595604515779729)
        ·
          refine ⟨171866241561446703386834797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229154988748595604515779729 171866241561446703386834797)
          ·
            refine ⟨64449840585542513770063049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171866241561446703386834797 64449840585542513770063049)
            ·
              refine ⟨48337380439156885327547287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64449840585542513770063049 48337380439156885327547287)
              ·
                refine ⟨72506070658735327991320931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48337380439156885327547287 72506070658735327991320931)
                ·
                  refine ⟨108759105988102991986981397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72506070658735327991320931 108759105988102991986981397)
                  ·
                    refine ⟨5098083093192327749389753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108759105988102991986981397 5098083093192327749389753)
                    ·
                      refine ⟨3823562319894245812042315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5098083093192327749389753 3823562319894245812042315)
                      ·
                        rfl

theorem cell23_7446361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 6, 2].length) (baseStart_7446361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446361 prefixEnd_7446361 := by exact prefixLift 7446361
  have htrace : WordTrace (prefixWord ++ tailWord_7446361) baseStart_7446361 baseEnd_7446361 := by
    simpa [prefixWord, tailWord_7446361, baseEnd_7446361] using wordTrace_append hprefix tailTrace_7446361
  have hstable : (prefixWord ++ tailWord_7446361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446361).length < 2 ^ (prefixWord ++ tailWord_7446361).sum := by decide
  have hdescent : baseEnd_7446361 < baseStart_7446361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446381 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_7446381 : Nat := 118140960795 + 7446381 * 2 ^ 59
def prefixEnd_7446381 : Nat := 4983230072969 + 3 ^ 40 * 7446381 * 2
def baseEnd_7446381 : Nat := 3823572589507335733792223

theorem tailTrace_7446381 : CollatzResearch.WordTrace tailWord_7446381 prefixEnd_7446381 3823572589507335733792223 := by
  unfold tailWord_7446381
  simp only [CollatzResearch.WordTrace]
  refine ⟨271591827236040852471466997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181061218157360568314311331 271591827236040852471466997)
  ·
    refine ⟨25461733803378829919200031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 271591827236040852471466997 25461733803378829919200031)
    ·
      refine ⟨38192600705068244878800047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25461733803378829919200031 38192600705068244878800047)
      ·
        refine ⟨57288901057602367318200071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38192600705068244878800047 57288901057602367318200071)
        ·
          refine ⟨85933351586403550977300107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57288901057602367318200071 85933351586403550977300107)
          ·
            refine ⟨128900027379605326465950161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85933351586403550977300107 128900027379605326465950161)
            ·
              refine ⟨96675020534703994849462621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128900027379605326465950161 96675020534703994849462621)
              ·
                refine ⟨36253132700513998068548483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96675020534703994849462621 36253132700513998068548483)
                ·
                  refine ⟨54379699050770997102822725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36253132700513998068548483 54379699050770997102822725)
                  ·
                    refine ⟨10196193572019561956779261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54379699050770997102822725 10196193572019561956779261)
                    ·
                      refine ⟨3823572589507335733792223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10196193572019561956779261 3823572589507335733792223)
                      ·
                        rfl

theorem cell23_7446381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_7446381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446381 prefixEnd_7446381 := by exact prefixLift 7446381
  have htrace : WordTrace (prefixWord ++ tailWord_7446381) baseStart_7446381 baseEnd_7446381 := by
    simpa [prefixWord, tailWord_7446381, baseEnd_7446381] using wordTrace_append hprefix tailTrace_7446381
  have hstable : (prefixWord ++ tailWord_7446381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446381).length < 2 ^ (prefixWord ++ tailWord_7446381).sum := by decide
  have hdescent : baseEnd_7446381 < baseStart_7446381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446418 : List Nat := [3, 2, 3, 2, 1, 1, 2, 3, 6]
def baseStart_7446418 : Nat := 118140960795 + 7446418 * 2 ^ 59
def prefixEnd_7446418 : Nat := 4983230072969 + 3 ^ 40 * 7446418 * 2
def baseEnd_7446418 : Nat := 424843509810172454336617

theorem tailTrace_7446418 : CollatzResearch.WordTrace tailWord_7446418 prefixEnd_7446418 424843509810172454336617 := by
  unfold tailWord_7446418
  simp only [CollatzResearch.WordTrace]
  refine ⟨67898294184226701947640977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181062117824604538527042605 67898294184226701947640977)
  ·
    refine ⟨50923720638170026460730733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67898294184226701947640977 50923720638170026460730733)
    ·
      refine ⟨19096395239313759922774025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50923720638170026460730733 19096395239313759922774025)
      ·
        refine ⟨14322296429485319942080519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19096395239313759922774025 14322296429485319942080519)
        ·
          refine ⟨21483444644227979913120779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14322296429485319942080519 21483444644227979913120779)
          ·
            refine ⟨32225166966341969869681169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21483444644227979913120779 32225166966341969869681169)
            ·
              refine ⟨24168875224756477402260877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32225166966341969869681169 24168875224756477402260877)
              ·
                refine ⟨9063328209283679025847829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24168875224756477402260877 9063328209283679025847829)
                ·
                  refine ⟨424843509810172454336617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9063328209283679025847829 424843509810172454336617)
                  ·
                    rfl

theorem cell23_7446418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_7446418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446418 prefixEnd_7446418 := by exact prefixLift 7446418
  have htrace : WordTrace (prefixWord ++ tailWord_7446418) baseStart_7446418 baseEnd_7446418 := by
    simpa [prefixWord, tailWord_7446418, baseEnd_7446418] using wordTrace_append hprefix tailTrace_7446418
  have hstable : (prefixWord ++ tailWord_7446418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446418).length < 2 ^ (prefixWord ++ tailWord_7446418).sum := by decide
  have hdescent : baseEnd_7446418 < baseStart_7446418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446452 : List Nat := [2, 5, 2, 1, 2, 2, 1, 2, 6]
def baseStart_7446452 : Nat := 118140960795 + 7446452 * 2 ^ 59
def prefixEnd_7446452 : Nat := 4983230072969 + 3 ^ 40 * 7446452 * 2
def baseEnd_7446452 : Nat := 424845449625978328444933

theorem tailTrace_7446452 : CollatzResearch.WordTrace tailWord_7446452 prefixEnd_7446452 424845449625978328444933 := by
  unfold tailWord_7446452
  simp only [CollatzResearch.WordTrace]
  refine ⟨135797208409391815798650805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181062944545855754398201073 135797208409391815798650805)
  ·
    refine ⟨12730988288380482731123513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135797208409391815798650805 12730988288380482731123513)
    ·
      refine ⟨9548241216285362048342635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12730988288380482731123513 9548241216285362048342635)
      ·
        refine ⟨14322361824428043072513953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9548241216285362048342635 14322361824428043072513953)
        ·
          refine ⟨10741771368321032304385465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14322361824428043072513953 10741771368321032304385465)
          ·
            refine ⟨8056328526240774228289099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10741771368321032304385465 8056328526240774228289099)
            ·
              refine ⟨12084492789361161342433649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8056328526240774228289099 12084492789361161342433649)
              ·
                refine ⟨9063369592020871006825237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12084492789361161342433649 9063369592020871006825237)
                ·
                  refine ⟨424845449625978328444933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9063369592020871006825237 424845449625978328444933)
                  ·
                    rfl

theorem cell23_7446452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_7446452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446452 prefixEnd_7446452 := by exact prefixLift 7446452
  have htrace : WordTrace (prefixWord ++ tailWord_7446452) baseStart_7446452 baseEnd_7446452 := by
    simpa [prefixWord, tailWord_7446452, baseEnd_7446452] using wordTrace_append hprefix tailTrace_7446452
  have hstable : (prefixWord ++ tailWord_7446452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446452).length < 2 ^ (prefixWord ++ tailWord_7446452).sum := by decide
  have hdescent : baseEnd_7446452 < baseStart_7446452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446462 : List Nat := [4, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3]
def baseStart_7446462 : Nat := 118140960795 + 7446462 * 2 ^ 59
def prefixEnd_7446462 : Nat := 4983230072969 + 3 ^ 40 * 7446462 * 2
def baseEnd_7446462 : Nat := 3823614181440349916879351

theorem tailTrace_7446462 : CollatzResearch.WordTrace tailWord_7446462 prefixEnd_7446462 3823614181440349916879351 := by
  unfold tailWord_7446462
  simp only [CollatzResearch.WordTrace]
  refine ⟨33949347693593425413145705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181063187699164935536777093 33949347693593425413145705)
  ·
    refine ⟨25462010770195069059859279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33949347693593425413145705 25462010770195069059859279)
    ·
      refine ⟨38193016155292603589788919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25462010770195069059859279 38193016155292603589788919)
      ·
        refine ⟨57289524232938905384683379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38193016155292603589788919 57289524232938905384683379)
        ·
          refine ⟨85934286349408358077025069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57289524232938905384683379 85934286349408358077025069)
          ·
            refine ⟨32225357381028134278884401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85934286349408358077025069 32225357381028134278884401)
            ·
              refine ⟨24169018035771100709163301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32225357381028134278884401 24169018035771100709163301)
              ·
                refine ⟨4531690881707081382968119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24169018035771100709163301 4531690881707081382968119)
                ·
                  refine ⟨6797536322560622074452179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4531690881707081382968119 6797536322560622074452179)
                  ·
                    refine ⟨10196304483840933111678269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6797536322560622074452179 10196304483840933111678269)
                    ·
                      refine ⟨3823614181440349916879351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10196304483840933111678269 3823614181440349916879351)
                      ·
                        rfl

theorem cell23_7446462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_7446462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446462 prefixEnd_7446462 := by exact prefixLift 7446462
  have htrace : WordTrace (prefixWord ++ tailWord_7446462) baseStart_7446462 baseEnd_7446462 := by
    simpa [prefixWord, tailWord_7446462, baseEnd_7446462] using wordTrace_append hprefix tailTrace_7446462
  have hstable : (prefixWord ++ tailWord_7446462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446462).length < 2 ^ (prefixWord ++ tailWord_7446462).sum := by decide
  have hdescent : baseEnd_7446462 < baseStart_7446462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446481 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 1, 2, 4]
def baseStart_7446481 : Nat := 118140960795 + 7446481 * 2 ^ 59
def prefixEnd_7446481 : Nat := 4983230072969 + 3 ^ 40 * 7446481 * 2
def baseEnd_7446481 : Nat := 3823623937572785342541763

theorem tailTrace_7446481 : CollatzResearch.WordTrace tailWord_7446481 prefixEnd_7446481 3823623937572785342541763 := by
  unfold tailWord_7446481
  simp only [CollatzResearch.WordTrace]
  refine ⟨271595474535678569550107297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181063649690452379700071531 271595474535678569550107297)
  ·
    refine ⟨203696605901758927162580473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271595474535678569550107297 203696605901758927162580473)
    ·
      refine ⟨152772454426319195371935355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203696605901758927162580473 152772454426319195371935355)
      ·
        refine ⟨229158681639478793057903033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152772454426319195371935355 229158681639478793057903033)
        ·
          refine ⟨171869011229609094793427275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229158681639478793057903033 171869011229609094793427275)
          ·
            refine ⟨257803516844413642190140913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171869011229609094793427275 257803516844413642190140913)
            ·
              refine ⟨193352637633310231642605685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257803516844413642190140913 193352637633310231642605685)
              ·
                refine ⟨18126809778122834216494283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193352637633310231642605685 18126809778122834216494283)
                ·
                  refine ⟨27190214667184251324741425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18126809778122834216494283 27190214667184251324741425)
                  ·
                    refine ⟨20392661000388188493556069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27190214667184251324741425 20392661000388188493556069)
                    ·
                      refine ⟨3823623937572785342541763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20392661000388188493556069 3823623937572785342541763)
                      ·
                        rfl

theorem cell23_7446481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_7446481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446481 prefixEnd_7446481 := by exact prefixLift 7446481
  have htrace : WordTrace (prefixWord ++ tailWord_7446481) baseStart_7446481 baseEnd_7446481 := by
    simpa [prefixWord, tailWord_7446481, baseEnd_7446481] using wordTrace_append hprefix tailTrace_7446481
  have hstable : (prefixWord ++ tailWord_7446481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446481).length < 2 ^ (prefixWord ++ tailWord_7446481).sum := by decide
  have hdescent : baseEnd_7446481 < baseStart_7446481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446485 : List Nat := [1, 3, 2, 3, 2, 2, 2, 2, 1, 1, 4]
def baseStart_7446485 : Nat := 118140960795 + 7446485 * 2 ^ 59
def prefixEnd_7446485 : Nat := 4983230072969 + 3 ^ 40 * 7446485 * 2
def baseEnd_7446485 : Nat := 3823625991495403326891745

theorem tailTrace_7446485 : CollatzResearch.WordTrace tailWord_7446485 prefixEnd_7446485 3823625991495403326891745 := by
  unfold tailWord_7446485
  simp only [CollatzResearch.WordTrace]
  refine ⟨271595620427664078233252909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181063746951776052155501939 271595620427664078233252909)
  ·
    refine ⟨101848357660374029337469841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271595620427664078233252909 101848357660374029337469841)
    ·
      refine ⟨76386268245280522003102381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101848357660374029337469841 76386268245280522003102381)
      ·
        refine ⟨28644850591980195751163393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76386268245280522003102381 28644850591980195751163393)
        ·
          refine ⟨21483637943985146813372545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28644850591980195751163393 21483637943985146813372545)
          ·
            refine ⟨16112728457988860110029409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21483637943985146813372545 16112728457988860110029409)
            ·
              refine ⟨12084546343491645082522057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16112728457988860110029409 12084546343491645082522057)
              ·
                refine ⟨9063409757618733811891543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12084546343491645082522057 9063409757618733811891543)
                ·
                  refine ⟨13595114636428100717837315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9063409757618733811891543 13595114636428100717837315)
                  ·
                    refine ⟨20392671954642151076755973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13595114636428100717837315 20392671954642151076755973)
                    ·
                      refine ⟨3823625991495403326891745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20392671954642151076755973 3823625991495403326891745)
                      ·
                        rfl

theorem cell23_7446485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_7446485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446485 prefixEnd_7446485 := by exact prefixLift 7446485
  have htrace : WordTrace (prefixWord ++ tailWord_7446485) baseStart_7446485 baseEnd_7446485 := by
    simpa [prefixWord, tailWord_7446485, baseEnd_7446485] using wordTrace_append hprefix tailTrace_7446485
  have hstable : (prefixWord ++ tailWord_7446485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446485).length < 2 ^ (prefixWord ++ tailWord_7446485).sum := by decide
  have hdescent : baseEnd_7446485 < baseStart_7446485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446578 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3]
def baseStart_7446578 : Nat := 118140960795 + 7446578 * 2 ^ 59
def prefixEnd_7446578 : Nat := 4983230072969 + 3 ^ 40 * 7446578 * 2
def baseEnd_7446578 : Nat := 3823673745196271463028817

theorem tailTrace_7446578 : CollatzResearch.WordTrace tailWord_7446578 prefixEnd_7446578 3823673745196271463028817 := by
  unfold tailWord_7446578
  simp only [CollatzResearch.WordTrace]
  refine ⟨67899753104081788779097097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181066008277551436744258925 67899753104081788779097097)
  ·
    refine ⟨50924814828061341584322823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67899753104081788779097097 50924814828061341584322823)
    ·
      refine ⟨76387222242092012376484235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50924814828061341584322823 76387222242092012376484235)
      ·
        refine ⟨114580833363138018564726353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76387222242092012376484235 114580833363138018564726353)
        ·
          refine ⟨85935625022353513923544765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114580833363138018564726353 85935625022353513923544765)
          ·
            refine ⟨32225859383382567721329287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85935625022353513923544765 32225859383382567721329287)
            ·
              refine ⟨48338789075073851581993931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32225859383382567721329287 48338789075073851581993931)
              ·
                refine ⟨72508183612610777372990897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48338789075073851581993931 72508183612610777372990897)
                ·
                  refine ⟨54381137709458083029743173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72508183612610777372990897 54381137709458083029743173)
                  ·
                    refine ⟨10196463320523390568076845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54381137709458083029743173 10196463320523390568076845)
                    ·
                      refine ⟨3823673745196271463028817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10196463320523390568076845 3823673745196271463028817)
                      ·
                        rfl

theorem cell23_7446578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_7446578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446578 prefixEnd_7446578 := by exact prefixLift 7446578
  have htrace : WordTrace (prefixWord ++ tailWord_7446578) baseStart_7446578 baseEnd_7446578 := by
    simpa [prefixWord, tailWord_7446578, baseEnd_7446578] using wordTrace_append hprefix tailTrace_7446578
  have hstable : (prefixWord ++ tailWord_7446578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446578).length < 2 ^ (prefixWord ++ tailWord_7446578).sum := by decide
  have hdescent : baseEnd_7446578 < baseStart_7446578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446588 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_7446588 : Nat := 118140960795 + 7446588 * 2 ^ 59
def prefixEnd_7446588 : Nat := 4983230072969 + 3 ^ 40 * 7446588 * 2
def baseEnd_7446588 : Nat := 3823678880002816423903771

theorem tailTrace_7446588 : CollatzResearch.WordTrace tailWord_7446588 prefixEnd_7446588 3823678880002816423903771 := by
  unfold tailWord_7446588
  simp only [CollatzResearch.WordTrace]
  refine ⟨135799688573145463412126209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181066251430860617882834945 135799688573145463412126209)
  ·
    refine ⟨101849766429859097559094657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135799688573145463412126209 101849766429859097559094657)
    ·
      refine ⟨76387324822394323169320993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101849766429859097559094657 76387324822394323169320993)
      ·
        refine ⟨57290493616795742376990745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76387324822394323169320993 57290493616795742376990745)
        ·
          refine ⟨42967870212596806782743059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57290493616795742376990745 42967870212596806782743059)
          ·
            refine ⟨64451805318895210174114589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42967870212596806782743059 64451805318895210174114589)
            ·
              refine ⟨24169426994585703815292971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64451805318895210174114589 24169426994585703815292971)
              ·
                refine ⟨36254140491878555722939457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24169426994585703815292971 36254140491878555722939457)
                ·
                  refine ⟨27190605368908916792204593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36254140491878555722939457 27190605368908916792204593)
                  ·
                    refine ⟨20392954026681687594153445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27190605368908916792204593 20392954026681687594153445)
                    ·
                      refine ⟨3823678880002816423903771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20392954026681687594153445 3823678880002816423903771)
                      ·
                        rfl

theorem cell23_7446588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_7446588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446588 prefixEnd_7446588 := by exact prefixLift 7446588
  have htrace : WordTrace (prefixWord ++ tailWord_7446588) baseStart_7446588 baseEnd_7446588 := by
    simpa [prefixWord, tailWord_7446588, baseEnd_7446588] using wordTrace_append hprefix tailTrace_7446588
  have hstable : (prefixWord ++ tailWord_7446588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446588).length < 2 ^ (prefixWord ++ tailWord_7446588).sum := by decide
  have hdescent : baseEnd_7446588 < baseStart_7446588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446592 : List Nat := [2, 1, 1, 2, 2, 4, 2, 3, 2, 2, 2]
def baseStart_7446592 : Nat := 118140960795 + 7446592 * 2 ^ 59
def prefixEnd_7446592 : Nat := 4983230072969 + 3 ^ 40 * 7446592 * 2
def baseEnd_7446592 : Nat := 3823680933925434408253753

theorem tailTrace_7446592 : CollatzResearch.WordTrace tailWord_7446592 prefixEnd_7446592 3823680933925434408253753 := by
  unfold tailWord_7446592
  simp only [CollatzResearch.WordTrace]
  refine ⟨135799761519138217753699015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181066348692184290338265353 135799761519138217753699015)
  ·
    refine ⟨203699642278707326630548523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135799761519138217753699015 203699642278707326630548523)
    ·
      refine ⟨305549463418060989945822785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203699642278707326630548523 305549463418060989945822785)
      ·
        refine ⟨229162097563545742459367089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305549463418060989945822785 229162097563545742459367089)
        ·
          refine ⟨171871573172659306844525317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229162097563545742459367089 171871573172659306844525317)
          ·
            refine ⟨32225919969873620033348497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171871573172659306844525317 32225919969873620033348497)
            ·
              refine ⟨24169439977405215025011373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32225919969873620033348497 24169439977405215025011373)
              ·
                refine ⟨9063539991526955634379265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24169439977405215025011373 9063539991526955634379265)
                ·
                  refine ⟨6797654993645216725784449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9063539991526955634379265 6797654993645216725784449)
                  ·
                    refine ⟨5098241245233912544338337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6797654993645216725784449 5098241245233912544338337)
                    ·
                      refine ⟨3823680933925434408253753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5098241245233912544338337 3823680933925434408253753)
                      ·
                        rfl

theorem cell23_7446592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 2, 2, 2].length) (baseStart_7446592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446592 prefixEnd_7446592 := by exact prefixLift 7446592
  have htrace : WordTrace (prefixWord ++ tailWord_7446592) baseStart_7446592 baseEnd_7446592 := by
    simpa [prefixWord, tailWord_7446592, baseEnd_7446592] using wordTrace_append hprefix tailTrace_7446592
  have hstable : (prefixWord ++ tailWord_7446592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446592).length < 2 ^ (prefixWord ++ tailWord_7446592).sum := by decide
  have hdescent : baseEnd_7446592 < baseStart_7446592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446628 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 2, 5]
def baseStart_7446628 : Nat := 118140960795 + 7446628 * 2 ^ 59
def prefixEnd_7446628 : Nat := 4983230072969 + 3 ^ 40 * 7446628 * 2
def baseEnd_7446628 : Nat := 1274566473076332089134529

theorem tailTrace_7446628 : CollatzResearch.WordTrace tailWord_7446628 prefixEnd_7446628 1274566473076332089134529 := by
  unfold tailWord_7446628
  simp only [CollatzResearch.WordTrace]
  refine ⟨135800418033073006827854269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181067224044097342437139025 135800418033073006827854269)
  ·
    refine ⟨50925156762402377560445351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135800418033073006827854269 50925156762402377560445351)
    ·
      refine ⟨76387735143603566340668027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50925156762402377560445351 76387735143603566340668027)
      ·
        refine ⟨114581602715405349511002041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76387735143603566340668027 114581602715405349511002041)
        ·
          refine ⟨85936202036554012133251531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114581602715405349511002041 85936202036554012133251531)
          ·
            refine ⟨128904303054831018199877297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85936202036554012133251531 128904303054831018199877297)
            ·
              refine ⟨96678227291123263649907973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128904303054831018199877297 96678227291123263649907973)
              ·
                refine ⟨18127167617085611934357745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96678227291123263649907973 18127167617085611934357745)
                ·
                  refine ⟨13595375712814208950768309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18127167617085611934357745 13595375712814208950768309)
                  ·
                    refine ⟨1274566473076332089134529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13595375712814208950768309 1274566473076332089134529)
                    ·
                      rfl

theorem cell23_7446628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_7446628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446628 prefixEnd_7446628 := by exact prefixLift 7446628
  have htrace : WordTrace (prefixWord ++ tailWord_7446628) baseStart_7446628 baseEnd_7446628 := by
    simpa [prefixWord, tailWord_7446628, baseEnd_7446628] using wordTrace_append hprefix tailTrace_7446628
  have hstable : (prefixWord ++ tailWord_7446628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446628).length < 2 ^ (prefixWord ++ tailWord_7446628).sum := by decide
  have hdescent : baseEnd_7446628 < baseStart_7446628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446638 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_7446638 : Nat := 118140960795 + 7446638 * 2 ^ 59
def prefixEnd_7446638 : Nat := 4983230072969 + 3 ^ 40 * 7446638 * 2
def baseEnd_7446638 : Nat := 3823704554035541228278541

theorem tailTrace_7446638 : CollatzResearch.WordTrace tailWord_7446638 prefixEnd_7446638 3823704554035541228278541 := by
  unfold tailWord_7446638
  simp only [CollatzResearch.WordTrace]
  refine ⟨33950150099513723170446571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181067467197406523575715045 33950150099513723170446571)
  ·
    refine ⟨50925225149270584755669857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33950150099513723170446571 50925225149270584755669857)
    ·
      refine ⟨38193918861952938566752393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50925225149270584755669857 38193918861952938566752393)
      ·
        refine ⟨28645439146464703925064295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38193918861952938566752393 28645439146464703925064295)
        ·
          refine ⟨42968158719697055887596443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28645439146464703925064295 42968158719697055887596443)
          ·
            refine ⟨64452238079545583831394665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42968158719697055887596443 64452238079545583831394665)
            ·
              refine ⟨48339178559659187873545999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64452238079545583831394665 48339178559659187873545999)
              ·
                refine ⟨72508767839488781810318999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48339178559659187873545999 72508767839488781810318999)
                ·
                  refine ⟨108763151759233172715478499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72508767839488781810318999 108763151759233172715478499)
                  ·
                    refine ⟨163144727638849759073217749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108763151759233172715478499 163144727638849759073217749)
                    ·
                      refine ⟨3823704554035541228278541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163144727638849759073217749 3823704554035541228278541)
                      ·
                        rfl

theorem cell23_7446638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_7446638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446638 prefixEnd_7446638 := by exact prefixLift 7446638
  have htrace : WordTrace (prefixWord ++ tailWord_7446638) baseStart_7446638 baseEnd_7446638 := by
    simpa [prefixWord, tailWord_7446638, baseEnd_7446638] using wordTrace_append hprefix tailTrace_7446638
  have hstable : (prefixWord ++ tailWord_7446638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446638).length < 2 ^ (prefixWord ++ tailWord_7446638).sum := by decide
  have hdescent : baseEnd_7446638 < baseStart_7446638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446682 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4]
def baseStart_7446682 : Nat := 118140960795 + 7446682 * 2 ^ 59
def prefixEnd_7446682 : Nat := 4983230072969 + 3 ^ 40 * 7446682 * 2
def baseEnd_7446682 : Nat := 3823727147184339056128339

theorem tailTrace_7446682 : CollatzResearch.WordTrace tailWord_7446682 prefixEnd_7446682 3823727147184339056128339 := by
  unfold tailWord_7446682
  simp only [CollatzResearch.WordTrace]
  refine ⟨67900701401987595219543575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181068537071966920585449533 67900701401987595219543575)
  ·
    refine ⟨101851052102981392829315363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67900701401987595219543575 101851052102981392829315363)
    ·
      refine ⟨152776578154472089243973045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101851052102981392829315363 152776578154472089243973045)
      ·
        refine ⟨14322804201981758366622473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152776578154472089243973045 14322804201981758366622473)
        ·
          refine ⟨10742103151486318774966855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14322804201981758366622473 10742103151486318774966855)
          ·
            refine ⟨16113154727229478162450283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10742103151486318774966855 16113154727229478162450283)
            ·
              refine ⟨24169732090844217243675425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16113154727229478162450283 24169732090844217243675425)
              ·
                refine ⟨18127299068133162932756569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24169732090844217243675425 18127299068133162932756569)
                ·
                  refine ⟨13595474301099872199567427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18127299068133162932756569 13595474301099872199567427)
                  ·
                    refine ⟨20393211451649808299351141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13595474301099872199567427 20393211451649808299351141)
                    ·
                      refine ⟨3823727147184339056128339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20393211451649808299351141 3823727147184339056128339)
                      ·
                        rfl

theorem cell23_7446682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_7446682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446682 prefixEnd_7446682 := by exact prefixLift 7446682
  have htrace : WordTrace (prefixWord ++ tailWord_7446682) baseStart_7446682 baseEnd_7446682 := by
    simpa [prefixWord, tailWord_7446682, baseEnd_7446682] using wordTrace_append hprefix tailTrace_7446682
  have hstable : (prefixWord ++ tailWord_7446682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446682).length < 2 ^ (prefixWord ++ tailWord_7446682).sum := by decide
  have hdescent : baseEnd_7446682 < baseStart_7446682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446685 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_7446685 : Nat := 118140960795 + 7446685 * 2 ^ 59
def prefixEnd_7446685 : Nat := 4983230072969 + 3 ^ 40 * 7446685 * 2
def baseEnd_7446685 : Nat := 3823728687626302544390825

theorem tailTrace_7446685 : CollatzResearch.WordTrace tailWord_7446685 prefixEnd_7446685 3823728687626302544390825 := by
  unfold tailWord_7446685
  simp only [CollatzResearch.WordTrace]
  refine ⟨271602915026939512390533509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181068610017959674927022339 271602915026939512390533509)
  ·
    refine ⟨50925546567551158573225033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271602915026939512390533509 50925546567551158573225033)
    ·
      refine ⟨38194159925663368929918775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50925546567551158573225033 38194159925663368929918775)
      ·
        refine ⟨57291239888495053394878163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38194159925663368929918775 57291239888495053394878163)
        ·
          refine ⟨85936859832742580092317245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57291239888495053394878163 85936859832742580092317245)
          ·
            refine ⟨32226322437278467534618967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85936859832742580092317245 32226322437278467534618967)
            ·
              refine ⟨48339483655917701301928451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32226322437278467534618967 48339483655917701301928451)
              ·
                refine ⟨72509225483876551952892677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48339483655917701301928451 72509225483876551952892677)
                ·
                  refine ⟨13595479778226853491167377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72509225483876551952892677 13595479778226853491167377)
                  ·
                    refine ⟨10196609833670140118375533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13595479778226853491167377 10196609833670140118375533)
                    ·
                      refine ⟨3823728687626302544390825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10196609833670140118375533 3823728687626302544390825)
                      ·
                        rfl

theorem cell23_7446685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_7446685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446685 prefixEnd_7446685 := by exact prefixLift 7446685
  have htrace : WordTrace (prefixWord ++ tailWord_7446685) baseStart_7446685 baseEnd_7446685 := by
    simpa [prefixWord, tailWord_7446685, baseEnd_7446685] using wordTrace_append hprefix tailTrace_7446685
  have hstable : (prefixWord ++ tailWord_7446685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446685).length < 2 ^ (prefixWord ++ tailWord_7446685).sum := by decide
  have hdescent : baseEnd_7446685 < baseStart_7446685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446688 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 8]
def baseStart_7446688 : Nat := 118140960795 + 7446688 * 2 ^ 59
def prefixEnd_7446688 : Nat := 4983230072969 + 3 ^ 40 * 7446688 * 2
def baseEnd_7446688 : Nat := 424858914229807336961479

theorem tailTrace_7446688 : CollatzResearch.WordTrace tailWord_7446688 prefixEnd_7446688 424858914229807336961479 := by
  unfold tailWord_7446688
  simp only [CollatzResearch.WordTrace]
  refine ⟨135801512222964321951446359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181068682963952429268595145 135801512222964321951446359)
  ·
    refine ⟨203702268334446482927169539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135801512222964321951446359 203702268334446482927169539)
    ·
      refine ⟨305553402501669724390754309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203702268334446482927169539 305553402501669724390754309)
      ·
        refine ⟨57291262969063073323266433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305553402501669724390754309 57291262969063073323266433)
        ·
          refine ⟨42968447226797304992449825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57291262969063073323266433 42968447226797304992449825)
          ·
            refine ⟨32226335420097978744337369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42968447226797304992449825 32226335420097978744337369)
            ·
              refine ⟨24169751565073484058253027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32226335420097978744337369 24169751565073484058253027)
              ·
                refine ⟨36254627347610226087379541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24169751565073484058253027 36254627347610226087379541)
                ·
                  refine ⟨424858914229807336961479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36254627347610226087379541 424858914229807336961479)
                  ·
                    rfl

theorem cell23_7446688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 8].length) (baseStart_7446688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446688 prefixEnd_7446688 := by exact prefixLift 7446688
  have htrace : WordTrace (prefixWord ++ tailWord_7446688) baseStart_7446688 baseEnd_7446688 := by
    simpa [prefixWord, tailWord_7446688, baseEnd_7446688] using wordTrace_append hprefix tailTrace_7446688
  have hstable : (prefixWord ++ tailWord_7446688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446688).length < 2 ^ (prefixWord ++ tailWord_7446688).sum := by decide
  have hdescent : baseEnd_7446688 < baseStart_7446688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446715 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 5, 1, 3]
def baseStart_7446715 : Nat := 118140960795 + 7446715 * 2 ^ 59
def prefixEnd_7446715 : Nat := 4983230072969 + 3 ^ 40 * 7446715 * 2
def baseEnd_7446715 : Nat := 3823744092045937427015687

theorem tailTrace_7446715 : CollatzResearch.WordTrace tailWord_7446715 prefixEnd_7446715 3823744092045937427015687 := by
  unfold tailWord_7446715
  simp only [CollatzResearch.WordTrace]
  refine ⟨271604009216830827514125599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181069339477887218342750399 271604009216830827514125599)
  ·
    refine ⟨407406013825246241271188399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271604009216830827514125599 407406013825246241271188399)
    ·
      refine ⟨611109020737869361906782599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407406013825246241271188399 611109020737869361906782599)
      ·
        refine ⟨916663531106804042860173899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611109020737869361906782599 916663531106804042860173899)
        ·
          refine ⟨1374995296660206064290260849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916663531106804042860173899 1374995296660206064290260849)
          ·
            refine ⟨1031246472495154548217695637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1374995296660206064290260849 1031246472495154548217695637)
            ·
              refine ⟨48339678398210369447704483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1031246472495154548217695637 48339678398210369447704483)
              ·
                refine ⟨72509517597315554171556725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48339678398210369447704483 72509517597315554171556725)
                ·
                  refine ⟨6797767274748333203583443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72509517597315554171556725 6797767274748333203583443)
                  ·
                    refine ⟨10196650912122499805375165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6797767274748333203583443 10196650912122499805375165)
                    ·
                      refine ⟨3823744092045937427015687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10196650912122499805375165 3823744092045937427015687)
                      ·
                        rfl

theorem cell23_7446715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 1, 3].length) (baseStart_7446715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446715 prefixEnd_7446715 := by exact prefixLift 7446715
  have htrace : WordTrace (prefixWord ++ tailWord_7446715) baseStart_7446715 baseEnd_7446715 := by
    simpa [prefixWord, tailWord_7446715, baseEnd_7446715] using wordTrace_append hprefix tailTrace_7446715
  have hstable : (prefixWord ++ tailWord_7446715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446715).length < 2 ^ (prefixWord ++ tailWord_7446715).sum := by decide
  have hdescent : baseEnd_7446715 < baseStart_7446715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446725 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 1, 5, 2]
def baseStart_7446725 : Nat := 118140960795 + 7446725 * 2 ^ 59
def prefixEnd_7446725 : Nat := 4983230072969 + 3 ^ 40 * 7446725 * 2
def baseEnd_7446725 : Nat := 3823749226852482387890641

theorem tailTrace_7446725 : CollatzResearch.WordTrace tailWord_7446725 prefixEnd_7446725 3823749226852482387890641 := by
  unfold tailWord_7446725
  simp only [CollatzResearch.WordTrace]
  refine ⟨271604373946794599221989629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181069582631196399481326419 271604373946794599221989629)
  ·
    refine ⟨101851640230047974708246111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271604373946794599221989629 101851640230047974708246111)
    ·
      refine ⟨152777460345071962062369167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101851640230047974708246111 152777460345071962062369167)
      ·
        refine ⟨229166190517607943093553751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152777460345071962062369167 229166190517607943093553751)
        ·
          refine ⟨343749285776411914640330627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229166190517607943093553751 343749285776411914640330627)
          ·
            refine ⟨515623928664617871960495941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343749285776411914640330627 515623928664617871960495941)
            ·
              refine ⟨96679486624615850992592989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 515623928664617871960495941 96679486624615850992592989)
              ·
                refine ⟨36254807484230944122222371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96679486624615850992592989 36254807484230944122222371)
                ·
                  refine ⟨54382211226346416183333557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36254807484230944122222371 54382211226346416183333557)
                  ·
                    refine ⟨5098332302469976517187521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54382211226346416183333557 5098332302469976517187521)
                    ·
                      refine ⟨3823749226852482387890641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5098332302469976517187521 3823749226852482387890641)
                      ·
                        rfl

theorem cell23_7446725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 5, 2].length) (baseStart_7446725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446725 prefixEnd_7446725 := by exact prefixLift 7446725
  have htrace : WordTrace (prefixWord ++ tailWord_7446725) baseStart_7446725 baseEnd_7446725 := by
    simpa [prefixWord, tailWord_7446725, baseEnd_7446725] using wordTrace_append hprefix tailTrace_7446725
  have hstable : (prefixWord ++ tailWord_7446725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446725).length < 2 ^ (prefixWord ++ tailWord_7446725).sum := by decide
  have hdescent : baseEnd_7446725 < baseStart_7446725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446768 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 6]
def baseStart_7446768 : Nat := 118140960795 + 7446768 * 2 ^ 59
def prefixEnd_7446768 : Nat := 4983230072969 + 3 ^ 40 * 7446768 * 2
def baseEnd_7446768 : Nat := 3823771306520625719652943

theorem tailTrace_7446768 : CollatzResearch.WordTrace tailWord_7446768 prefixEnd_7446768 3823771306520625719652943 := by
  unfold tailWord_7446768
  simp only [CollatzResearch.WordTrace]
  refine ⟨135802971142819408782902479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181070628190425878377203305 135802971142819408782902479)
  ·
    refine ⟨203704456714229113174353719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135802971142819408782902479 203704456714229113174353719)
    ·
      refine ⟨305556685071343669761530579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203704456714229113174353719 305556685071343669761530579)
      ·
        refine ⟨458335027607015504642295869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305556685071343669761530579 458335027607015504642295869)
        ·
          refine ⟨171875635352630814240860951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 458335027607015504642295869 171875635352630814240860951)
          ·
            refine ⟨257813453028946221361291427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171875635352630814240860951 257813453028946221361291427)
            ·
              refine ⟨386720179543419332041937141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257813453028946221361291427 386720179543419332041937141)
              ·
                refine ⟨36255016832195562378931607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 386720179543419332041937141 36255016832195562378931607)
                ·
                  refine ⟨54382525248293343568397411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36255016832195562378931607 54382525248293343568397411)
                  ·
                    refine ⟨81573787872440015352596117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54382525248293343568397411 81573787872440015352596117)
                    ·
                      refine ⟨3823771306520625719652943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81573787872440015352596117 3823771306520625719652943)
                      ·
                        rfl

theorem cell23_7446768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_7446768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446768 prefixEnd_7446768 := by exact prefixLift 7446768
  have htrace : WordTrace (prefixWord ++ tailWord_7446768) baseStart_7446768 baseEnd_7446768 := by
    simpa [prefixWord, tailWord_7446768, baseEnd_7446768] using wordTrace_append hprefix tailTrace_7446768
  have hstable : (prefixWord ++ tailWord_7446768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446768).length < 2 ^ (prefixWord ++ tailWord_7446768).sum := by decide
  have hdescent : baseEnd_7446768 < baseStart_7446768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446782 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_7446782 : Nat := 118140960795 + 7446782 * 2 ^ 59
def prefixEnd_7446782 : Nat := 4983230072969 + 3 ^ 40 * 7446782 * 2
def baseEnd_7446782 : Nat := 1274592831749929554959293

theorem tailTrace_7446782 : CollatzResearch.WordTrace tailWord_7446782 prefixEnd_7446782 1274592831749929554959293 := by
  unfold tailWord_7446782
  simp only [CollatzResearch.WordTrace]
  refine ⟨33950806613448512244601825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181070968605058731971209733 33950806613448512244601825)
  ·
    refine ⟨25463104960086384183451369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33950806613448512244601825 25463104960086384183451369)
    ·
      refine ⟨19097328720064788137588527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25463104960086384183451369 19097328720064788137588527)
      ·
        refine ⟨28645993080097182206382791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19097328720064788137588527 28645993080097182206382791)
        ·
          refine ⟨42968989620145773309574187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28645993080097182206382791 42968989620145773309574187)
          ·
            refine ⟨64453484430218659964361281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42968989620145773309574187 64453484430218659964361281)
            ·
              refine ⟨48340113322663994973270961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64453484430218659964361281 48340113322663994973270961)
              ·
                refine ⟨36255084991997996229953221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48340113322663994973270961 36255084991997996229953221)
                ·
                  refine ⟨6797828435999624293116229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36255084991997996229953221 6797828435999624293116229)
                  ·
                    refine ⟨1274592831749929554959293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6797828435999624293116229 1274592831749929554959293)
                    ·
                      rfl

theorem cell23_7446782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_7446782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446782 prefixEnd_7446782 := by exact prefixLift 7446782
  have htrace : WordTrace (prefixWord ++ tailWord_7446782) baseStart_7446782 baseEnd_7446782 := by
    simpa [prefixWord, tailWord_7446782, baseEnd_7446782] using wordTrace_append hprefix tailTrace_7446782
  have hstable : (prefixWord ++ tailWord_7446782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446782).length < 2 ^ (prefixWord ++ tailWord_7446782).sum := by decide
  have hdescent : baseEnd_7446782 < baseStart_7446782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446785 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_7446785 : Nat := 118140960795 + 7446785 * 2 ^ 59
def prefixEnd_7446785 : Nat := 4983230072969 + 3 ^ 40 * 7446785 * 2
def baseEnd_7446785 : Nat := 3823780035691752153140365

theorem tailTrace_7446785 : CollatzResearch.WordTrace tailWord_7446785 prefixEnd_7446785 3823780035691752153140365 := by
  unfold tailWord_7446785
  simp only [CollatzResearch.WordTrace]
  refine ⟨271606562326577229469173809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181071041551051486312782539 271606562326577229469173809)
  ·
    refine ⟨203704921744932922101880357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271606562326577229469173809 203704921744932922101880357)
    ·
      refine ⟨38194672827174922894102567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203704921744932922101880357 38194672827174922894102567)
      ·
        refine ⟨57292009240762384341153851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38194672827174922894102567 57292009240762384341153851)
        ·
          refine ⟨85938013861143576511730777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57292009240762384341153851 85938013861143576511730777)
          ·
            refine ⟨64453510395857682383798083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85938013861143576511730777 64453510395857682383798083)
            ·
              refine ⟨96680265593786523575697125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64453510395857682383798083 96680265593786523575697125)
              ·
                refine ⟨18127549798834973170443211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96680265593786523575697125 18127549798834973170443211)
                ·
                  refine ⟨27191324698252459755664817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18127549798834973170443211 27191324698252459755664817)
                  ·
                    refine ⟨20393493523689344816748613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27191324698252459755664817 20393493523689344816748613)
                    ·
                      refine ⟨3823780035691752153140365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20393493523689344816748613 3823780035691752153140365)
                      ·
                        rfl

theorem cell23_7446785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_7446785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446785 prefixEnd_7446785 := by exact prefixLift 7446785
  have htrace : WordTrace (prefixWord ++ tailWord_7446785) baseStart_7446785 baseEnd_7446785 := by
    simpa [prefixWord, tailWord_7446785, baseEnd_7446785] using wordTrace_append hprefix tailTrace_7446785
  have hstable : (prefixWord ++ tailWord_7446785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446785).length < 2 ^ (prefixWord ++ tailWord_7446785).sum := by decide
  have hdescent : baseEnd_7446785 < baseStart_7446785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446786 : List Nat := [3, 4, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_7446786 : Nat := 118140960795 + 7446786 * 2 ^ 59
def prefixEnd_7446786 : Nat := 4983230072969 + 3 ^ 40 * 7446786 * 2
def baseEnd_7446786 : Nat := 1274593516390802216409287

theorem tailTrace_7446786 : CollatzResearch.WordTrace tailWord_7446786 prefixEnd_7446786 1274593516390802216409287 := by
  unfold tailWord_7446786
  simp only [CollatzResearch.WordTrace]
  refine ⟨67901649699893401659990053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181071065866382404426640141 67901649699893401659990053)
  ·
    refine ⟨12731559318730012811248135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67901649699893401659990053 12731559318730012811248135)
    ·
      refine ⟨19097338978095019216872203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12731559318730012811248135 19097338978095019216872203)
      ·
        refine ⟨28646008467142528825308305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19097338978095019216872203 28646008467142528825308305)
        ·
          refine ⟨21484506350356896618981229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28646008467142528825308305 21484506350356896618981229)
          ·
            refine ⟨8056689881383836232117961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21484506350356896618981229 8056689881383836232117961)
            ·
              refine ⟨6042517411037877174088471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8056689881383836232117961 6042517411037877174088471)
              ·
                refine ⟨9063776116556815761132707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6042517411037877174088471 9063776116556815761132707)
                ·
                  refine ⟨13595664174835223641699061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9063776116556815761132707 13595664174835223641699061)
                  ·
                    refine ⟨1274593516390802216409287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13595664174835223641699061 1274593516390802216409287)
                    ·
                      rfl

theorem cell23_7446786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_7446786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446786 prefixEnd_7446786 := by exact prefixLift 7446786
  have htrace : WordTrace (prefixWord ++ tailWord_7446786) baseStart_7446786 baseEnd_7446786 := by
    simpa [prefixWord, tailWord_7446786, baseEnd_7446786] using wordTrace_append hprefix tailTrace_7446786
  have hstable : (prefixWord ++ tailWord_7446786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446786).length < 2 ^ (prefixWord ++ tailWord_7446786).sum := by decide
  have hdescent : baseEnd_7446786 < baseStart_7446786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446805 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 3, 3, 3]
def baseStart_7446805 : Nat := 118140960795 + 7446805 * 2 ^ 59
def prefixEnd_7446805 : Nat := 4983230072969 + 3 ^ 40 * 7446805 * 2
def baseEnd_7446805 : Nat := 3823790305304842074890273

theorem tailTrace_7446805 : CollatzResearch.WordTrace tailWord_7446805 prefixEnd_7446805 3823790305304842074890273 := by
  unfold tailWord_7446805
  simp only [CollatzResearch.WordTrace]
  refine ⟨271607291786504772884901869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181071527857669848589934579 271607291786504772884901869)
  ·
    refine ⟨101852734419939289831838201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271607291786504772884901869 101852734419939289831838201)
    ·
      refine ⟨76389550814954467373878651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101852734419939289831838201 76389550814954467373878651)
      ·
        refine ⟨114584326222431701060817977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76389550814954467373878651 114584326222431701060817977)
        ·
          refine ⟨85938244666823775795613483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114584326222431701060817977 85938244666823775795613483)
          ·
            refine ⟨128907367000235663693420225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85938244666823775795613483 128907367000235663693420225)
            ·
              refine ⟨96680525250176747770065169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128907367000235663693420225 96680525250176747770065169)
              ·
                refine ⟨72510393937632560827548877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96680525250176747770065169 72510393937632560827548877)
                ·
                  refine ⟨27191397726612210310330829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72510393937632560827548877 27191397726612210310330829)
                  ·
                    refine ⟨10196774147479578866374061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27191397726612210310330829 10196774147479578866374061)
                    ·
                      refine ⟨3823790305304842074890273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10196774147479578866374061 3823790305304842074890273)
                      ·
                        rfl

theorem cell23_7446805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_7446805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446805 prefixEnd_7446805 := by exact prefixLift 7446805
  have htrace : WordTrace (prefixWord ++ tailWord_7446805) baseStart_7446805 baseEnd_7446805 := by
    simpa [prefixWord, tailWord_7446805, baseEnd_7446805] using wordTrace_append hprefix tailTrace_7446805
  have hstable : (prefixWord ++ tailWord_7446805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446805).length < 2 ^ (prefixWord ++ tailWord_7446805).sum := by decide
  have hdescent : baseEnd_7446805 < baseStart_7446805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446823 : List Nat := [1, 1, 8, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_7446823 : Nat := 118140960795 + 7446823 * 2 ^ 59
def prefixEnd_7446823 : Nat := 4983230072969 + 3 ^ 40 * 7446823 * 2
def baseEnd_7446823 : Nat := 3823799547956623004465191

theorem tailTrace_7446823 : CollatzResearch.WordTrace tailWord_7446823 prefixEnd_7446823 3823799547956623004465191 := by
  unfold tailWord_7446823
  simp only [CollatzResearch.WordTrace]
  refine ⟨271607948300439561959057123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181071965533626374639371415 271607948300439561959057123)
  ·
    refine ⟨407411922450659342938585685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271607948300439561959057123 407411922450659342938585685)
    ·
      refine ⟨4774358466218664175061551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 407411922450659342938585685 4774358466218664175061551)
      ·
        refine ⟨7161537699327996262592327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4774358466218664175061551 7161537699327996262592327)
        ·
          refine ⟨10742306548991994393888491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7161537699327996262592327 10742306548991994393888491)
          ·
            refine ⟨16113459823487991590832737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10742306548991994393888491 16113459823487991590832737)
            ·
              refine ⟨12085094867615993693124553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16113459823487991590832737 12085094867615993693124553)
              ·
                refine ⟨9063821150711995269843415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12085094867615993693124553 9063821150711995269843415)
                ·
                  refine ⟨13595731726067992904765123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9063821150711995269843415 13595731726067992904765123)
                  ·
                    refine ⟨20393597589101989357147685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13595731726067992904765123 20393597589101989357147685)
                    ·
                      refine ⟨3823799547956623004465191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20393597589101989357147685 3823799547956623004465191)
                      ·
                        rfl

theorem cell23_7446823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_7446823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446823 prefixEnd_7446823 := by exact prefixLift 7446823
  have htrace : WordTrace (prefixWord ++ tailWord_7446823) baseStart_7446823 baseEnd_7446823 := by
    simpa [prefixWord, tailWord_7446823, baseEnd_7446823] using wordTrace_append hprefix tailTrace_7446823
  have hstable : (prefixWord ++ tailWord_7446823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446823).length < 2 ^ (prefixWord ++ tailWord_7446823).sum := by decide
  have hdescent : baseEnd_7446823 < baseStart_7446823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446826 : List Nat := [3, 1, 4, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_7446826 : Nat := 118140960795 + 7446826 * 2 ^ 59
def prefixEnd_7446826 : Nat := 4983230072969 + 3 ^ 40 * 7446826 * 2
def baseEnd_7446826 : Nat := 3823801088398586492727677

theorem tailTrace_7446826 : CollatzResearch.WordTrace tailWord_7446826 prefixEnd_7446826 3823801088398586492727677 := by
  unfold tailWord_7446826
  simp only [CollatzResearch.WordTrace]
  refine ⟨67902014429857173367854083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181072038479619128980944221 67902014429857173367854083)
  ·
    refine ⟨101853021644785760051781125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67902014429857173367854083 101853021644785760051781125)
    ·
      refine ⟨19097441558397330009708961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101853021644785760051781125 19097441558397330009708961)
      ·
        refine ⟨14323081168797997507281721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19097441558397330009708961 14323081168797997507281721)
        ·
          refine ⟨10742310876598498130461291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14323081168797997507281721 10742310876598498130461291)
          ·
            refine ⟨16113466314897747195691937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10742310876598498130461291 16113466314897747195691937)
            ·
              refine ⟨12085099736173310396768953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16113466314897747195691937 12085099736173310396768953)
              ·
                refine ⟨9063824802129982797576715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12085099736173310396768953 9063824802129982797576715)
                ·
                  refine ⟨13595737203194974196365073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9063824802129982797576715 13595737203194974196365073)
                  ·
                    refine ⟨10196802902396230647273805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13595737203194974196365073 10196802902396230647273805)
                    ·
                      refine ⟨3823801088398586492727677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10196802902396230647273805 3823801088398586492727677)
                      ·
                        rfl

theorem cell23_7446826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_7446826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446826 prefixEnd_7446826 := by exact prefixLift 7446826
  have htrace : WordTrace (prefixWord ++ tailWord_7446826) baseStart_7446826 baseEnd_7446826 := by
    simpa [prefixWord, tailWord_7446826, baseEnd_7446826] using wordTrace_append hprefix tailTrace_7446826
  have hstable : (prefixWord ++ tailWord_7446826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446826).length < 2 ^ (prefixWord ++ tailWord_7446826).sum := by decide
  have hdescent : baseEnd_7446826 < baseStart_7446826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446862 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2]
def baseStart_7446862 : Nat := 118140960795 + 7446862 * 2 ^ 59
def prefixEnd_7446862 : Nat := 4983230072969 + 3 ^ 40 * 7446862 * 2
def baseEnd_7446862 : Nat := 3823819573702148351877511

theorem tailTrace_7446862 : CollatzResearch.WordTrace tailWord_7446862 prefixEnd_7446862 3823819573702148351877511 := by
  unfold tailWord_7446862
  simp only [CollatzResearch.WordTrace]
  refine ⟨33951171343412283952465855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181072913831532181079817893 33951171343412283952465855)
  ·
    refine ⟨50926757015118425928698783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33951171343412283952465855 50926757015118425928698783)
    ·
      refine ⟨76390135522677638893048175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50926757015118425928698783 76390135522677638893048175)
      ·
        refine ⟨114585203284016458339572263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76390135522677638893048175 114585203284016458339572263)
        ·
          refine ⟨171877804926024687509358395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114585203284016458339572263 171877804926024687509358395)
          ·
            refine ⟨257816707389037031264037593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171877804926024687509358395 257816707389037031264037593)
            ·
              refine ⟨193362530541777773448028195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257816707389037031264037593 193362530541777773448028195)
              ·
                refine ⟨290043795812666660172042293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193362530541777773448028195 290043795812666660172042293)
                ·
                  refine ⟨27191605857437499391128965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 290043795812666660172042293 27191605857437499391128965)
                  ·
                    refine ⟨5098426098269531135836681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27191605857437499391128965 5098426098269531135836681)
                    ·
                      refine ⟨3823819573702148351877511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5098426098269531135836681 3823819573702148351877511)
                      ·
                        rfl

theorem cell23_7446862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_7446862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446862 prefixEnd_7446862 := by exact prefixLift 7446862
  have htrace : WordTrace (prefixWord ++ tailWord_7446862) baseStart_7446862 baseEnd_7446862 := by
    simpa [prefixWord, tailWord_7446862, baseEnd_7446862] using wordTrace_append hprefix tailTrace_7446862
  have hstable : (prefixWord ++ tailWord_7446862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446862).length < 2 ^ (prefixWord ++ tailWord_7446862).sum := by decide
  have hdescent : baseEnd_7446862 < baseStart_7446862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446882 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_7446882 : Nat := 118140960795 + 7446882 * 2 ^ 59
def prefixEnd_7446882 : Nat := 4983230072969 + 3 ^ 40 * 7446882 * 2
def baseEnd_7446882 : Nat := 3823829843315238273627419

theorem tailTrace_7446882 : CollatzResearch.WordTrace tailWord_7446882 prefixEnd_7446882 3823829843315238273627419 := by
  unfold tailWord_7446882
  simp only [CollatzResearch.WordTrace]
  refine ⟨67902525051806453758863725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181073400138150543356969933 67902525051806453758863725)
  ·
    refine ⟨25463446894427420159573897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67902525051806453758863725 25463446894427420159573897)
    ·
      refine ⟨19097585170820565119680423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25463446894427420159573897 19097585170820565119680423)
      ·
        refine ⟨28646377756230847679520635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19097585170820565119680423 28646377756230847679520635)
        ·
          refine ⟨42969566634346271519280953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28646377756230847679520635 42969566634346271519280953)
          ·
            refine ⟨32227174975759703639460715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42969566634346271519280953 32227174975759703639460715)
            ·
              refine ⟨48340762463639555459191073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32227174975759703639460715 48340762463639555459191073)
              ·
                refine ⟨36255571847729666594393305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48340762463639555459191073 36255571847729666594393305)
                ·
                  refine ⟨27191678885797249945794979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36255571847729666594393305 27191678885797249945794979)
                  ·
                    refine ⟨40787518328695874918692469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27191678885797249945794979 40787518328695874918692469)
                    ·
                      refine ⟨3823829843315238273627419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40787518328695874918692469 3823829843315238273627419)
                      ·
                        rfl

theorem cell23_7446882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_7446882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446882 prefixEnd_7446882 := by exact prefixLift 7446882
  have htrace : WordTrace (prefixWord ++ tailWord_7446882) baseStart_7446882 baseEnd_7446882 := by
    simpa [prefixWord, tailWord_7446882, baseEnd_7446882] using wordTrace_append hprefix tailTrace_7446882
  have hstable : (prefixWord ++ tailWord_7446882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446882).length < 2 ^ (prefixWord ++ tailWord_7446882).sum := by decide
  have hdescent : baseEnd_7446882 < baseStart_7446882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446895 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 3]
def baseStart_7446895 : Nat := 118140960795 + 7446895 * 2 ^ 59
def prefixEnd_7446895 : Nat := 4983230072969 + 3 ^ 40 * 7446895 * 2
def baseEnd_7446895 : Nat := 3823836518563746722764859

theorem tailTrace_7446895 : CollatzResearch.WordTrace tailWord_7446895 prefixEnd_7446895 3823836518563746722764859 := by
  unfold tailWord_7446895
  simp only [CollatzResearch.WordTrace]
  refine ⟨271610574356178718255678139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181073716237452478837118759 271610574356178718255678139)
  ·
    refine ⟨407415861534268077383517209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271610574356178718255678139 407415861534268077383517209)
    ·
      refine ⟨305561896150701058037637907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407415861534268077383517209 305561896150701058037637907)
      ·
        refine ⟨458342844226051587056456861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305561896150701058037637907 458342844226051587056456861)
        ·
          refine ⟨171878566584769345146171323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 458342844226051587056456861 171878566584769345146171323)
          ·
            refine ⟨257817849877154017719256985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171878566584769345146171323 257817849877154017719256985)
            ·
              refine ⟨193363387407865513289442739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257817849877154017719256985 193363387407865513289442739)
              ·
                refine ⟨290045081111798269934164109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193363387407865513289442739 290045081111798269934164109)
                ·
                  refine ⟨108766905416924351225311541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 290045081111798269934164109 108766905416924351225311541)
                  ·
                    refine ⟨10196897382836657927372957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108766905416924351225311541 10196897382836657927372957)
                    ·
                      refine ⟨3823836518563746722764859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10196897382836657927372957 3823836518563746722764859)
                      ·
                        rfl

theorem cell23_7446895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 3].length) (baseStart_7446895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446895 prefixEnd_7446895 := by exact prefixLift 7446895
  have htrace : WordTrace (prefixWord ++ tailWord_7446895) baseStart_7446895 baseEnd_7446895 := by
    simpa [prefixWord, tailWord_7446895, baseEnd_7446895] using wordTrace_append hprefix tailTrace_7446895
  have hstable : (prefixWord ++ tailWord_7446895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446895).length < 2 ^ (prefixWord ++ tailWord_7446895).sum := by decide
  have hdescent : baseEnd_7446895 < baseStart_7446895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446913 : List Nat := [1, 2, 4, 3, 1, 2, 2, 2, 2, 2, 2]
def baseStart_7446913 : Nat := 118140960795 + 7446913 * 2 ^ 59
def prefixEnd_7446913 : Nat := 4983230072969 + 3 ^ 40 * 7446913 * 2
def baseEnd_7446913 : Nat := 3823845761215527652339777

theorem tailTrace_7446913 : CollatzResearch.WordTrace tailWord_7446913 prefixEnd_7446913 3823845761215527652339777 := by
  unfold tailWord_7446913
  simp only [CollatzResearch.WordTrace]
  refine ⟨271611230870113507329833393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181074153913409004886555595 271611230870113507329833393)
  ·
    refine ⟨203708423152585130497375045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271611230870113507329833393 203708423152585130497375045)
    ·
      refine ⟨38195329341109711968257821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203708423152585130497375045 38195329341109711968257821)
      ·
        refine ⟨14323248502916141988096683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38195329341109711968257821 14323248502916141988096683)
        ·
          refine ⟨21484872754374212982145025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14323248502916141988096683 21484872754374212982145025)
          ·
            refine ⟨16113654565780659736608769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21484872754374212982145025 16113654565780659736608769)
            ·
              refine ⟨12085240924335494802456577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16113654565780659736608769 12085240924335494802456577)
              ·
                refine ⟨9063930693251621101842433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12085240924335494802456577 9063930693251621101842433)
                ·
                  refine ⟨6797948019938715826381825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9063930693251621101842433 6797948019938715826381825)
                  ·
                    refine ⟨5098461014954036869786369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6797948019938715826381825 5098461014954036869786369)
                    ·
                      refine ⟨3823845761215527652339777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5098461014954036869786369 3823845761215527652339777)
                      ·
                        rfl

theorem cell23_7446913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_7446913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446913 prefixEnd_7446913 := by exact prefixLift 7446913
  have htrace : WordTrace (prefixWord ++ tailWord_7446913) baseStart_7446913 baseEnd_7446913 := by
    simpa [prefixWord, tailWord_7446913, baseEnd_7446913] using wordTrace_append hprefix tailTrace_7446913
  have hstable : (prefixWord ++ tailWord_7446913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446913).length < 2 ^ (prefixWord ++ tailWord_7446913).sum := by decide
  have hdescent : baseEnd_7446913 < baseStart_7446913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446962 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 5, 4]
def baseStart_7446962 : Nat := 118140960795 + 7446962 * 2 ^ 59
def prefixEnd_7446962 : Nat := 4983230072969 + 3 ^ 40 * 7446962 * 2
def baseEnd_7446962 : Nat := 1274623640589199320209017

theorem tailTrace_7446962 : CollatzResearch.WordTrace tailWord_7446962 prefixEnd_7446962 1274623640589199320209017 := by
  unfold tailWord_7446962
  simp only [CollatzResearch.WordTrace]
  refine ⟨67903254511733997174591785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181075345364623992465578093 67903254511733997174591785)
  ·
    refine ⟨50927440883800497880943839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67903254511733997174591785 50927440883800497880943839)
    ·
      refine ⟨76391161325700746821415759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50927440883800497880943839 76391161325700746821415759)
      ·
        refine ⟨114586741988551120232123639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76391161325700746821415759 114586741988551120232123639)
        ·
          refine ⟨171880112982826680348185459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114586741988551120232123639 171880112982826680348185459)
          ·
            refine ⟨257820169474240020522278189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171880112982826680348185459 257820169474240020522278189)
            ·
              refine ⟨96682563552840007695854321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257820169474240020522278189 96682563552840007695854321)
              ·
                refine ⟨72511922664630005771890741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96682563552840007695854321 72511922664630005771890741)
                ·
                  refine ⟨6797992749809063041114757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72511922664630005771890741 6797992749809063041114757)
                  ·
                    refine ⟨1274623640589199320209017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6797992749809063041114757 1274623640589199320209017)
                    ·
                      rfl

theorem cell23_7446962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_7446962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446962 prefixEnd_7446962 := by exact prefixLift 7446962
  have htrace : WordTrace (prefixWord ++ tailWord_7446962) baseStart_7446962 baseEnd_7446962 := by
    simpa [prefixWord, tailWord_7446962, baseEnd_7446962] using wordTrace_append hprefix tailTrace_7446962
  have hstable : (prefixWord ++ tailWord_7446962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446962).length < 2 ^ (prefixWord ++ tailWord_7446962).sum := by decide
  have hdescent : baseEnd_7446962 < baseStart_7446962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446964 : List Nat := [2, 5, 2, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_7446964 : Nat := 118140960795 + 7446964 * 2 ^ 59
def prefixEnd_7446964 : Nat := 4983230072969 + 3 ^ 40 * 7446964 * 2
def baseEnd_7446964 : Nat := 3823871948728906952802043

theorem tailTrace_7446964 : CollatzResearch.WordTrace tailWord_7446964 prefixEnd_7446964 3823871948728906952802043 := by
  unfold tailWord_7446964
  simp only [CollatzResearch.WordTrace]
  refine ⟨135806545496464371519969973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181075393995285828693293297 135806545496464371519969973)
  ·
    refine ⟨12731863640293534829997185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135806545496464371519969973 12731863640293534829997185)
    ·
      refine ⟨9548897730220151122497889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12731863640293534829997185 9548897730220151122497889)
      ·
        refine ⟨7161673297665113341873417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9548897730220151122497889 7161673297665113341873417)
        ·
          refine ⟨5371254973248835006405063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7161673297665113341873417 5371254973248835006405063)
          ·
            refine ⟨8056882459873252509607595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5371254973248835006405063 8056882459873252509607595)
            ·
              refine ⟨12085323689809878764411393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8056882459873252509607595 12085323689809878764411393)
              ·
                refine ⟨9063992767357409073308545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12085323689809878764411393 9063992767357409073308545)
                ·
                  refine ⟨6797994575518056804981409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9063992767357409073308545 6797994575518056804981409)
                  ·
                    refine ⟨5098495931638542603736057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6797994575518056804981409 5098495931638542603736057)
                    ·
                      refine ⟨3823871948728906952802043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5098495931638542603736057 3823871948728906952802043)
                      ·
                        rfl

theorem cell23_7446964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_7446964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446964 prefixEnd_7446964 := by exact prefixLift 7446964
  have htrace : WordTrace (prefixWord ++ tailWord_7446964) baseStart_7446964 baseEnd_7446964 := by
    simpa [prefixWord, tailWord_7446964, baseEnd_7446964] using wordTrace_append hprefix tailTrace_7446964
  have hstable : (prefixWord ++ tailWord_7446964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446964).length < 2 ^ (prefixWord ++ tailWord_7446964).sum := by decide
  have hdescent : baseEnd_7446964 < baseStart_7446964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7446969 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 2, 4, 2]
def baseStart_7446969 : Nat := 118140960795 + 7446969 * 2 ^ 59
def prefixEnd_7446969 : Nat := 4983230072969 + 3 ^ 40 * 7446969 * 2
def baseEnd_7446969 : Nat := 3823874516132179433239519

theorem tailTrace_7446969 : CollatzResearch.WordTrace tailWord_7446969 prefixEnd_7446969 3823874516132179433239519 := by
  unfold tailWord_7446969
  simp only [CollatzResearch.WordTrace]
  refine ⟨271613273357910628893871961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181075515571940419262581307 271613273357910628893871961)
  ·
    refine ⟨203709955018432971670403971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271613273357910628893871961 203709955018432971670403971)
    ·
      refine ⟨305564932527649457505605957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203709955018432971670403971 305564932527649457505605957)
      ·
        refine ⟨57293424848934273282301117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305564932527649457505605957 57293424848934273282301117)
        ·
          refine ⟨21485034318350352480862919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57293424848934273282301117 21485034318350352480862919)
          ·
            refine ⟨32227551477525528721294379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21485034318350352480862919 32227551477525528721294379)
            ·
              refine ⟨48341327216288293081941569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32227551477525528721294379 48341327216288293081941569)
              ·
                refine ⟨36255995412216219811456177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48341327216288293081941569 36255995412216219811456177)
                ·
                  refine ⟨27191996559162164858592133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36255995412216219811456177 27191996559162164858592133)
                  ·
                    refine ⟨5098499354842905910986025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27191996559162164858592133 5098499354842905910986025)
                    ·
                      refine ⟨3823874516132179433239519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5098499354842905910986025 3823874516132179433239519)
                      ·
                        rfl

theorem cell23_7446969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_7446969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7446969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7446969 prefixEnd_7446969 := by exact prefixLift 7446969
  have htrace : WordTrace (prefixWord ++ tailWord_7446969) baseStart_7446969 baseEnd_7446969 := by
    simpa [prefixWord, tailWord_7446969, baseEnd_7446969] using wordTrace_append hprefix tailTrace_7446969
  have hstable : (prefixWord ++ tailWord_7446969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7446969).length < 2 ^ (prefixWord ++ tailWord_7446969).sum := by decide
  have hdescent : baseEnd_7446969 < baseStart_7446969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7446969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447002 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3]
def baseStart_7447002 : Nat := 118140960795 + 7447002 * 2 ^ 59
def prefixEnd_7447002 : Nat := 4983230072969 + 3 ^ 40 * 7447002 * 2
def baseEnd_7447002 : Nat := 3823891460993777804126867

theorem tailTrace_7447002 : CollatzResearch.WordTrace tailWord_7447002 prefixEnd_7447002 3823891460993777804126867 := by
  unfold tailWord_7447002
  simp only [CollatzResearch.WordTrace]
  refine ⟨67903619241697768882455815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181076317977860717019882173 67903619241697768882455815)
  ·
    refine ⟨101855428862546653323683723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67903619241697768882455815 101855428862546653323683723)
    ·
      refine ⟨152783143293819979985525585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101855428862546653323683723 152783143293819979985525585)
      ·
        refine ⟨114587357470364984989144189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152783143293819979985525585 114587357470364984989144189)
        ·
          refine ⟨42970259051386869370929071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114587357470364984989144189 42970259051386869370929071)
          ·
            refine ⟨64455388577080304056393607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42970259051386869370929071 64455388577080304056393607)
            ·
              refine ⟨96683082865620456084590411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64455388577080304056393607 96683082865620456084590411)
              ·
                refine ⟨145024624298430684126885617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96683082865620456084590411 145024624298430684126885617)
                ·
                  refine ⟨108768468223823013095164213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145024624298430684126885617 108768468223823013095164213)
                  ·
                    refine ⟨10197043895983407477671645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108768468223823013095164213 10197043895983407477671645)
                    ·
                      refine ⟨3823891460993777804126867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10197043895983407477671645 3823891460993777804126867)
                      ·
                        rfl

theorem cell23_7447002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_7447002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447002 prefixEnd_7447002 := by exact prefixLift 7447002
  have htrace : WordTrace (prefixWord ++ tailWord_7447002) baseStart_7447002 baseEnd_7447002 := by
    simpa [prefixWord, tailWord_7447002, baseEnd_7447002] using wordTrace_append hprefix tailTrace_7447002
  have hstable : (prefixWord ++ tailWord_7447002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447002).length < 2 ^ (prefixWord ++ tailWord_7447002).sum := by decide
  have hdescent : baseEnd_7447002 < baseStart_7447002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447035 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 2, 10]
def baseStart_7447035 : Nat := 118140960795 + 7447035 * 2 ^ 59
def prefixEnd_7447035 : Nat := 4983230072969 + 3 ^ 40 * 7447035 * 2
def baseEnd_7447035 : Nat := 1274636135285125391671405

theorem tailTrace_7447035 : CollatzResearch.WordTrace tailWord_7447035 prefixEnd_7447035 1274636135285125391671405 := by
  unfold tailWord_7447035
  simp only [CollatzResearch.WordTrace]
  refine ⟨271615680575671522165774559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181077120383781014777183039 271615680575671522165774559)
  ·
    refine ⟨407423520863507283248661839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271615680575671522165774559 407423520863507283248661839)
    ·
      refine ⟨611135281295260924872992759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407423520863507283248661839 611135281295260924872992759)
      ·
        refine ⟨916702921942891387309489139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611135281295260924872992759 916702921942891387309489139)
        ·
          refine ⟨1375054382914337080964233709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916702921942891387309489139 1375054382914337080964233709)
          ·
            refine ⟨515645393592876405361587641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1375054382914337080964233709 515645393592876405361587641)
            ·
              refine ⟨386734045194657304021190731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515645393592876405361587641 386734045194657304021190731)
              ·
                refine ⟨580101067791985956031786097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386734045194657304021190731 580101067791985956031786097)
                ·
                  refine ⟨435075800843989467023839573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580101067791985956031786097 435075800843989467023839573)
                  ·
                    refine ⟨1274636135285125391671405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 435075800843989467023839573 1274636135285125391671405)
                    ·
                      rfl

theorem cell23_7447035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 10].length) (baseStart_7447035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447035 prefixEnd_7447035 := by exact prefixLift 7447035
  have htrace : WordTrace (prefixWord ++ tailWord_7447035) baseStart_7447035 baseEnd_7447035 := by
    simpa [prefixWord, tailWord_7447035, baseEnd_7447035] using wordTrace_append hprefix tailTrace_7447035
  have hstable : (prefixWord ++ tailWord_7447035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447035).length < 2 ^ (prefixWord ++ tailWord_7447035).sum := by decide
  have hdescent : baseEnd_7447035 < baseStart_7447035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447069 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 1, 6]
def baseStart_7447069 : Nat := 118140960795 + 7447069 * 2 ^ 59
def prefixEnd_7447069 : Nat := 4983230072969 + 3 ^ 40 * 7447069 * 2
def baseEnd_7447069 : Nat := 1274641954732543013996353

theorem tailTrace_7447069 : CollatzResearch.WordTrace tailWord_7447069 prefixEnd_7447069 1274641954732543013996353 := by
  unfold tailWord_7447069
  simp only [CollatzResearch.WordTrace]
  refine ⟨271616920657548345972512261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181077947105032230648341507 271616920657548345972512261)
  ·
    refine ⟨50928172623290314869846049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271616920657548345972512261 50928172623290314869846049)
    ·
      refine ⟨38196129467467736152384537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50928172623290314869846049 38196129467467736152384537)
      ·
        refine ⟨28647097100600802114288403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38196129467467736152384537 28647097100600802114288403)
        ·
          refine ⟨42970645650901203171432605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28647097100600802114288403 42970645650901203171432605)
          ·
            refine ⟨16113992119087951189287227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42970645650901203171432605 16113992119087951189287227)
            ·
              refine ⟨24170988178631926783930841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16113992119087951189287227 24170988178631926783930841)
              ·
                refine ⟨18128241133973945087948131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24170988178631926783930841 18128241133973945087948131)
                ·
                  refine ⟨27192361700960917631922197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18128241133973945087948131 27192361700960917631922197)
                  ·
                    refine ⟨1274641954732543013996353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27192361700960917631922197 1274641954732543013996353)
                    ·
                      rfl

theorem cell23_7447069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_7447069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447069 prefixEnd_7447069 := by exact prefixLift 7447069
  have htrace : WordTrace (prefixWord ++ tailWord_7447069) baseStart_7447069 baseEnd_7447069 := by
    simpa [prefixWord, tailWord_7447069, baseEnd_7447069] using wordTrace_append hprefix tailTrace_7447069
  have hstable : (prefixWord ++ tailWord_7447069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447069).length < 2 ^ (prefixWord ++ tailWord_7447069).sum := by decide
  have hdescent : baseEnd_7447069 < baseStart_7447069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447082 : List Nat := [3, 1, 4, 1, 1, 13]
def baseStart_7447082 : Nat := 118140960795 + 7447082 * 2 ^ 59
def prefixEnd_7447082 : Nat := 4983230072969 + 3 ^ 40 * 7447082 * 2
def baseEnd_7447082 : Nat := 15736347898955298317393

theorem tailTrace_7447082 : CollatzResearch.WordTrace tailWord_7447082 prefixEnd_7447082 15736347898955298317393 := by
  unfold tailWord_7447082
  simp only [CollatzResearch.WordTrace]
  refine ⟨67904348701625312298183875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181078263204334166128490333 67904348701625312298183875)
  ·
    refine ⟨101856523052437968447275813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67904348701625312298183875 101856523052437968447275813)
    ·
      refine ⟨19098098072332119083864215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101856523052437968447275813 19098098072332119083864215)
      ·
        refine ⟨28647147108498178625796323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19098098072332119083864215 28647147108498178625796323)
        ·
          refine ⟨42970720662747267938694485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28647147108498178625796323 42970720662747267938694485)
          ·
            refine ⟨15736347898955298317393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 42970720662747267938694485 15736347898955298317393)
            ·
              rfl

theorem cell23_7447082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 13].length) (baseStart_7447082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447082 prefixEnd_7447082 := by exact prefixLift 7447082
  have htrace : WordTrace (prefixWord ++ tailWord_7447082) baseStart_7447082 baseEnd_7447082 := by
    simpa [prefixWord, tailWord_7447082, baseEnd_7447082] using wordTrace_append hprefix tailTrace_7447082
  have hstable : (prefixWord ++ tailWord_7447082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447082).length < 2 ^ (prefixWord ++ tailWord_7447082).sum := by decide
  have hdescent : baseEnd_7447082 < baseStart_7447082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447109 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 1, 3, 3]
def baseStart_7447109 : Nat := 118140960795 + 7447109 * 2 ^ 59
def prefixEnd_7447109 : Nat := 4983230072969 + 3 ^ 40 * 7447109 * 2
def baseEnd_7447109 : Nat := 3823946403423808885488875

theorem tailTrace_7447109 : CollatzResearch.WordTrace tailWord_7447109 prefixEnd_7447109 3823946403423808885488875 := by
  unfold tailWord_7447109
  simp only [CollatzResearch.WordTrace]
  refine ⟨271618379577403432803968381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181078919718268955202645587 271618379577403432803968381)
  ·
    refine ⟨101856892341526287301488143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271618379577403432803968381 101856892341526287301488143)
    ·
      refine ⟨152785338512289430952232215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101856892341526287301488143 152785338512289430952232215)
      ·
        refine ⟨229178007768434146428348323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152785338512289430952232215 229178007768434146428348323)
        ·
          refine ⟨343767011652651219642522485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229178007768434146428348323 343767011652651219642522485)
          ·
            refine ⟨32228157342436051841486483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 343767011652651219642522485 32228157342436051841486483)
            ·
              refine ⟨48342236013654077762229725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32228157342436051841486483 48342236013654077762229725)
              ·
                refine ⟨18128338505120279160836147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48342236013654077762229725 18128338505120279160836147)
                ·
                  refine ⟨27192507757680418741254221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18128338505120279160836147 27192507757680418741254221)
                  ·
                    refine ⟨10197190409130157027970333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27192507757680418741254221 10197190409130157027970333)
                    ·
                      refine ⟨3823946403423808885488875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10197190409130157027970333 3823946403423808885488875)
                      ·
                        rfl

theorem cell23_7447109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_7447109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447109 prefixEnd_7447109 := by exact prefixLift 7447109
  have htrace : WordTrace (prefixWord ++ tailWord_7447109) baseStart_7447109 baseEnd_7447109 := by
    simpa [prefixWord, tailWord_7447109, baseEnd_7447109] using wordTrace_append hprefix tailTrace_7447109
  have hstable : (prefixWord ++ tailWord_7447109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447109).length < 2 ^ (prefixWord ++ tailWord_7447109).sum := by decide
  have hdescent : baseEnd_7447109 < baseStart_7447109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447110 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_7447110 : Nat := 118140960795 + 7447110 * 2 ^ 59
def prefixEnd_7447110 : Nat := 4983230072969 + 3 ^ 40 * 7447110 * 2
def baseEnd_7447110 : Nat := 3823946916904463381576371

theorem tailTrace_7447110 : CollatzResearch.WordTrace tailWord_7447110 prefixEnd_7447110 3823946916904463381576371 := by
  unfold tailWord_7447110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8488075501574994061711087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181078944033599873316503189 8488075501574994061711087)
  ·
    refine ⟨12732113252362491092566631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8488075501574994061711087 12732113252362491092566631)
    ·
      refine ⟨19098169878543736638849947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12732113252362491092566631 19098169878543736638849947)
      ·
        refine ⟨28647254817815604958274921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19098169878543736638849947 28647254817815604958274921)
        ·
          refine ⟨21485441113361703718706191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28647254817815604958274921 21485441113361703718706191)
          ·
            refine ⟨32228161670042555578059287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21485441113361703718706191 32228161670042555578059287)
            ·
              refine ⟨48342242505063833367088931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32228161670042555578059287 48342242505063833367088931)
              ·
                refine ⟨72513363757595750050633397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48342242505063833367088931 72513363757595750050633397)
                ·
                  refine ⟨6798127852274601567246881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72513363757595750050633397 6798127852274601567246881)
                  ·
                    refine ⟨5098595889205951175435161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6798127852274601567246881 5098595889205951175435161)
                    ·
                      refine ⟨3823946916904463381576371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5098595889205951175435161 3823946916904463381576371)
                      ·
                        rfl

theorem cell23_7447110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_7447110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447110 prefixEnd_7447110 := by exact prefixLift 7447110
  have htrace : WordTrace (prefixWord ++ tailWord_7447110) baseStart_7447110 baseEnd_7447110 := by
    simpa [prefixWord, tailWord_7447110, baseEnd_7447110] using wordTrace_append hprefix tailTrace_7447110
  have hstable : (prefixWord ++ tailWord_7447110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447110).length < 2 ^ (prefixWord ++ tailWord_7447110).sum := by decide
  have hdescent : baseEnd_7447110 < baseStart_7447110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447169 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_7447169 : Nat := 118140960795 + 7447169 * 2 ^ 59
def prefixEnd_7447169 : Nat := 4983230072969 + 3 ^ 40 * 7447169 * 2
def baseEnd_7447169 : Nat := 3823977212263078650738599

theorem tailTrace_7447169 : CollatzResearch.WordTrace tailWord_7447169 prefixEnd_7447169 3823977212263078650738599 := by
  unfold tailWord_7447169
  simp only [CollatzResearch.WordTrace]
  refine ⟨271620567957186063051152561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181080378638124042034101707 271620567957186063051152561)
  ·
    refine ⟨203715425967889547288364421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271620567957186063051152561 203715425967889547288364421)
    ·
      refine ⟨38196642368979290116568329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203715425967889547288364421 38196642368979290116568329)
      ·
        refine ⟨28647481776734467587426247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38196642368979290116568329 28647481776734467587426247)
        ·
          refine ⟨42971222665101701381139371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28647481776734467587426247 42971222665101701381139371)
          ·
            refine ⟨64456833997652552071709057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42971222665101701381139371 64456833997652552071709057)
            ·
              refine ⟨48342625498239414053781793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64456833997652552071709057 48342625498239414053781793)
              ·
                refine ⟨36256969123679560540336345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48342625498239414053781793 36256969123679560540336345)
                ·
                  refine ⟨27192726842759670405252259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36256969123679560540336345 27192726842759670405252259)
                  ·
                    refine ⟨40789090264139505607878389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27192726842759670405252259 40789090264139505607878389)
                    ·
                      refine ⟨3823977212263078650738599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40789090264139505607878389 3823977212263078650738599)
                      ·
                        rfl

theorem cell23_7447169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_7447169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447169 prefixEnd_7447169 := by exact prefixLift 7447169
  have htrace : WordTrace (prefixWord ++ tailWord_7447169) baseStart_7447169 baseEnd_7447169 := by
    simpa [prefixWord, tailWord_7447169, baseEnd_7447169] using wordTrace_append hprefix tailTrace_7447169
  have hstable : (prefixWord ++ tailWord_7447169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447169).length < 2 ^ (prefixWord ++ tailWord_7447169).sum := by decide
  have hdescent : baseEnd_7447169 < baseStart_7447169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447186 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_7447186 : Nat := 118140960795 + 7447186 * 2 ^ 59
def prefixEnd_7447186 : Nat := 4983230072969 + 3 ^ 40 * 7447186 * 2
def baseEnd_7447186 : Nat := 3823985941434205084226021

theorem tailTrace_7447186 : CollatzResearch.WordTrace tailWord_7447186 prefixEnd_7447186 3823985941434205084226021 := by
  unfold tailWord_7447186
  simp only [CollatzResearch.WordTrace]
  refine ⟨67905296999531118738630353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181080791998749649969680941 67905296999531118738630353)
  ·
    refine ⟨50928972749648339053972765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67905296999531118738630353 50928972749648339053972765)
    ·
      refine ⟨19098364781118127145239787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50928972749648339053972765 19098364781118127145239787)
      ·
        refine ⟨28647547171677190717859681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19098364781118127145239787 28647547171677190717859681)
        ·
          refine ⟨21485660378757893038394761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28647547171677190717859681 21485660378757893038394761)
          ·
            refine ⟨16114245284068419778796071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21485660378757893038394761 16114245284068419778796071)
            ·
              refine ⟨24171367926102629668194107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16114245284068419778796071 24171367926102629668194107)
              ·
                refine ⟨36257051889153944502291161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24171367926102629668194107 36257051889153944502291161)
                ·
                  refine ⟨27192788916865458376718371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36257051889153944502291161 27192788916865458376718371)
                  ·
                    refine ⟨40789183375298187565077557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27192788916865458376718371 40789183375298187565077557)
                    ·
                      refine ⟨3823985941434205084226021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40789183375298187565077557 3823985941434205084226021)
                      ·
                        rfl

theorem cell23_7447186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_7447186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447186 prefixEnd_7447186 := by exact prefixLift 7447186
  have htrace : WordTrace (prefixWord ++ tailWord_7447186) baseStart_7447186 baseEnd_7447186 := by
    simpa [prefixWord, tailWord_7447186, baseEnd_7447186] using wordTrace_append hprefix tailTrace_7447186
  have hstable : (prefixWord ++ tailWord_7447186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447186).length < 2 ^ (prefixWord ++ tailWord_7447186).sum := by decide
  have hdescent : baseEnd_7447186 < baseStart_7447186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447217 : List Nat := [1, 2, 2, 6, 1, 1, 1, 3, 2, 2, 2]
def baseStart_7447217 : Nat := 118140960795 + 7447217 * 2 ^ 59
def prefixEnd_7447217 : Nat := 4983230072969 + 3 ^ 40 * 7447217 * 2
def baseEnd_7447217 : Nat := 3824001859334494462938379

theorem tailTrace_7447217 : CollatzResearch.WordTrace tailWord_7447217 prefixEnd_7447217 3824001859334494462938379 := by
  unfold tailWord_7447217
  simp only [CollatzResearch.WordTrace]
  refine ⟨271622318661012167248899905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181081545774008111499266603 271622318661012167248899905)
  ·
    refine ⟨203716738995759125436674929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271622318661012167248899905 203716738995759125436674929)
    ·
      refine ⟨152787554246819344077506197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203716738995759125436674929 152787554246819344077506197)
      ·
        refine ⟨7161916605319656753633103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152787554246819344077506197 7161916605319656753633103)
        ·
          refine ⟨10742874907979485130449655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7161916605319656753633103 10742874907979485130449655)
          ·
            refine ⟨16114312361969227695674483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10742874907979485130449655 16114312361969227695674483)
            ·
              refine ⟨24171468542953841543511725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16114312361969227695674483 24171468542953841543511725)
              ·
                refine ⟨9064300703607690578816897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24171468542953841543511725 9064300703607690578816897)
                ·
                  refine ⟨6798225527705767934112673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9064300703607690578816897 6798225527705767934112673)
                  ·
                    refine ⟨5098669145779325950584505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6798225527705767934112673 5098669145779325950584505)
                    ·
                      refine ⟨3824001859334494462938379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5098669145779325950584505 3824001859334494462938379)
                      ·
                        rfl

theorem cell23_7447217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_7447217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447217 prefixEnd_7447217 := by exact prefixLift 7447217
  have htrace : WordTrace (prefixWord ++ tailWord_7447217) baseStart_7447217 baseEnd_7447217 := by
    simpa [prefixWord, tailWord_7447217, baseEnd_7447217] using wordTrace_append hprefix tailTrace_7447217
  have hstable : (prefixWord ++ tailWord_7447217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447217).length < 2 ^ (prefixWord ++ tailWord_7447217).sum := by decide
  have hdescent : baseEnd_7447217 < baseStart_7447217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447236 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 2, 5]
def baseStart_7447236 : Nat := 118140960795 + 7447236 * 2 ^ 59
def prefixEnd_7447236 : Nat := 4983230072969 + 3 ^ 40 * 7447236 * 2
def baseEnd_7447236 : Nat := 1274670538488976629533597

theorem tailTrace_7447236 : CollatzResearch.WordTrace tailWord_7447236 prefixEnd_7447236 1274670538488976629533597 := by
  unfold tailWord_7447236
  simp only [CollatzResearch.WordTrace]
  refine ⟨135811505823971666746920781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181082007765295555662561041 135811505823971666746920781)
  ·
    refine ⟨50929314683989375030095293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135811505823971666746920781 50929314683989375030095293)
    ·
      refine ⟨19098493006496015636285735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50929314683989375030095293 19098493006496015636285735)
      ·
        refine ⟨28647739509744023454428603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19098493006496015636285735 28647739509744023454428603)
        ·
          refine ⟨42971609264616035181642905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28647739509744023454428603 42971609264616035181642905)
          ·
            refine ⟨32228706948462026386232179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42971609264616035181642905 32228706948462026386232179)
            ·
              refine ⟨48343060422693039579348269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32228706948462026386232179 48343060422693039579348269)
              ·
                refine ⟨18128647658509889842255601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48343060422693039579348269 18128647658509889842255601)
                ·
                  refine ⟨13596485743882417381691701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18128647658509889842255601 13596485743882417381691701)
                  ·
                    refine ⟨1274670538488976629533597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13596485743882417381691701 1274670538488976629533597)
                    ·
                      rfl

theorem cell23_7447236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_7447236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447236 prefixEnd_7447236 := by exact prefixLift 7447236
  have htrace : WordTrace (prefixWord ++ tailWord_7447236) baseStart_7447236 baseEnd_7447236 := by
    simpa [prefixWord, tailWord_7447236, baseEnd_7447236] using wordTrace_append hprefix tailTrace_7447236
  have hstable : (prefixWord ++ tailWord_7447236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447236).length < 2 ^ (prefixWord ++ tailWord_7447236).sum := by decide
  have hdescent : baseEnd_7447236 < baseStart_7447236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447256 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 2, 1, 4]
def baseStart_7447256 : Nat := 118140960795 + 7447256 * 2 ^ 59
def prefixEnd_7447256 : Nat := 4983230072969 + 3 ^ 40 * 7447256 * 2
def baseEnd_7447256 : Nat := 3824021885080019810350699

theorem tailTrace_7447256 : CollatzResearch.WordTrace tailWord_7447256 prefixEnd_7447256 3824021885080019810350699 := by
  unfold tailWord_7447256
  simp only [CollatzResearch.WordTrace]
  refine ⟨135811870553935438454784811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181082494071913917939713081 135811870553935438454784811)
  ·
    refine ⟨203717805830903157682177217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135811870553935438454784811 203717805830903157682177217)
    ·
      refine ⟨152788354373177368261632913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203717805830903157682177217 152788354373177368261632913)
      ·
        refine ⟨114591265779883026196224685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152788354373177368261632913 114591265779883026196224685)
        ·
          refine ⟨42971724667456134823584257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114591265779883026196224685 42971724667456134823584257)
          ·
            refine ⟨32228793500592101117688193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42971724667456134823584257 32228793500592101117688193)
            ·
              refine ⟨24171595125444075838266145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32228793500592101117688193 24171595125444075838266145)
              ·
                refine ⟨18128696344083056878699609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24171595125444075838266145 18128696344083056878699609)
                ·
                  refine ⟨13596522258062292659024707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18128696344083056878699609 13596522258062292659024707)
                  ·
                    refine ⟨20394783387093438988537061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13596522258062292659024707 20394783387093438988537061)
                    ·
                      refine ⟨3824021885080019810350699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20394783387093438988537061 3824021885080019810350699)
                      ·
                        rfl

theorem cell23_7447256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_7447256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447256 prefixEnd_7447256 := by exact prefixLift 7447256
  have htrace : WordTrace (prefixWord ++ tailWord_7447256) baseStart_7447256 baseEnd_7447256 := by
    simpa [prefixWord, tailWord_7447256, baseEnd_7447256] using wordTrace_append hprefix tailTrace_7447256
  have hstable : (prefixWord ++ tailWord_7447256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447256).length < 2 ^ (prefixWord ++ tailWord_7447256).sum := by decide
  have hdescent : baseEnd_7447256 < baseStart_7447256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447300 : List Nat := [2, 3, 2, 2, 1, 1, 4, 3, 1, 4]
def baseStart_7447300 : Nat := 118140960795 + 7447300 * 2 ^ 59
def prefixEnd_7447300 : Nat := 4983230072969 + 3 ^ 40 * 7447300 * 2
def baseEnd_7447300 : Nat := 1274681492742939212733499

theorem tailTrace_7447300 : CollatzResearch.WordTrace tailWord_7447300 prefixEnd_7447300 1274681492742939212733499 := by
  unfold tailWord_7447300
  simp only [CollatzResearch.WordTrace]
  refine ⟨135812672959855736212085677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181083563946474314949447569 135812672959855736212085677)
  ·
    refine ⟨50929752359945901079532129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135812672959855736212085677 50929752359945901079532129)
    ·
      refine ⟨38197314269959425809649097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50929752359945901079532129 38197314269959425809649097)
      ·
        refine ⟨28647985702469569357236823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38197314269959425809649097 28647985702469569357236823)
        ·
          refine ⟨42971978553704354035855235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28647985702469569357236823 42971978553704354035855235)
          ·
            refine ⟨64457967830556531053782853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42971978553704354035855235 64457967830556531053782853)
            ·
              refine ⟨12085868968229349572584285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64457967830556531053782853 12085868968229349572584285)
              ·
                refine ⟨4532200863086006089719107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12085868968229349572584285 4532200863086006089719107)
                ·
                  refine ⟨6798301294629009134578661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4532200863086006089719107 6798301294629009134578661)
                  ·
                    refine ⟨1274681492742939212733499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6798301294629009134578661 1274681492742939212733499)
                    ·
                      rfl

theorem cell23_7447300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_7447300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447300 prefixEnd_7447300 := by exact prefixLift 7447300
  have htrace : WordTrace (prefixWord ++ tailWord_7447300) baseStart_7447300 baseEnd_7447300 := by
    simpa [prefixWord, tailWord_7447300, baseEnd_7447300] using wordTrace_append hprefix tailTrace_7447300
  have hstable : (prefixWord ++ tailWord_7447300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447300).length < 2 ^ (prefixWord ++ tailWord_7447300).sum := by decide
  have hdescent : baseEnd_7447300 < baseStart_7447300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447369 : List Nat := [1, 2, 1, 1, 2, 5, 11]
def baseStart_7447369 : Nat := 118140960795 + 7447369 * 2 ^ 59
def prefixEnd_7447369 : Nat := 4983230072969 + 3 ^ 40 * 7447369 * 2
def baseEnd_7447369 : Nat := 47210863066592319360959

theorem tailTrace_7447369 : CollatzResearch.WordTrace tailWord_7447369 prefixEnd_7447369 47210863066592319360959 := by
  unfold tailWord_7447369
  simp only [CollatzResearch.WordTrace]
  refine ⟨271627862556461497208433161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181085241704307664805622107 271627862556461497208433161)
  ·
    refine ⟨203720896917346122906324871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271627862556461497208433161 203720896917346122906324871)
    ·
      refine ⟨305581345376019184359487307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203720896917346122906324871 305581345376019184359487307)
      ·
        refine ⟨458372018064028776539230961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305581345376019184359487307 458372018064028776539230961)
        ·
          refine ⟨343779013548021582404423221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458372018064028776539230961 343779013548021582404423221)
          ·
            refine ⟨32229282520127023350414677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 343779013548021582404423221 32229282520127023350414677)
            ·
              refine ⟨47210863066592319360959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32229282520127023350414677 47210863066592319360959)
              ·
                rfl

theorem cell23_7447369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 11].length) (baseStart_7447369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447369 prefixEnd_7447369 := by exact prefixLift 7447369
  have htrace : WordTrace (prefixWord ++ tailWord_7447369) baseStart_7447369 baseEnd_7447369 := by
    simpa [prefixWord, tailWord_7447369, baseEnd_7447369] using wordTrace_append hprefix tailTrace_7447369
  have hstable : (prefixWord ++ tailWord_7447369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447369).length < 2 ^ (prefixWord ++ tailWord_7447369).sum := by decide
  have hdescent : baseEnd_7447369 < baseStart_7447369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447386 : List Nat := [3, 1, 1, 2, 1, 5, 2, 8]
def baseStart_7447386 : Nat := 118140960795 + 7447386 * 2 ^ 59
def prefixEnd_7447386 : Nat := 4983230072969 + 3 ^ 40 * 7447386 * 2
def baseEnd_7447386 : Nat := 141632912502411270434263

theorem tailTrace_7447386 : CollatzResearch.WordTrace tailWord_7447386 prefixEnd_7447386 141632912502411270434263 := by
  unfold tailWord_7447386
  simp only [CollatzResearch.WordTrace]
  refine ⟨67907120649349977277950503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181085655064933272741201341 67907120649349977277950503)
  ·
    refine ⟨101860680974024965916925755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67907120649349977277950503 101860680974024965916925755)
    ·
      refine ⟨152791021461037448875388633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101860680974024965916925755 152791021461037448875388633)
      ·
        refine ⟨114593266095778086656541475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152791021461037448875388633 114593266095778086656541475)
        ·
          refine ⟨171889899143667129984812213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114593266095778086656541475 171889899143667129984812213)
          ·
            refine ⟨16114678044718793436076145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171889899143667129984812213 16114678044718793436076145)
            ·
              refine ⟨12086008533539095077057109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16114678044718793436076145 12086008533539095077057109)
              ·
                refine ⟨141632912502411270434263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12086008533539095077057109 141632912502411270434263)
                ·
                  rfl

theorem cell23_7447386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 8].length) (baseStart_7447386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447386 prefixEnd_7447386 := by exact prefixLift 7447386
  have htrace : WordTrace (prefixWord ++ tailWord_7447386) baseStart_7447386 baseEnd_7447386 := by
    simpa [prefixWord, tailWord_7447386, baseEnd_7447386] using wordTrace_append hprefix tailTrace_7447386
  have hstable : (prefixWord ++ tailWord_7447386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447386).length < 2 ^ (prefixWord ++ tailWord_7447386).sum := by decide
  have hdescent : baseEnd_7447386 < baseStart_7447386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447400 : List Nat := [2, 1, 4, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_7447400 : Nat := 118140960795 + 7447400 * 2 ^ 59
def prefixEnd_7447400 : Nat := 4983230072969 + 3 ^ 40 * 7447400 * 2
def baseEnd_7447400 : Nat := 3824095826294267246950037

theorem tailTrace_7447400 : CollatzResearch.WordTrace tailWord_7447400 prefixEnd_7447400 3824095826294267246950037 := by
  unfold tailWord_7447400
  simp only [CollatzResearch.WordTrace]
  refine ⟨135814496609674594751405827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181085995479566126335207769 135814496609674594751405827)
  ·
    refine ⟨203721744914511892127108741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135814496609674594751405827 203721744914511892127108741)
    ·
      refine ⟨38197827171470979773832889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203721744914511892127108741 38197827171470979773832889)
      ·
        refine ⟨28648370378603234830374667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38197827171470979773832889 28648370378603234830374667)
        ·
          refine ⟨42972555567904852245562001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28648370378603234830374667 42972555567904852245562001)
          ·
            refine ⟨32229416675928639184171501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42972555567904852245562001 32229416675928639184171501)
            ·
              refine ⟨12086031253473239694064313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32229416675928639184171501 12086031253473239694064313)
              ·
                refine ⟨9064523440104929770548235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12086031253473239694064313 9064523440104929770548235)
                ·
                  refine ⟨13596785160157394655822353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9064523440104929770548235 13596785160157394655822353)
                  ·
                    refine ⟨10197588870118045991866765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13596785160157394655822353 10197588870118045991866765)
                    ·
                      refine ⟨3824095826294267246950037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10197588870118045991866765 3824095826294267246950037)
                      ·
                        rfl

theorem cell23_7447400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_7447400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447400 prefixEnd_7447400 := by exact prefixLift 7447400
  have htrace : WordTrace (prefixWord ++ tailWord_7447400) baseStart_7447400 baseEnd_7447400 := by
    simpa [prefixWord, tailWord_7447400, baseEnd_7447400] using wordTrace_append hprefix tailTrace_7447400
  have hstable : (prefixWord ++ tailWord_7447400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447400).length < 2 ^ (prefixWord ++ tailWord_7447400).sum := by decide
  have hdescent : baseEnd_7447400 < baseStart_7447400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447413 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_7447413 : Nat := 118140960795 + 7447413 * 2 ^ 59
def prefixEnd_7447413 : Nat := 4983230072969 + 3 ^ 40 * 7447413 * 2
def baseEnd_7447413 : Nat := 3824102501542775696087477

theorem tailTrace_7447413 : CollatzResearch.WordTrace tailWord_7447413 prefixEnd_7447413 3824102501542775696087477 := by
  unfold tailWord_7447413
  simp only [CollatzResearch.WordTrace]
  refine ⟨271629467368302092723034893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181086311578868061815356595 271629467368302092723034893)
  ·
    refine ⟨101861050263113284771138085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271629467368302092723034893 101861050263113284771138085)
    ·
      refine ⟨19098946924333740894588391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101861050263113284771138085 19098946924333740894588391)
      ·
        refine ⟨28648420386500611341882587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19098946924333740894588391 28648420386500611341882587)
        ·
          refine ⟨42972630579750917012823881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28648420386500611341882587 42972630579750917012823881)
          ·
            refine ⟨32229472934813187759617911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42972630579750917012823881 32229472934813187759617911)
            ·
              refine ⟨48344209402219781639426867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32229472934813187759617911 48344209402219781639426867)
              ·
                refine ⟨72516314103329672459140301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48344209402219781639426867 72516314103329672459140301)
                ·
                  refine ⟨27193617788748627172177613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72516314103329672459140301 27193617788748627172177613)
                  ·
                    refine ⟨10197606670780735189566605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27193617788748627172177613 10197606670780735189566605)
                    ·
                      refine ⟨3824102501542775696087477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10197606670780735189566605 3824102501542775696087477)
                      ·
                        rfl

theorem cell23_7447413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_7447413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447413 prefixEnd_7447413 := by exact prefixLift 7447413
  have htrace : WordTrace (prefixWord ++ tailWord_7447413) baseStart_7447413 baseEnd_7447413 := by
    simpa [prefixWord, tailWord_7447413, baseEnd_7447413] using wordTrace_append hprefix tailTrace_7447413
  have hstable : (prefixWord ++ tailWord_7447413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447413).length < 2 ^ (prefixWord ++ tailWord_7447413).sum := by decide
  have hdescent : baseEnd_7447413 < baseStart_7447413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447431 : List Nat := [1, 1, 4, 2, 3, 3, 2, 2, 1, 2, 2]
def baseStart_7447431 : Nat := 118140960795 + 7447431 * 2 ^ 59
def prefixEnd_7447431 : Nat := 4983230072969 + 3 ^ 40 * 7447431 * 2
def baseEnd_7447431 : Nat := 3824111744194556625662395

theorem tailTrace_7447431 : CollatzResearch.WordTrace tailWord_7447431 prefixEnd_7447431 3824111744194556625662395 := by
  unfold tailWord_7447431
  simp only [CollatzResearch.WordTrace]
  refine ⟨271630123882236881797190147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181086749254824587864793431 271630123882236881797190147)
  ·
    refine ⟨407445185823355322695785221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271630123882236881797190147 407445185823355322695785221)
    ·
      refine ⟨76395972341879123005459729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 407445185823355322695785221 76395972341879123005459729)
      ·
        refine ⟨57296979256409342254094797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76395972341879123005459729 57296979256409342254094797)
        ·
          refine ⟨21486367221153503345285549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57296979256409342254094797 21486367221153503345285549)
          ·
            refine ⟨8057387707932563754482081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21486367221153503345285549 8057387707932563754482081)
            ·
              refine ⟨6043040780949422815861561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8057387707932563754482081 6043040780949422815861561)
              ·
                refine ⟨4532280585712067111896171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6043040780949422815861561 4532280585712067111896171)
                ·
                  refine ⟨6798420878568100667844257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4532280585712067111896171 6798420878568100667844257)
                  ·
                    refine ⟨5098815658926075500883193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6798420878568100667844257 5098815658926075500883193)
                    ·
                      refine ⟨3824111744194556625662395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5098815658926075500883193 3824111744194556625662395)
                      ·
                        rfl

theorem cell23_7447431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_7447431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447431 prefixEnd_7447431 := by exact prefixLift 7447431
  have htrace : WordTrace (prefixWord ++ tailWord_7447431) baseStart_7447431 baseEnd_7447431 := by
    simpa [prefixWord, tailWord_7447431, baseEnd_7447431] using wordTrace_append hprefix tailTrace_7447431
  have hstable : (prefixWord ++ tailWord_7447431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447431).length < 2 ^ (prefixWord ++ tailWord_7447431).sum := by decide
  have hdescent : baseEnd_7447431 < baseStart_7447431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447436 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 2, 3, 4]
def baseStart_7447436 : Nat := 118140960795 + 7447436 * 2 ^ 59
def prefixEnd_7447436 : Nat := 4983230072969 + 3 ^ 40 * 7447436 * 2
def baseEnd_7447436 : Nat := 3824114311597829106099871

theorem tailTrace_7447436 : CollatzResearch.WordTrace tailWord_7447436 prefixEnd_7447436 3824114311597829106099871 := by
  unfold tailWord_7447436
  simp only [CollatzResearch.WordTrace]
  refine ⟨135815153123609383825561081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181086870831479178434081441 135815153123609383825561081)
  ·
    refine ⟨101861364842707037869170811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135815153123609383825561081 101861364842707037869170811)
    ·
      refine ⟨152792047264060556803756217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101861364842707037869170811 152792047264060556803756217)
      ·
        refine ⟨114594035448045417602817163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152792047264060556803756217 114594035448045417602817163)
        ·
          refine ⟨171891053172068126404225745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114594035448045417602817163 171891053172068126404225745)
          ·
            refine ⟨128918289879051094803169309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171891053172068126404225745 128918289879051094803169309)
            ·
              refine ⟨48344358704644160551188491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128918289879051094803169309 48344358704644160551188491)
              ·
                refine ⟨72516538056966240826782737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48344358704644160551188491 72516538056966240826782737)
                ·
                  refine ⟨54387403542724680620087053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72516538056966240826782737 54387403542724680620087053)
                  ·
                    refine ⟨20395276328521755232532645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54387403542724680620087053 20395276328521755232532645)
                    ·
                      refine ⟨3824114311597829106099871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20395276328521755232532645 3824114311597829106099871)
                      ·
                        rfl

theorem cell23_7447436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_7447436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447436 prefixEnd_7447436 := by exact prefixLift 7447436
  have htrace : WordTrace (prefixWord ++ tailWord_7447436) baseStart_7447436 baseEnd_7447436 := by
    simpa [prefixWord, tailWord_7447436, baseEnd_7447436] using wordTrace_append hprefix tailTrace_7447436
  have hstable : (prefixWord ++ tailWord_7447436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447436).length < 2 ^ (prefixWord ++ tailWord_7447436).sum := by decide
  have hdescent : baseEnd_7447436 < baseStart_7447436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447456 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 5]
def baseStart_7447456 : Nat := 118140960795 + 7447456 * 2 ^ 59
def prefixEnd_7447456 : Nat := 4983230072969 + 3 ^ 40 * 7447456 * 2
def baseEnd_7447456 : Nat := 3824124581210919027849779

theorem tailTrace_7447456 : CollatzResearch.WordTrace tailWord_7447456 prefixEnd_7447456 3824124581210919027849779 := by
  unfold tailWord_7447456
  simp only [CollatzResearch.WordTrace]
  refine ⟨135815517853573155533425111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181087357138097540711233481 135815517853573155533425111)
  ·
    refine ⟨203723276780359733300137667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135815517853573155533425111 203723276780359733300137667)
    ·
      refine ⟨305584915170539599950206501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203723276780359733300137667 305584915170539599950206501)
      ·
        refine ⟨57297171594476174990663719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305584915170539599950206501 57297171594476174990663719)
        ·
          refine ⟨85945757391714262485995579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57297171594476174990663719 85945757391714262485995579)
          ·
            refine ⟨128918636087571393728993369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85945757391714262485995579 128918636087571393728993369)
            ·
              refine ⟨96688977065678545296745027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128918636087571393728993369 96688977065678545296745027)
              ·
                refine ⟨145033465598517817945117541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96688977065678545296745027 145033465598517817945117541)
                ·
                  refine ⟨27193774799722090864709539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145033465598517817945117541 27193774799722090864709539)
                  ·
                    refine ⟨40790662199583136297064309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27193774799722090864709539 40790662199583136297064309)
                    ·
                      refine ⟨3824124581210919027849779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40790662199583136297064309 3824124581210919027849779)
                      ·
                        rfl

theorem cell23_7447456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_7447456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447456 prefixEnd_7447456 := by exact prefixLift 7447456
  have htrace : WordTrace (prefixWord ++ tailWord_7447456) baseStart_7447456 baseEnd_7447456 := by
    simpa [prefixWord, tailWord_7447456, baseEnd_7447456] using wordTrace_append hprefix tailTrace_7447456
  have hstable : (prefixWord ++ tailWord_7447456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447456).length < 2 ^ (prefixWord ++ tailWord_7447456).sum := by decide
  have hdescent : baseEnd_7447456 < baseStart_7447456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447503 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 3]
def baseStart_7447503 : Nat := 118140960795 + 7447503 * 2 ^ 59
def prefixEnd_7447503 : Nat := 4983230072969 + 3 ^ 40 * 7447503 * 2
def baseEnd_7447503 : Nat := 3824148714801680343962063

theorem tailTrace_7447503 : CollatzResearch.WordTrace tailWord_7447503 prefixEnd_7447503 3824148714801680343962063 := by
  unfold tailWord_7447503
  simp only [CollatzResearch.WordTrace]
  refine ⟨271632749937976038093811163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181088499958650692062540775 271632749937976038093811163)
  ·
    refine ⟨407449124906964057140716745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271632749937976038093811163 407449124906964057140716745)
    ·
      refine ⟨305586843680223042855537559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407449124906964057140716745 305586843680223042855537559)
      ·
        refine ⟨458380265520334564283306339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305586843680223042855537559 458380265520334564283306339)
        ·
          refine ⟨687570398280501846424959509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458380265520334564283306339 687570398280501846424959509)
          ·
            refine ⟨32229862419398524051169977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 687570398280501846424959509 32229862419398524051169977)
            ·
              refine ⟨24172396814548893038377483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32229862419398524051169977 24172396814548893038377483)
              ·
                refine ⟨36258595221823339557566225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24172396814548893038377483 36258595221823339557566225)
                ·
                  refine ⟨27193946416367504668174669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36258595221823339557566225 27193946416367504668174669)
                  ·
                    refine ⟨10197729906137814250565501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27193946416367504668174669 10197729906137814250565501)
                    ·
                      refine ⟨3824148714801680343962063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10197729906137814250565501 3824148714801680343962063)
                      ·
                        rfl

theorem cell23_7447503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 3].length) (baseStart_7447503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447503 prefixEnd_7447503 := by exact prefixLift 7447503
  have htrace : WordTrace (prefixWord ++ tailWord_7447503) baseStart_7447503 baseEnd_7447503 := by
    simpa [prefixWord, tailWord_7447503, baseEnd_7447503] using wordTrace_append hprefix tailTrace_7447503
  have hstable : (prefixWord ++ tailWord_7447503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447503).length < 2 ^ (prefixWord ++ tailWord_7447503).sum := by decide
  have hdescent : baseEnd_7447503 < baseStart_7447503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447510 : List Nat := [5, 2, 1, 1, 2, 1, 2, 2, 7]
def baseStart_7447510 : Nat := 118140960795 + 7447510 * 2 ^ 59
def prefixEnd_7447510 : Nat := 4983230072969 + 3 ^ 40 * 7447510 * 2
def baseEnd_7447510 : Nat := 424905812129584646286059

theorem tailTrace_7447510 : CollatzResearch.WordTrace tailWord_7447510 prefixEnd_7447510 424905812129584646286059 := by
  unfold tailWord_7447510
  simp only [CollatzResearch.WordTrace]
  refine ⟨16977062828059417393082249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181088670165967118859543989 16977062828059417393082249)
  ·
    refine ⟨12732797121044563044811687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16977062828059417393082249 12732797121044563044811687)
    ·
      refine ⟨19099195681566844567217531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12732797121044563044811687 19099195681566844567217531)
      ·
        refine ⟨28648793522350266850826297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19099195681566844567217531 28648793522350266850826297)
        ·
          refine ⟨21486595141762700138119723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28648793522350266850826297 21486595141762700138119723)
          ·
            refine ⟨32229892712644050207179585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21486595141762700138119723 32229892712644050207179585)
            ·
              refine ⟨24172419534483037655384689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32229892712644050207179585 24172419534483037655384689)
              ·
                refine ⟨18129314650862278241538517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24172419534483037655384689 18129314650862278241538517)
                ·
                  refine ⟨424905812129584646286059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18129314650862278241538517 424905812129584646286059)
                  ·
                    rfl

theorem cell23_7447510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_7447510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447510 prefixEnd_7447510 := by exact prefixLift 7447510
  have htrace : WordTrace (prefixWord ++ tailWord_7447510) baseStart_7447510 baseEnd_7447510 := by
    simpa [prefixWord, tailWord_7447510, baseEnd_7447510] using wordTrace_append hprefix tailTrace_7447510
  have hstable : (prefixWord ++ tailWord_7447510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447510).length < 2 ^ (prefixWord ++ tailWord_7447510).sum := by decide
  have hdescent : baseEnd_7447510 < baseStart_7447510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447523 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 2, 5]
def baseStart_7447523 : Nat := 118140960795 + 7447523 * 2 ^ 59
def prefixEnd_7447523 : Nat := 4983230072969 + 3 ^ 40 * 7447523 * 2
def baseEnd_7447523 : Nat := 1274719661471590088570657

theorem tailTrace_7447523 : CollatzResearch.WordTrace tailWord_7447523 prefixEnd_7447523 1274719661471590088570657 := by
  unfold tailWord_7447523
  simp only [CollatzResearch.WordTrace]
  refine ⟨271633479397903581509539223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181088986265269054339692815 271633479397903581509539223)
  ·
    refine ⟨407450219096855372264308835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271633479397903581509539223 407450219096855372264308835)
    ·
      refine ⟨611175328645283058396463253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407450219096855372264308835 611175328645283058396463253)
      ·
        refine ⟨28648843530247643362334215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 611175328645283058396463253 28648843530247643362334215)
        ·
          refine ⟨42973265295371465043501323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28648843530247643362334215 42973265295371465043501323)
          ·
            refine ⟨64459897943057197565251985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42973265295371465043501323 64459897943057197565251985)
            ·
              refine ⟨48344923457292898173938989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64459897943057197565251985 48344923457292898173938989)
              ·
                refine ⟨18129346296484836815227121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48344923457292898173938989 18129346296484836815227121)
                ·
                  refine ⟨13597009722363627611420341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18129346296484836815227121 13597009722363627611420341)
                  ·
                    refine ⟨1274719661471590088570657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13597009722363627611420341 1274719661471590088570657)
                    ·
                      rfl

theorem cell23_7447523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 5].length) (baseStart_7447523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447523 prefixEnd_7447523 := by exact prefixLift 7447523
  have htrace : WordTrace (prefixWord ++ tailWord_7447523) baseStart_7447523 baseEnd_7447523 := by
    simpa [prefixWord, tailWord_7447523, baseEnd_7447523] using wordTrace_append hprefix tailTrace_7447523
  have hstable : (prefixWord ++ tailWord_7447523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447523).length < 2 ^ (prefixWord ++ tailWord_7447523).sum := by decide
  have hdescent : baseEnd_7447523 < baseStart_7447523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447527 : List Nat := [1, 1, 5, 2, 2, 3, 1, 3, 5]
def baseStart_7447527 : Nat := 118140960795 + 7447527 * 2 ^ 59
def prefixEnd_7447527 : Nat := 4983230072969 + 3 ^ 40 * 7447527 * 2
def baseEnd_7447527 : Nat := 424906782037487583340217

theorem tailTrace_7447527 : CollatzResearch.WordTrace tailWord_7447527 prefixEnd_7447527 424906782037487583340217 := by
  unfold tailWord_7447527
  simp only [CollatzResearch.WordTrace]
  refine ⟨271633625289889090192684835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181089083526592726795123223 271633625289889090192684835)
  ·
    refine ⟨407450437934833635289027253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271633625289889090192684835 407450437934833635289027253)
    ·
      refine ⟨38198478556390653308346305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 407450437934833635289027253 38198478556390653308346305)
      ·
        refine ⟨28648858917292989981259729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38198478556390653308346305 28648858917292989981259729)
        ·
          refine ⟨21486644187969742485944797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28648858917292989981259729 21486644187969742485944797)
          ·
            refine ⟨8057491570488653432229299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21486644187969742485944797 8057491570488653432229299)
            ·
              refine ⟨12086237355732980148343949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8057491570488653432229299 12086237355732980148343949)
              ·
                refine ⟨4532339008399867555628981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12086237355732980148343949 4532339008399867555628981)
                ·
                  refine ⟨424906782037487583340217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4532339008399867555628981 424906782037487583340217)
                  ·
                    rfl

theorem cell23_7447527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 3, 5].length) (baseStart_7447527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447527 prefixEnd_7447527 := by exact prefixLift 7447527
  have htrace : WordTrace (prefixWord ++ tailWord_7447527) baseStart_7447527 baseEnd_7447527 := by
    simpa [prefixWord, tailWord_7447527, baseEnd_7447527] using wordTrace_append hprefix tailTrace_7447527
  have hstable : (prefixWord ++ tailWord_7447527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447527).length < 2 ^ (prefixWord ++ tailWord_7447527).sum := by decide
  have hdescent : baseEnd_7447527 < baseStart_7447527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447630 : List Nat := [4, 1, 1, 1, 1, 3, 2, 4, 1, 5]
def baseStart_7447630 : Nat := 118140960795 + 7447630 * 2 ^ 59
def prefixEnd_7447630 : Nat := 4983230072969 + 3 ^ 40 * 7447630 * 2
def baseEnd_7447630 : Nat := 1274737975614933782357993

theorem tailTrace_7447630 : CollatzResearch.WordTrace tailWord_7447630 prefixEnd_7447630 1274737975614933782357993 := by
  unfold tailWord_7447630
  simp only [CollatzResearch.WordTrace]
  refine ⟨33954672751064492347960543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181091588005677292522456229 33954672751064492347960543)
  ·
    refine ⟨50932009126596738521940815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33954672751064492347960543 50932009126596738521940815)
    ·
      refine ⟨76398013689895107782911223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50932009126596738521940815 76398013689895107782911223)
      ·
        refine ⟨114597020534842661674366835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76398013689895107782911223 114597020534842661674366835)
        ·
          refine ⟨171895530802263992511550253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114597020534842661674366835 171895530802263992511550253)
          ·
            refine ⟨64460824050848997191831345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171895530802263992511550253 64460824050848997191831345)
            ·
              refine ⟨48345618038136747893873509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64460824050848997191831345 48345618038136747893873509)
              ·
                refine ⟨9064803382150640230101283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48345618038136747893873509 9064803382150640230101283)
                ·
                  refine ⟨13597205073225960345151925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9064803382150640230101283 13597205073225960345151925)
                  ·
                    refine ⟨1274737975614933782357993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13597205073225960345151925 1274737975614933782357993)
                    ·
                      rfl

theorem cell23_7447630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_7447630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447630 prefixEnd_7447630 := by exact prefixLift 7447630
  have htrace : WordTrace (prefixWord ++ tailWord_7447630) baseStart_7447630 baseEnd_7447630 := by
    simpa [prefixWord, tailWord_7447630, baseEnd_7447630] using wordTrace_append hprefix tailTrace_7447630
  have hstable : (prefixWord ++ tailWord_7447630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447630).length < 2 ^ (prefixWord ++ tailWord_7447630).sum := by decide
  have hdescent : baseEnd_7447630 < baseStart_7447630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447638 : List Nat := [5, 2, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_7447638 : Nat := 118140960795 + 7447638 * 2 ^ 59
def prefixEnd_7447638 : Nat := 4983230072969 + 3 ^ 40 * 7447638 * 2
def baseEnd_7447638 : Nat := 1274739344896679105257981

theorem tailTrace_7447638 : CollatzResearch.WordTrace tailWord_7447638 prefixEnd_7447638 1274739344896679105257981 := by
  unfold tailWord_7447638
  simp only [CollatzResearch.WordTrace]
  refine ⟨16977354612030434759373473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181091782528324637433317045 16977354612030434759373473)
  ·
    refine ⟨12733015959022826069530105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16977354612030434759373473 12733015959022826069530105)
    ·
      refine ⟨9549761969267119552147579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12733015959022826069530105 9549761969267119552147579)
      ·
        refine ⟨14324642953900679328221369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9549761969267119552147579 14324642953900679328221369)
        ·
          refine ⟨10743482215425509496166027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14324642953900679328221369 10743482215425509496166027)
          ·
            refine ⟨16115223323138264244249041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10743482215425509496166027 16115223323138264244249041)
            ·
              refine ⟨12086417492353698183186781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16115223323138264244249041 12086417492353698183186781)
              ·
                refine ⟨4532406559632636818695043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12086417492353698183186781 4532406559632636818695043)
                ·
                  refine ⟨6798609839448955228042565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4532406559632636818695043 6798609839448955228042565)
                  ·
                    refine ⟨1274739344896679105257981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6798609839448955228042565 1274739344896679105257981)
                    ·
                      rfl

theorem cell23_7447638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_7447638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447638 prefixEnd_7447638 := by exact prefixLift 7447638
  have htrace : WordTrace (prefixWord ++ tailWord_7447638) baseStart_7447638 baseEnd_7447638 := by
    simpa [prefixWord, tailWord_7447638, baseEnd_7447638] using wordTrace_append hprefix tailTrace_7447638
  have hstable : (prefixWord ++ tailWord_7447638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447638).length < 2 ^ (prefixWord ++ tailWord_7447638).sum := by decide
  have hdescent : baseEnd_7447638 < baseStart_7447638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447660 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 4, 4]
def baseStart_7447660 : Nat := 118140960795 + 7447660 * 2 ^ 59
def prefixEnd_7447660 : Nat := 4983230072969 + 3 ^ 40 * 7447660 * 2
def baseEnd_7447660 : Nat := 1274743110421478743232947

theorem tailTrace_7447660 : CollatzResearch.WordTrace tailWord_7447660 prefixEnd_7447660 1274743110421478743232947 := by
  unfold tailWord_7447660
  simp only [CollatzResearch.WordTrace]
  refine ⟨135819238099203626953638217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181092317465604835938184289 135819238099203626953638217)
  ·
    refine ⟨101864428574402720215228663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135819238099203626953638217 101864428574402720215228663)
    ·
      refine ⟨152796642861604080322842995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101864428574402720215228663 152796642861604080322842995)
      ·
        refine ⟨229194964292406120484264493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152796642861604080322842995 229194964292406120484264493)
        ·
          refine ⟨85948111609652295181599185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229194964292406120484264493 85948111609652295181599185)
          ·
            refine ⟨64461083707239221386199389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85948111609652295181599185 64461083707239221386199389)
            ·
              refine ⟨24172906390214708019824771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64461083707239221386199389 24172906390214708019824771)
              ·
                refine ⟨36259359585322062029737157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24172906390214708019824771 36259359585322062029737157)
                ·
                  refine ⟨6798629922247886630575717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36259359585322062029737157 6798629922247886630575717)
                  ·
                    refine ⟨1274743110421478743232947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6798629922247886630575717 1274743110421478743232947)
                    ·
                      rfl

theorem cell23_7447660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_7447660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447660 prefixEnd_7447660 := by exact prefixLift 7447660
  have htrace : WordTrace (prefixWord ++ tailWord_7447660) baseStart_7447660 baseEnd_7447660 := by
    simpa [prefixWord, tailWord_7447660, baseEnd_7447660] using wordTrace_append hprefix tailTrace_7447660
  have hstable : (prefixWord ++ tailWord_7447660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447660).length < 2 ^ (prefixWord ++ tailWord_7447660).sum := by decide
  have hdescent : baseEnd_7447660 < baseStart_7447660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447663 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 6]
def baseStart_7447663 : Nat := 118140960795 + 7447663 * 2 ^ 59
def prefixEnd_7447663 : Nat := 4983230072969 + 3 ^ 40 * 7447663 * 2
def baseEnd_7447663 : Nat := 3824230871706399717961327

theorem tailTrace_7447663 : CollatzResearch.WordTrace tailWord_7447663 prefixEnd_7447663 3824230871706399717961327 := by
  unfold tailWord_7447663
  simp only [CollatzResearch.WordTrace]
  refine ⟨271638585617396385419635643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181092390411597590279757095 271638585617396385419635643)
  ·
    refine ⟨407457878426094578129453465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271638585617396385419635643 407457878426094578129453465)
    ·
      refine ⟨305593408819570933597090099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407457878426094578129453465 305593408819570933597090099)
      ·
        refine ⟨458390113229356400395635149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305593408819570933597090099 458390113229356400395635149)
        ·
          refine ⟨171896292461008650148363181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 458390113229356400395635149 171896292461008650148363181)
          ·
            refine ⟨64461109672878243805636193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171896292461008650148363181 64461109672878243805636193)
            ·
              refine ⟨48345832254658682854227145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64461109672878243805636193 48345832254658682854227145)
              ·
                refine ⟨36259374190994012140670359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48345832254658682854227145 36259374190994012140670359)
                ·
                  refine ⟨54389061286491018211005539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36259374190994012140670359 54389061286491018211005539)
                  ·
                    refine ⟨81583591929736527316508309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54389061286491018211005539 81583591929736527316508309)
                    ·
                      refine ⟨3824230871706399717961327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81583591929736527316508309 3824230871706399717961327)
                      ·
                        rfl

theorem cell23_7447663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_7447663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447663 prefixEnd_7447663 := by exact prefixLift 7447663
  have htrace : WordTrace (prefixWord ++ tailWord_7447663) baseStart_7447663 baseEnd_7447663 := by
    simpa [prefixWord, tailWord_7447663, baseEnd_7447663] using wordTrace_append hprefix tailTrace_7447663
  have hstable : (prefixWord ++ tailWord_7447663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447663).length < 2 ^ (prefixWord ++ tailWord_7447663).sum := by decide
  have hdescent : baseEnd_7447663 < baseStart_7447663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447680 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 4]
def baseStart_7447680 : Nat := 118140960795 + 7447680 * 2 ^ 59
def prefixEnd_7447680 : Nat := 4983230072969 + 3 ^ 40 * 7447680 * 2
def baseEnd_7447680 : Nat := 3824239600877526151448749

theorem tailTrace_7447680 : CollatzResearch.WordTrace tailWord_7447680 prefixEnd_7447680 3824239600877526151448749 := by
  unfold tailWord_7447680
  simp only [CollatzResearch.WordTrace]
  refine ⟨135819602829167398661502247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181092803772223198215336329 135819602829167398661502247)
  ·
    refine ⟨203729404243751097992253371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135819602829167398661502247 203729404243751097992253371)
    ·
      refine ⟨305594106365626646988380057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203729404243751097992253371 305594106365626646988380057)
      ·
        refine ⟨229195579774219985241285043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305594106365626646988380057 229195579774219985241285043)
        ·
          refine ⟨343793369661329977861927565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229195579774219985241285043 343793369661329977861927565)
          ·
            refine ⟨128922513622998741698222837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343793369661329977861927565 128922513622998741698222837)
            ·
              refine ⟨12086485652156132034208391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128922513622998741698222837 12086485652156132034208391)
              ·
                refine ⟨18129728478234198051312587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12086485652156132034208391 18129728478234198051312587)
                ·
                  refine ⟨27194592717351297076968881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18129728478234198051312587 27194592717351297076968881)
                  ·
                    refine ⟨20395944538013472807726661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27194592717351297076968881 20395944538013472807726661)
                    ·
                      refine ⟨3824239600877526151448749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20395944538013472807726661 3824239600877526151448749)
                      ·
                        rfl

theorem cell23_7447680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_7447680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447680 prefixEnd_7447680 := by exact prefixLift 7447680
  have htrace : WordTrace (prefixWord ++ tailWord_7447680) baseStart_7447680 baseEnd_7447680 := by
    simpa [prefixWord, tailWord_7447680, baseEnd_7447680] using wordTrace_append hprefix tailTrace_7447680
  have hstable : (prefixWord ++ tailWord_7447680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447680).length < 2 ^ (prefixWord ++ tailWord_7447680).sum := by decide
  have hdescent : baseEnd_7447680 < baseStart_7447680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447684 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 3, 2, 2]
def baseStart_7447684 : Nat := 118140960795 + 7447684 * 2 ^ 59
def prefixEnd_7447684 : Nat := 4983230072969 + 3 ^ 40 * 7447684 * 2
def baseEnd_7447684 : Nat := 3824241654800144135798731

theorem tailTrace_7447684 : CollatzResearch.WordTrace tailWord_7447684 prefixEnd_7447684 3824241654800144135798731 := by
  unfold tailWord_7447684
  simp only [CollatzResearch.WordTrace]
  refine ⟨135819675775160153003075053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181092901033546870670766737 135819675775160153003075053)
  ·
    refine ⟨50932378415685057376153145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135819675775160153003075053 50932378415685057376153145)
    ·
      refine ⟨38199283811763793032114859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50932378415685057376153145 38199283811763793032114859)
      ·
        refine ⟨57298925717645689548172289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38199283811763793032114859 57298925717645689548172289)
        ·
          refine ⟨42974194288234267161129217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57298925717645689548172289 42974194288234267161129217)
          ·
            refine ⟨32230645716175700370846913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42974194288234267161129217 32230645716175700370846913)
            ·
              refine ⟨24172984287131775278135185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32230645716175700370846913 24172984287131775278135185)
              ·
                refine ⟨18129738215348831458601389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24172984287131775278135185 18129738215348831458601389)
                ·
                  refine ⟨6798651830755811796975521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18129738215348831458601389 6798651830755811796975521)
                  ·
                    refine ⟨5098988873066858847731641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6798651830755811796975521 5098988873066858847731641)
                    ·
                      refine ⟨3824241654800144135798731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5098988873066858847731641 3824241654800144135798731)
                      ·
                        rfl

theorem cell23_7447684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_7447684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447684 prefixEnd_7447684 := by exact prefixLift 7447684
  have htrace : WordTrace (prefixWord ++ tailWord_7447684) baseStart_7447684 baseEnd_7447684 := by
    simpa [prefixWord, tailWord_7447684, baseEnd_7447684] using wordTrace_append hprefix tailTrace_7447684
  have hstable : (prefixWord ++ tailWord_7447684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447684).length < 2 ^ (prefixWord ++ tailWord_7447684).sum := by decide
  have hdescent : baseEnd_7447684 < baseStart_7447684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447717 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 4, 1, 3]
def baseStart_7447717 : Nat := 118140960795 + 7447717 * 2 ^ 59
def prefixEnd_7447717 : Nat := 4983230072969 + 3 ^ 40 * 7447717 * 2
def baseEnd_7447717 : Nat := 3824258599661742506686079

theorem tailTrace_7447717 : CollatzResearch.WordTrace tailWord_7447717 prefixEnd_7447717 3824258599661742506686079 := by
  unfold tailWord_7447717
  simp only [CollatzResearch.WordTrace]
  refine ⟨271640555159200752642101405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181093703439467168428067603 271640555159200752642101405)
  ·
    refine ⟨101865208184700282240788027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271640555159200752642101405 101865208184700282240788027)
    ·
      refine ⟨152797812277050423361182041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101865208184700282240788027 152797812277050423361182041)
      ·
        refine ⟨114598359207787817520886531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152797812277050423361182041 114598359207787817520886531)
        ·
          refine ⟨171897538811681726281329797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114598359207787817520886531 171897538811681726281329797)
          ·
            refine ⟨32230788527190323677749337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171897538811681726281329797 32230788527190323677749337)
            ·
              refine ⟨24173091395392742758312003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32230788527190323677749337 24173091395392742758312003)
              ·
                refine ⟨36259637093089114137468005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24173091395392742758312003 36259637093089114137468005)
                ·
                  refine ⟨6798681954954208900775251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36259637093089114137468005 6798681954954208900775251)
                  ·
                    refine ⟨10198022932431313351162877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6798681954954208900775251 10198022932431313351162877)
                    ·
                      refine ⟨3824258599661742506686079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10198022932431313351162877 3824258599661742506686079)
                      ·
                        rfl

theorem cell23_7447717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_7447717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447717 prefixEnd_7447717 := by exact prefixLift 7447717
  have htrace : WordTrace (prefixWord ++ tailWord_7447717) baseStart_7447717 baseEnd_7447717 := by
    simpa [prefixWord, tailWord_7447717, baseEnd_7447717] using wordTrace_append hprefix tailTrace_7447717
  have hstable : (prefixWord ++ tailWord_7447717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447717).length < 2 ^ (prefixWord ++ tailWord_7447717).sum := by decide
  have hdescent : baseEnd_7447717 < baseStart_7447717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447744 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 3, 3, 2]
def baseStart_7447744 : Nat := 118140960795 + 7447744 * 2 ^ 59
def prefixEnd_7447744 : Nat := 4983230072969 + 3 ^ 40 * 7447744 * 2
def baseEnd_7447744 : Nat := 3824272463639413901048455

theorem tailTrace_7447744 : CollatzResearch.WordTrace tailWord_7447744 prefixEnd_7447744 3824272463639413901048455 := by
  unfold tailWord_7447744
  simp only [CollatzResearch.WordTrace]
  refine ⟨135820769965051468126667143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181094359953401957502222857 135820769965051468126667143)
  ·
    refine ⟨203731154947577202190000715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135820769965051468126667143 203731154947577202190000715)
    ·
      refine ⟨305596732421365803285001073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203731154947577202190000715 305596732421365803285001073)
      ·
        refine ⟨229197549316024352463750805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305596732421365803285001073 229197549316024352463750805)
        ·
          refine ⟨10743635124188641521738319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 229197549316024352463750805 10743635124188641521738319)
          ·
            refine ⟨16115452686282962282607479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10743635124188641521738319 16115452686282962282607479)
            ·
              refine ⟨24173179029424443423911219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16115452686282962282607479 24173179029424443423911219)
              ·
                refine ⟨36259768544136665135866829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24173179029424443423911219 36259768544136665135866829)
                ·
                  refine ⟨13597413204051249425950061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36259768544136665135866829 13597413204051249425950061)
                  ·
                    refine ⟨5099029951519218534731273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13597413204051249425950061 5099029951519218534731273)
                    ·
                      refine ⟨3824272463639413901048455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5099029951519218534731273 3824272463639413901048455)
                      ·
                        rfl

theorem cell23_7447744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 3, 3, 2].length) (baseStart_7447744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447744 prefixEnd_7447744 := by exact prefixLift 7447744
  have htrace : WordTrace (prefixWord ++ tailWord_7447744) baseStart_7447744 baseEnd_7447744 := by
    simpa [prefixWord, tailWord_7447744, baseEnd_7447744] using wordTrace_append hprefix tailTrace_7447744
  have hstable : (prefixWord ++ tailWord_7447744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447744).length < 2 ^ (prefixWord ++ tailWord_7447744).sum := by decide
  have hdescent : baseEnd_7447744 < baseStart_7447744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447753 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 1, 5, 6]
def baseStart_7447753 : Nat := 118140960795 + 7447753 * 2 ^ 59
def prefixEnd_7447753 : Nat := 4983230072969 + 3 ^ 40 * 7447753 * 2
def baseEnd_7447753 : Nat := 3824277084965304365835913

theorem tailTrace_7447753 : CollatzResearch.WordTrace tailWord_7447753 prefixEnd_7447753 3824277084965304365835913 := by
  unfold tailWord_7447753
  simp only [CollatzResearch.WordTrace]
  refine ⟨271641868187070330790411913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181094578791380220526941275 271641868187070330790411913)
  ·
    refine ⟨203731401140302748092808935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271641868187070330790411913 203731401140302748092808935)
    ·
      refine ⟨305597101710454122139213403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203731401140302748092808935 305597101710454122139213403)
      ·
        refine ⟨458395652565681183208820105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305597101710454122139213403 458395652565681183208820105)
        ·
          refine ⟨343796739424260887406615079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458395652565681183208820105 343796739424260887406615079)
          ·
            refine ⟨515695109136391331109922619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343796739424260887406615079 515695109136391331109922619)
            ·
              refine ⟨773542663704586996664883929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515695109136391331109922619 773542663704586996664883929)
              ·
                refine ⟨580156997778440247498662947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 773542663704586996664883929 580156997778440247498662947)
                ·
                  refine ⟨870235496667660371247994421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 580156997778440247498662947 870235496667660371247994421)
                  ·
                    refine ⟨81584577812593159804499477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 870235496667660371247994421 81584577812593159804499477)
                    ·
                      refine ⟨3824277084965304365835913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81584577812593159804499477 3824277084965304365835913)
                      ·
                        rfl

theorem cell23_7447753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_7447753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447753 prefixEnd_7447753 := by exact prefixLift 7447753
  have htrace : WordTrace (prefixWord ++ tailWord_7447753) baseStart_7447753 baseEnd_7447753 := by
    simpa [prefixWord, tailWord_7447753, baseEnd_7447753] using wordTrace_append hprefix tailTrace_7447753
  have hstable : (prefixWord ++ tailWord_7447753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447753).length < 2 ^ (prefixWord ++ tailWord_7447753).sum := by decide
  have hdescent : baseEnd_7447753 < baseStart_7447753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447763 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 9]
def baseStart_7447763 : Nat := 118140960795 + 7447763 * 2 ^ 59
def prefixEnd_7447763 : Nat := 4983230072969 + 3 ^ 40 * 7447763 * 2
def baseEnd_7447763 : Nat := 424920246641316591856763

theorem tailTrace_7447763 : CollatzResearch.WordTrace tailWord_7447763 prefixEnd_7447763 424920246641316591856763 := by
  unfold tailWord_7447763
  simp only [CollatzResearch.WordTrace]
  refine ⟨271642232917034102498275943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181094821944689401665517295 271642232917034102498275943)
  ·
    refine ⟨407463349375551153747413915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271642232917034102498275943 407463349375551153747413915)
    ·
      refine ⟨611195024063326730621120873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407463349375551153747413915 611195024063326730621120873)
      ·
        refine ⟨458396268047495047965840655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 611195024063326730621120873 458396268047495047965840655)
        ·
          refine ⟨687594402071242571948760983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458396268047495047965840655 687594402071242571948760983)
          ·
            refine ⟨1031391603106863857923141475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687594402071242571948760983 1031391603106863857923141475)
            ·
              refine ⟨1547087404660295786884712213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031391603106863857923141475 1547087404660295786884712213)
              ·
                refine ⟨72519722093451365010220885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1547087404660295786884712213 72519722093451365010220885)
                ·
                  refine ⟨424920246641316591856763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72519722093451365010220885 424920246641316591856763)
                  ·
                    rfl

theorem cell23_7447763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 9].length) (baseStart_7447763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447763 prefixEnd_7447763 := by exact prefixLift 7447763
  have htrace : WordTrace (prefixWord ++ tailWord_7447763) baseStart_7447763 baseEnd_7447763 := by
    simpa [prefixWord, tailWord_7447763, baseEnd_7447763] using wordTrace_append hprefix tailTrace_7447763
  have hstable : (prefixWord ++ tailWord_7447763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447763).length < 2 ^ (prefixWord ++ tailWord_7447763).sum := by decide
  have hdescent : baseEnd_7447763 < baseStart_7447763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447770 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4]
def baseStart_7447770 : Nat := 118140960795 + 7447770 * 2 ^ 59
def prefixEnd_7447770 : Nat := 4983230072969 + 3 ^ 40 * 7447770 * 2
def baseEnd_7447770 : Nat := 3824285814136430799323335

theorem tailTrace_7447770 : CollatzResearch.WordTrace tailWord_7447770 prefixEnd_7447770 3824285814136430799323335 := by
  unfold tailWord_7447770
  simp only [CollatzResearch.WordTrace]
  refine ⟨67910622057002185673445191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181094992152005828462520509 67910622057002185673445191)
  ·
    refine ⟨101865933085503278510167787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67910622057002185673445191 101865933085503278510167787)
    ·
      refine ⟨152798899628254917765251681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101865933085503278510167787 152798899628254917765251681)
      ·
        refine ⟨114599174721191188323938761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152798899628254917765251681 114599174721191188323938761)
        ·
          refine ⟨85949381040893391242954071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114599174721191188323938761 85949381040893391242954071)
          ·
            refine ⟨128924071561340086864431107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85949381040893391242954071 128924071561340086864431107)
            ·
              refine ⟨193386107342010130296646661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128924071561340086864431107 193386107342010130296646661)
              ·
                refine ⟨36259895126626899430621249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193386107342010130296646661 36259895126626899430621249)
                ·
                  refine ⟨27194921344970174572965937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36259895126626899430621249 27194921344970174572965937)
                  ·
                    refine ⟨20396191008727630929724453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27194921344970174572965937 20396191008727630929724453)
                    ·
                      refine ⟨3824285814136430799323335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20396191008727630929724453 3824285814136430799323335)
                      ·
                        rfl

theorem cell23_7447770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_7447770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447770 prefixEnd_7447770 := by exact prefixLift 7447770
  have htrace : WordTrace (prefixWord ++ tailWord_7447770) baseStart_7447770 baseEnd_7447770 := by
    simpa [prefixWord, tailWord_7447770, baseEnd_7447770] using wordTrace_append hprefix tailTrace_7447770
  have hstable : (prefixWord ++ tailWord_7447770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447770).length < 2 ^ (prefixWord ++ tailWord_7447770).sum := by decide
  have hdescent : baseEnd_7447770 < baseStart_7447770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447878 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_7447878 : Nat := 118140960795 + 7447878 * 2 ^ 59
def prefixEnd_7447878 : Nat := 4983230072969 + 3 ^ 40 * 7447878 * 2
def baseEnd_7447878 : Nat := 1274780423349038792257613

theorem tailTrace_7447878 : CollatzResearch.WordTrace tailWord_7447878 prefixEnd_7447878 1274780423349038792257613 := by
  unfold tailWord_7447878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8488950853488046160584759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181097618207744984759141525 8488950853488046160584759)
  ·
    refine ⟨12733426280232069240877139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8488950853488046160584759 12733426280232069240877139)
    ·
      refine ⟨19100139420348103861315709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12733426280232069240877139 19100139420348103861315709)
      ·
        refine ⟨7162552282630538947993391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19100139420348103861315709 7162552282630538947993391)
        ·
          refine ⟨10743828423945808421990087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7162552282630538947993391 10743828423945808421990087)
          ·
            refine ⟨16115742635918712632985131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10743828423945808421990087 16115742635918712632985131)
            ·
              refine ⟨24173613953878068949477697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16115742635918712632985131 24173613953878068949477697)
              ·
                refine ⟨18130210465408551712108273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24173613953878068949477697 18130210465408551712108273)
                ·
                  refine ⟨13597657849056413784081205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18130210465408551712108273 13597657849056413784081205)
                  ·
                    refine ⟨1274780423349038792257613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13597657849056413784081205 1274780423349038792257613)
                    ·
                      rfl

theorem cell23_7447878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_7447878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447878 prefixEnd_7447878 := by exact prefixLift 7447878
  have htrace : WordTrace (prefixWord ++ tailWord_7447878) baseStart_7447878 baseEnd_7447878 := by
    simpa [prefixWord, tailWord_7447878, baseEnd_7447878] using wordTrace_append hprefix tailTrace_7447878
  have hstable : (prefixWord ++ tailWord_7447878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447878).length < 2 ^ (prefixWord ++ tailWord_7447878).sum := by decide
  have hdescent : baseEnd_7447878 < baseStart_7447878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447884 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 2, 2, 3]
def baseStart_7447884 : Nat := 118140960795 + 7447884 * 2 ^ 59
def prefixEnd_7447884 : Nat := 4983230072969 + 3 ^ 40 * 7447884 * 2
def baseEnd_7447884 : Nat := 3824344350931043353297811

theorem tailTrace_7447884 : CollatzResearch.WordTrace tailWord_7447884 prefixEnd_7447884 3824344350931043353297811 := by
  unfold tailWord_7447884
  simp only [CollatzResearch.WordTrace]
  refine ⟨135823323074797870081715353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181097764099730493442287137 135823323074797870081715353)
  ·
    refine ⟨101867492306098402561286515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135823323074797870081715353 101867492306098402561286515)
    ·
      refine ⟨152801238459147603841929773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101867492306098402561286515 152801238459147603841929773)
      ·
        refine ⟨57300464422180351440723665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152801238459147603841929773 57300464422180351440723665)
        ·
          refine ⟨42975348316635263580542749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57300464422180351440723665 42975348316635263580542749)
          ·
            refine ⟨16115755618738223842703531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42975348316635263580542749 16115755618738223842703531)
            ·
              refine ⟨24173633428107335764055297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16115755618738223842703531 24173633428107335764055297)
              ·
                refine ⟨18130225071080501823041473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24173633428107335764055297 18130225071080501823041473)
                ·
                  refine ⟨13597668803310376367281105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18130225071080501823041473 13597668803310376367281105)
                  ·
                    refine ⟨10198251602482782275460829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13597668803310376367281105 10198251602482782275460829)
                    ·
                      refine ⟨3824344350931043353297811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10198251602482782275460829 3824344350931043353297811)
                      ·
                        rfl

theorem cell23_7447884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_7447884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447884 prefixEnd_7447884 := by exact prefixLift 7447884
  have htrace : WordTrace (prefixWord ++ tailWord_7447884) baseStart_7447884 baseEnd_7447884 := by
    simpa [prefixWord, tailWord_7447884, baseEnd_7447884] using wordTrace_append hprefix tailTrace_7447884
  have hstable : (prefixWord ++ tailWord_7447884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447884).length < 2 ^ (prefixWord ++ tailWord_7447884).sum := by decide
  have hdescent : baseEnd_7447884 < baseStart_7447884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447891 : List Nat := [1, 1, 1, 2, 1, 1, 9, 2, 1, 4]
def baseStart_7447891 : Nat := 118140960795 + 7447891 * 2 ^ 59
def prefixEnd_7447891 : Nat := 4983230072969 + 3 ^ 40 * 7447891 * 2
def baseEnd_7447891 : Nat := 1274782648431874941970093

theorem tailTrace_7447891 : CollatzResearch.WordTrace tailWord_7447891 prefixEnd_7447891 1274782648431874941970093 := by
  unfold tailWord_7447891
  simp only [CollatzResearch.WordTrace]
  refine ⟨271646901460570380358935527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181097934307046920239290351 271646901460570380358935527)
  ·
    refine ⟨407470352190855570538403291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271646901460570380358935527 407470352190855570538403291)
    ·
      refine ⟨611205528286283355807604937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407470352190855570538403291 611205528286283355807604937)
      ·
        refine ⟨458404146214712516855703703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 611205528286283355807604937 458404146214712516855703703)
        ·
          refine ⟨687606219322068775283555555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458404146214712516855703703 687606219322068775283555555)
          ·
            refine ⟨1031409328983103162925333333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687606219322068775283555555 1031409328983103162925333333)
            ·
              refine ⟨6043414037010370095265625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1031409328983103162925333333 6043414037010370095265625)
              ·
                refine ⟨4532560527757777571449219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6043414037010370095265625 4532560527757777571449219)
                ·
                  refine ⟨6798840791636666357173829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4532560527757777571449219 6798840791636666357173829)
                  ·
                    refine ⟨1274782648431874941970093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6798840791636666357173829 1274782648431874941970093)
                    ·
                      rfl

theorem cell23_7447891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 1, 4].length) (baseStart_7447891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447891 prefixEnd_7447891 := by exact prefixLift 7447891
  have htrace : WordTrace (prefixWord ++ tailWord_7447891) baseStart_7447891 baseEnd_7447891 := by
    simpa [prefixWord, tailWord_7447891, baseEnd_7447891] using wordTrace_append hprefix tailTrace_7447891
  have hstable : (prefixWord ++ tailWord_7447891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447891).length < 2 ^ (prefixWord ++ tailWord_7447891).sum := by decide
  have hdescent : baseEnd_7447891 < baseStart_7447891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447904 : List Nat := [2, 1, 1, 3, 4, 1, 4, 1, 6]
def baseStart_7447904 : Nat := 118140960795 + 7447904 * 2 ^ 59
def prefixEnd_7447904 : Nat := 4983230072969 + 3 ^ 40 * 7447904 * 2
def baseEnd_7447904 : Nat := 424928291171570363894191

theorem tailTrace_7447904 : CollatzResearch.WordTrace tailWord_7447904 prefixEnd_7447904 424928291171570363894191 := by
  unfold tailWord_7447904
  simp only [CollatzResearch.WordTrace]
  refine ⟨135823687804761641789579383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181098250406348855719439177 135823687804761641789579383)
  ·
    refine ⟨203735531707142462684369075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135823687804761641789579383 203735531707142462684369075)
    ·
      refine ⟨305603297560713694026553613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203735531707142462684369075 305603297560713694026553613)
      ·
        refine ⟨114601236585267635259957605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305603297560713694026553613 114601236585267635259957605)
        ·
          refine ⟨21487731859737681611242051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114601236585267635259957605 21487731859737681611242051)
          ·
            refine ⟨32231597789606522416863077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21487731859737681611242051 32231597789606522416863077)
            ·
              refine ⟨6043424585551222953161827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32231597789606522416863077 6043424585551222953161827)
              ·
                refine ⟨9065136878326834429742741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6043424585551222953161827 9065136878326834429742741)
                ·
                  refine ⟨424928291171570363894191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9065136878326834429742741 424928291171570363894191)
                  ·
                    rfl

theorem cell23_7447904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 6].length) (baseStart_7447904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447904 prefixEnd_7447904 := by exact prefixLift 7447904
  have htrace : WordTrace (prefixWord ++ tailWord_7447904) baseStart_7447904 baseEnd_7447904 := by
    simpa [prefixWord, tailWord_7447904, baseEnd_7447904] using wordTrace_append hprefix tailTrace_7447904
  have hstable : (prefixWord ++ tailWord_7447904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447904).length < 2 ^ (prefixWord ++ tailWord_7447904).sum := by decide
  have hdescent : baseEnd_7447904 < baseStart_7447904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447918 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_7447918 : Nat := 118140960795 + 7447918 * 2 ^ 59
def prefixEnd_7447918 : Nat := 4983230072969 + 3 ^ 40 * 7447918 * 2
def baseEnd_7447918 : Nat := 3824361809273296220272655

theorem tailTrace_7447918 : CollatzResearch.WordTrace tailWord_7447918 prefixEnd_7447918 3824361809273296220272655 := by
  unfold tailWord_7447918
  simp only [CollatzResearch.WordTrace]
  refine ⟨33955985778934070496271051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181098590820981709313445605 33955985778934070496271051)
  ·
    refine ⟨50933978668401105744406577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33955985778934070496271051 50933978668401105744406577)
    ·
      refine ⟨38200484001300829308304933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50933978668401105744406577 38200484001300829308304933)
      ·
        refine ⟨7162590750243905495307175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38200484001300829308304933 7162590750243905495307175)
        ·
          refine ⟨10743886125365858242960763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7162590750243905495307175 10743886125365858242960763)
          ·
            refine ⟨16115829188048787364441145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10743886125365858242960763 16115829188048787364441145)
            ·
              refine ⟨12086871891036590523330859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16115829188048787364441145 12086871891036590523330859)
              ·
                refine ⟨18130307836554885784996289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12086871891036590523330859 18130307836554885784996289)
                ·
                  refine ⟨13597730877416164338747217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18130307836554885784996289 13597730877416164338747217)
                  ·
                    refine ⟨10198298158062123254060413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13597730877416164338747217 10198298158062123254060413)
                    ·
                      refine ⟨3824361809273296220272655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10198298158062123254060413 3824361809273296220272655)
                      ·
                        rfl

theorem cell23_7447918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_7447918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447918 prefixEnd_7447918 := by exact prefixLift 7447918
  have htrace : WordTrace (prefixWord ++ tailWord_7447918) baseStart_7447918 baseEnd_7447918 := by
    simpa [prefixWord, tailWord_7447918, baseEnd_7447918] using wordTrace_append hprefix tailTrace_7447918
  have hstable : (prefixWord ++ tailWord_7447918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447918).length < 2 ^ (prefixWord ++ tailWord_7447918).sum := by decide
  have hdescent : baseEnd_7447918 < baseStart_7447918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447931 : List Nat := [1, 1, 1, 1, 1, 6, 2, 5, 1, 1, 3]
def baseStart_7447931 : Nat := 118140960795 + 7447931 * 2 ^ 59
def prefixEnd_7447931 : Nat := 4983230072969 + 3 ^ 40 * 7447931 * 2
def baseEnd_7447931 : Nat := 3824368484521804669410095

theorem tailTrace_7447931 : CollatzResearch.WordTrace tailWord_7447931 prefixEnd_7447931 3824368484521804669410095 := by
  unfold tailWord_7447931
  simp only [CollatzResearch.WordTrace]
  refine ⟨271648360380425467190391647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181098906920283644793594431 271648360380425467190391647)
  ·
    refine ⟨407472540570638200785587471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271648360380425467190391647 407472540570638200785587471)
    ·
      refine ⟨611208810855957301178381207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407472540570638200785587471 611208810855957301178381207)
      ·
        refine ⟨916813216283935951767571811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611208810855957301178381207 916813216283935951767571811)
        ·
          refine ⟨1375219824425903927651357717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916813216283935951767571811 1375219824425903927651357717)
          ·
            refine ⟨64463429269964246608657393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1375219824425903927651357717 64463429269964246608657393)
            ·
              refine ⟨48347571952473184956493045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64463429269964246608657393 48347571952473184956493045)
              ·
                refine ⟨4532584870544361089671223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48347571952473184956493045 4532584870544361089671223)
                ·
                  refine ⟨6798877305816541634506835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4532584870544361089671223 6798877305816541634506835)
                  ·
                    refine ⟨10198315958724812451760253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6798877305816541634506835 10198315958724812451760253)
                    ·
                      refine ⟨3824368484521804669410095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10198315958724812451760253 3824368484521804669410095)
                      ·
                        rfl

theorem cell23_7447931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 1, 1, 3].length) (baseStart_7447931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447931 prefixEnd_7447931 := by exact prefixLift 7447931
  have htrace : WordTrace (prefixWord ++ tailWord_7447931) baseStart_7447931 baseEnd_7447931 := by
    simpa [prefixWord, tailWord_7447931, baseEnd_7447931] using wordTrace_append hprefix tailTrace_7447931
  have hstable : (prefixWord ++ tailWord_7447931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447931).length < 2 ^ (prefixWord ++ tailWord_7447931).sum := by decide
  have hdescent : baseEnd_7447931 < baseStart_7447931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447957 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_7447957 : Nat := 118140960795 + 7447957 * 2 ^ 59
def prefixEnd_7447957 : Nat := 4983230072969 + 3 ^ 40 * 7447957 * 2
def baseEnd_7447957 : Nat := 3824381835018821567684975

theorem tailTrace_7447957 : CollatzResearch.WordTrace tailWord_7447957 prefixEnd_7447957 3824381835018821567684975 := by
  unfold tailWord_7447957
  simp only [CollatzResearch.WordTrace]
  refine ⟨271649308678331273630838125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181099539118887515753892083 271649308678331273630838125)
  ·
    refine ⟨101868490754374227611564297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271649308678331273630838125 101868490754374227611564297)
    ·
      refine ⟨76401368065780670708673223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101868490754374227611564297 76401368065780670708673223)
      ·
        refine ⟨114602052098671006063009835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76401368065780670708673223 114602052098671006063009835)
        ·
          refine ⟨171903078148006509094514753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114602052098671006063009835 171903078148006509094514753)
          ·
            refine ⟨128927308611004881820886065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171903078148006509094514753 128927308611004881820886065)
            ·
              refine ⟨96695481458253661365664549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128927308611004881820886065 96695481458253661365664549)
              ·
                refine ⟨18130402773422561506062103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96695481458253661365664549 18130402773422561506062103)
                ·
                  refine ⟨27195604160133842259093155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18130402773422561506062103 27195604160133842259093155)
                  ·
                    refine ⟨40793406240200763388639733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27195604160133842259093155 40793406240200763388639733)
                    ·
                      refine ⟨3824381835018821567684975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40793406240200763388639733 3824381835018821567684975)
                      ·
                        rfl

theorem cell23_7447957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_7447957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447957 prefixEnd_7447957 := by exact prefixLift 7447957
  have htrace : WordTrace (prefixWord ++ tailWord_7447957) baseStart_7447957 baseEnd_7447957 := by
    simpa [prefixWord, tailWord_7447957, baseEnd_7447957] using wordTrace_append hprefix tailTrace_7447957
  have hstable : (prefixWord ++ tailWord_7447957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447957).length < 2 ^ (prefixWord ++ tailWord_7447957).sum := by decide
  have hdescent : baseEnd_7447957 < baseStart_7447957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7447971 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 3, 2, 2]
def baseStart_7447971 : Nat := 118140960795 + 7447971 * 2 ^ 59
def prefixEnd_7447971 : Nat := 4983230072969 + 3 ^ 40 * 7447971 * 2
def baseEnd_7447971 : Nat := 3824389023747984512909911

theorem tailTrace_7447971 : CollatzResearch.WordTrace tailWord_7447971 prefixEnd_7447971 3824389023747984512909911 := by
  unfold tailWord_7447971
  simp only [CollatzResearch.WordTrace]
  refine ⟨271649819300280554021847767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181099879533520369347898511 271649819300280554021847767)
  ·
    refine ⟨407474728950420831032771651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271649819300280554021847767 407474728950420831032771651)
    ·
      refine ⟨611212093425631246549157477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407474728950420831032771651 611212093425631246549157477)
      ·
        refine ⟨114602267517305858727967027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 611212093425631246549157477 114602267517305858727967027)
        ·
          refine ⟨171903401275958788091950541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114602267517305858727967027 171903401275958788091950541)
          ·
            refine ⟨64463775478484545534481453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171903401275958788091950541 64463775478484545534481453)
            ·
              refine ⟨24173915804431704575430545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64463775478484545534481453 24173915804431704575430545)
              ·
                refine ⟨18130436853323778431572909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24173915804431704575430545 18130436853323778431572909)
                ·
                  refine ⟨6798913819996416911839841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18130436853323778431572909 6798913819996416911839841)
                  ·
                    refine ⟨5099185364997312683879881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6798913819996416911839841 5099185364997312683879881)
                    ·
                      refine ⟨3824389023747984512909911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5099185364997312683879881 3824389023747984512909911)
                      ·
                        rfl

theorem cell23_7447971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_7447971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7447971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7447971 prefixEnd_7447971 := by exact prefixLift 7447971
  have htrace : WordTrace (prefixWord ++ tailWord_7447971) baseStart_7447971 baseEnd_7447971 := by
    simpa [prefixWord, tailWord_7447971, baseEnd_7447971] using wordTrace_append hprefix tailTrace_7447971
  have hstable : (prefixWord ++ tailWord_7447971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7447971).length < 2 ^ (prefixWord ++ tailWord_7447971).sum := by decide
  have hdescent : baseEnd_7447971 < baseStart_7447971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7447971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448047 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 5]
def baseStart_7448047 : Nat := 118140960795 + 7448047 * 2 ^ 59
def prefixEnd_7448047 : Nat := 4983230072969 + 3 ^ 40 * 7448047 * 2
def baseEnd_7448047 : Nat := 3824428048277726215559561

theorem tailTrace_7448047 : CollatzResearch.WordTrace tailWord_7448047 prefixEnd_7448047 3824428048277726215559561 := by
  unfold tailWord_7448047
  simp only [CollatzResearch.WordTrace]
  refine ⟨271652591248005219001614395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181101727498670146001076263 271652591248005219001614395)
  ·
    refine ⟨407478886872007828502421593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271652591248005219001614395 407478886872007828502421593)
    ·
      refine ⟨305609165154005871376816195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407478886872007828502421593 305609165154005871376816195)
      ·
        refine ⟨458413747731008807065224293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305609165154005871376816195 458413747731008807065224293)
        ·
          refine ⟨85952577699564151324729555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 458413747731008807065224293 85952577699564151324729555)
          ·
            refine ⟨128928866549346226987094333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85952577699564151324729555 128928866549346226987094333)
            ·
              refine ⟨48348324956004835120160375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128928866549346226987094333 48348324956004835120160375)
              ·
                refine ⟨72522487434007252680240563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48348324956004835120160375 72522487434007252680240563)
                ·
                  refine ⟨108783731151010879020360845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72522487434007252680240563 108783731151010879020360845)
                  ·
                    refine ⟨40793899181629079632635317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108783731151010879020360845 40793899181629079632635317)
                    ·
                      refine ⟨3824428048277726215559561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40793899181629079632635317 3824428048277726215559561)
                      ·
                        rfl

theorem cell23_7448047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_7448047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448047 prefixEnd_7448047 := by exact prefixLift 7448047
  have htrace : WordTrace (prefixWord ++ tailWord_7448047) baseStart_7448047 baseEnd_7448047 := by
    simpa [prefixWord, tailWord_7448047, baseEnd_7448047] using wordTrace_append hprefix tailTrace_7448047
  have hstable : (prefixWord ++ tailWord_7448047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448047).length < 2 ^ (prefixWord ++ tailWord_7448047).sum := by decide
  have hdescent : baseEnd_7448047 < baseStart_7448047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448067 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 7]
def baseStart_7448067 : Nat := 118140960795 + 7448067 * 2 ^ 59
def prefixEnd_7448067 : Nat := 4983230072969 + 3 ^ 40 * 7448067 * 2
def baseEnd_7448067 : Nat := 424937590876757348589941

theorem tailTrace_7448067 : CollatzResearch.WordTrace tailWord_7448067 prefixEnd_7448067 424937590876757348589941 := by
  unfold tailWord_7448067
  simp only [CollatzResearch.WordTrace]
  refine ⟨271653320707932762417342455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181102213805288508278228303 271653320707932762417342455)
  ·
    refine ⟨407479981061899143626013683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271653320707932762417342455 407479981061899143626013683)
    ·
      refine ⟨611219971592848715439020525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407479981061899143626013683 611219971592848715439020525)
      ·
        refine ⟨229207489347318268289632697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 611219971592848715439020525 229207489347318268289632697)
        ·
          refine ⟨171905617010488701217224523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229207489347318268289632697 171905617010488701217224523)
          ·
            refine ⟨257858425515733051825836785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171905617010488701217224523 257858425515733051825836785)
            ·
              refine ⟨193393819136799788869377589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257858425515733051825836785 193393819136799788869377589)
              ·
                refine ⟨18130670544074980206504149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193393819136799788869377589 18130670544074980206504149)
                ·
                  refine ⟨424937590876757348589941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18130670544074980206504149 424937590876757348589941)
                  ·
                    rfl

theorem cell23_7448067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 7].length) (baseStart_7448067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448067 prefixEnd_7448067 := by exact prefixLift 7448067
  have htrace : WordTrace (prefixWord ++ tailWord_7448067) baseStart_7448067 baseEnd_7448067 := by
    simpa [prefixWord, tailWord_7448067, baseEnd_7448067] using wordTrace_append hprefix tailTrace_7448067
  have hstable : (prefixWord ++ tailWord_7448067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448067).length < 2 ^ (prefixWord ++ tailWord_7448067).sum := by decide
  have hdescent : baseEnd_7448067 < baseStart_7448067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448121 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 2, 5, 2]
def baseStart_7448121 : Nat := 118140960795 + 7448121 * 2 ^ 59
def prefixEnd_7448121 : Nat := 4983230072969 + 3 ^ 40 * 7448121 * 2
def baseEnd_7448121 : Nat := 3824466045846158926034221

theorem tailTrace_7448121 : CollatzResearch.WordTrace tailWord_7448121 prefixEnd_7448121 3824466045846158926034221 := by
  unfold tailWord_7448121
  simp only [CollatzResearch.WordTrace]
  refine ⟨271655290249737129639808217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181103526833158086426538811 271655290249737129639808217)
  ·
    refine ⟨203741467687302847229856163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271655290249737129639808217 203741467687302847229856163)
    ·
      refine ⟨305612201530954270844784245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203741467687302847229856163 305612201530954270844784245)
      ·
        refine ⟨28651143893526962891698523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 305612201530954270844784245 28651143893526962891698523)
        ·
          refine ⟨42976715840290444337547785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28651143893526962891698523 42976715840290444337547785)
          ·
            refine ⟨32232536880217833253160839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42976715840290444337547785 32232536880217833253160839)
            ·
              refine ⟨48348805320326749879741259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32232536880217833253160839 48348805320326749879741259)
              ·
                refine ⟨72523207980490124819611889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48348805320326749879741259 72523207980490124819611889)
                ·
                  refine ⟨54392405985367593614708917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72523207980490124819611889 54392405985367593614708917)
                  ·
                    refine ⟨5099288061128211901378961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54392405985367593614708917 5099288061128211901378961)
                    ·
                      refine ⟨3824466045846158926034221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5099288061128211901378961 3824466045846158926034221)
                      ·
                        rfl

theorem cell23_7448121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_7448121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448121 prefixEnd_7448121 := by exact prefixLift 7448121
  have htrace : WordTrace (prefixWord ++ tailWord_7448121) baseStart_7448121 baseEnd_7448121 := by
    simpa [prefixWord, tailWord_7448121, baseEnd_7448121] using wordTrace_append hprefix tailTrace_7448121
  have hstable : (prefixWord ++ tailWord_7448121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448121).length < 2 ^ (prefixWord ++ tailWord_7448121).sum := by decide
  have hdescent : baseEnd_7448121 < baseStart_7448121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448151 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 4]
def baseStart_7448151 : Nat := 118140960795 + 7448151 * 2 ^ 59
def prefixEnd_7448151 : Nat := 4983230072969 + 3 ^ 40 * 7448151 * 2
def baseEnd_7448151 : Nat := 3824481450265793808659083

theorem tailTrace_7448151 : CollatzResearch.WordTrace tailWord_7448151 prefixEnd_7448151 3824481450265793808659083 := by
  unfold tailWord_7448151
  simp only [CollatzResearch.WordTrace]
  refine ⟨271656384439628444763400307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181104256293085629842266871 271656384439628444763400307)
  ·
    refine ⟨407484576659442667145100461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271656384439628444763400307 407484576659442667145100461)
    ·
      refine ⟨152806716247291000179412673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407484576659442667145100461 152806716247291000179412673)
      ·
        refine ⟨114605037185468250134559505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152806716247291000179412673 114605037185468250134559505)
        ·
          refine ⟨85953777889101187600919629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114605037185468250134559505 85953777889101187600919629)
          ·
            refine ⟨32232666708412945350344861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85953777889101187600919629 32232666708412945350344861)
            ·
              refine ⟨12087250015654854506379323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32232666708412945350344861 12087250015654854506379323)
              ·
                refine ⟨18130875023482281759568985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12087250015654854506379323 18130875023482281759568985)
                ·
                  refine ⟨13598156267611711319676739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18130875023482281759568985 13598156267611711319676739)
                  ·
                    refine ⟨20397234401417566979515109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13598156267611711319676739 20397234401417566979515109)
                    ·
                      refine ⟨3824481450265793808659083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20397234401417566979515109 3824481450265793808659083)
                      ·
                        rfl

theorem cell23_7448151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_7448151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448151 prefixEnd_7448151 := by exact prefixLift 7448151
  have htrace : WordTrace (prefixWord ++ tailWord_7448151) baseStart_7448151 baseEnd_7448151 := by
    simpa [prefixWord, tailWord_7448151, baseEnd_7448151] using wordTrace_append hprefix tailTrace_7448151
  have hstable : (prefixWord ++ tailWord_7448151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448151).length < 2 ^ (prefixWord ++ tailWord_7448151).sum := by decide
  have hdescent : baseEnd_7448151 < baseStart_7448151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448164 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_7448164 : Nat := 118140960795 + 7448164 * 2 ^ 59
def prefixEnd_7448164 : Nat := 4983230072969 + 3 ^ 40 * 7448164 * 2
def baseEnd_7448164 : Nat := 3824488125514302257796523

theorem tailTrace_7448164 : CollatzResearch.WordTrace tailWord_7448164 prefixEnd_7448164 3824488125514302257796523 := by
  unfold tailWord_7448164
  simp only [CollatzResearch.WordTrace]
  refine ⟨135828429294290673991811773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181104572392387565322415697 135828429294290673991811773)
  ·
    refine ⟨50935660985359002746929415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135828429294290673991811773 50935660985359002746929415)
    ·
      refine ⟨76403491478038504120394123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50935660985359002746929415 76403491478038504120394123)
      ·
        refine ⟨114605237217057756180591185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76403491478038504120394123 114605237217057756180591185)
        ·
          refine ⟨85953927912793317135443389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114605237217057756180591185 85953927912793317135443389)
          ·
            refine ⟨32232722967297493925791271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85953927912793317135443389 32232722967297493925791271)
            ·
              refine ⟨48349084450946240888686907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32232722967297493925791271 48349084450946240888686907)
              ·
                refine ⟨72523626676419361333030361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48349084450946240888686907 72523626676419361333030361)
                ·
                  refine ⟨54392720007314520999772771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72523626676419361333030361 54392720007314520999772771)
                  ·
                    refine ⟨81589080010971781499659157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54392720007314520999772771 81589080010971781499659157)
                    ·
                      refine ⟨3824488125514302257796523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81589080010971781499659157 3824488125514302257796523)
                      ·
                        rfl

theorem cell23_7448164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_7448164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448164 prefixEnd_7448164 := by exact prefixLift 7448164
  have htrace : WordTrace (prefixWord ++ tailWord_7448164) baseStart_7448164 baseEnd_7448164 := by
    simpa [prefixWord, tailWord_7448164, baseEnd_7448164] using wordTrace_append hprefix tailTrace_7448164
  have hstable : (prefixWord ++ tailWord_7448164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448164).length < 2 ^ (prefixWord ++ tailWord_7448164).sum := by decide
  have hdescent : baseEnd_7448164 < baseStart_7448164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448168 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 2, 4, 2]
def baseStart_7448168 : Nat := 118140960795 + 7448168 * 2 ^ 59
def prefixEnd_7448168 : Nat := 4983230072969 + 3 ^ 40 * 7448168 * 2
def baseEnd_7448168 : Nat := 3824490179436920242146505

theorem tailTrace_7448168 : CollatzResearch.WordTrace tailWord_7448168 prefixEnd_7448168 3824490179436920242146505 := by
  unfold tailWord_7448168
  simp only [CollatzResearch.WordTrace]
  refine ⟨135828502240283428333384579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181104669653711237777846105 135828502240283428333384579)
  ·
    refine ⟨203742753360425142500076869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135828502240283428333384579 203742753360425142500076869)
    ·
      refine ⟨38201766255079714218764413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203742753360425142500076869 38201766255079714218764413)
      ·
        refine ⟨14325662345654892832036655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38201766255079714218764413 14325662345654892832036655)
        ·
          refine ⟨21488493518482339248054983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14325662345654892832036655 21488493518482339248054983)
          ·
            refine ⟨32232740277723508872082475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21488493518482339248054983 32232740277723508872082475)
            ·
              refine ⟨48349110416585263308123713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32232740277723508872082475 48349110416585263308123713)
              ·
                refine ⟨36261832812438947481092785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48349110416585263308123713 36261832812438947481092785)
                ·
                  refine ⟨27196374609329210610819589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36261832812438947481092785 27196374609329210610819589)
                  ·
                    refine ⟨5099320239249226989528673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27196374609329210610819589 5099320239249226989528673)
                    ·
                      refine ⟨3824490179436920242146505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5099320239249226989528673 3824490179436920242146505)
                      ·
                        rfl

theorem cell23_7448168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_7448168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448168 prefixEnd_7448168 := by exact prefixLift 7448168
  have htrace : WordTrace (prefixWord ++ tailWord_7448168) baseStart_7448168 baseEnd_7448168 := by
    simpa [prefixWord, tailWord_7448168, baseEnd_7448168] using wordTrace_append hprefix tailTrace_7448168
  have hstable : (prefixWord ++ tailWord_7448168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448168).length < 2 ^ (prefixWord ++ tailWord_7448168).sum := by decide
  have hdescent : baseEnd_7448168 < baseStart_7448168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448178 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 3, 4]
def baseStart_7448178 : Nat := 118140960795 + 7448178 * 2 ^ 59
def prefixEnd_7448178 : Nat := 4983230072969 + 3 ^ 40 * 7448178 * 2
def baseEnd_7448178 : Nat := 1274831771414488401007153

theorem tailTrace_7448178 : CollatzResearch.WordTrace tailWord_7448178 prefixEnd_7448178 1274831771414488401007153 := by
  unfold tailWord_7448178
  simp only [CollatzResearch.WordTrace]
  refine ⟨67914342302632657093658297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181104912807020418916422125 67914342302632657093658297)
  ·
    refine ⟨50935756726974492820243723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67914342302632657093658297 50935756726974492820243723)
    ·
      refine ⟨76403635090461739230365585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50935756726974492820243723 76403635090461739230365585)
      ·
        refine ⟨57302726317846304422774189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76403635090461739230365585 57302726317846304422774189)
        ·
          refine ⟨21488522369192364158540321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57302726317846304422774189 21488522369192364158540321)
          ·
            refine ⟨16116391776894273118905241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21488522369192364158540321 16116391776894273118905241)
            ·
              refine ⟨12087293832670704839178931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16116391776894273118905241 12087293832670704839178931)
              ·
                refine ⟨18130940749006057258768397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12087293832670704839178931 18130940749006057258768397)
                ·
                  refine ⟨6799102780877271472038149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18130940749006057258768397 6799102780877271472038149)
                  ·
                    refine ⟨1274831771414488401007153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6799102780877271472038149 1274831771414488401007153)
                    ·
                      rfl

theorem cell23_7448178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_7448178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448178 prefixEnd_7448178 := by exact prefixLift 7448178
  have htrace : WordTrace (prefixWord ++ tailWord_7448178) baseStart_7448178 baseEnd_7448178 := by
    simpa [prefixWord, tailWord_7448178, baseEnd_7448178] using wordTrace_append hprefix tailTrace_7448178
  have hstable : (prefixWord ++ tailWord_7448178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448178).length < 2 ^ (prefixWord ++ tailWord_7448178).sum := by decide
  have hdescent : baseEnd_7448178 < baseStart_7448178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448184 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 4, 5, 3]
def baseStart_7448184 : Nat := 118140960795 + 7448184 * 2 ^ 59
def prefixEnd_7448184 : Nat := 4983230072969 + 3 ^ 40 * 7448184 * 2
def baseEnd_7448184 : Nat := 3824498395127392179546431

theorem tailTrace_7448184 : CollatzResearch.WordTrace tailWord_7448184 prefixEnd_7448184 3824498395127392179546431 := by
  unfold tailWord_7448184
  simp only [CollatzResearch.WordTrace]
  refine ⟨135828794024254445699675803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181105058699005927599567737 135828794024254445699675803)
  ·
    refine ⟨203743191036381668549513705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135828794024254445699675803 203743191036381668549513705)
    ·
      refine ⟨152807393277286251412135279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203743191036381668549513705 152807393277286251412135279)
      ·
        refine ⟨229211089915929377118202919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152807393277286251412135279 229211089915929377118202919)
        ·
          refine ⟨343816634873894065677304379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229211089915929377118202919 343816634873894065677304379)
          ·
            refine ⟨515724952310841098515956569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343816634873894065677304379 515724952310841098515956569)
            ·
              refine ⟨386793714233130823886967427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515724952310841098515956569 386793714233130823886967427)
              ·
                refine ⟨580190571349696235830451141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386793714233130823886967427 580190571349696235830451141)
                ·
                  refine ⟨108785732128068044218209589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 580190571349696235830451141 108785732128068044218209589)
                  ·
                    refine ⟨10198662387006379145457149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108785732128068044218209589 10198662387006379145457149)
                    ·
                      refine ⟨3824498395127392179546431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10198662387006379145457149 3824498395127392179546431)
                      ·
                        rfl

theorem cell23_7448184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_7448184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448184 prefixEnd_7448184 := by exact prefixLift 7448184
  have htrace : WordTrace (prefixWord ++ tailWord_7448184) baseStart_7448184 baseEnd_7448184 := by
    simpa [prefixWord, tailWord_7448184, baseEnd_7448184] using wordTrace_append hprefix tailTrace_7448184
  have hstable : (prefixWord ++ tailWord_7448184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448184).length < 2 ^ (prefixWord ++ tailWord_7448184).sum := by decide
  have hdescent : baseEnd_7448184 < baseStart_7448184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448228 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 4, 3, 2]
def baseStart_7448228 : Nat := 118140960795 + 7448228 * 2 ^ 59
def prefixEnd_7448228 : Nat := 4983230072969 + 3 ^ 40 * 7448228 * 2
def baseEnd_7448228 : Nat := 3824520988276190007396229

theorem tailTrace_7448228 : CollatzResearch.WordTrace tailWord_7448228 prefixEnd_7448228 3824520988276190007396229 := by
  unfold tailWord_7448228
  simp only [CollatzResearch.WordTrace]
  refine ⟨135829596430174743456976669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181106128573566324609302225 135829596430174743456976669)
  ·
    refine ⟨50936098661315528796366251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135829596430174743456976669 50936098661315528796366251)
    ·
      refine ⟨76404147991973293194549377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50936098661315528796366251 76404147991973293194549377)
      ·
        refine ⟨57303110993979969895912033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76404147991973293194549377 57303110993979969895912033)
        ·
          refine ⟨42977333245484977421934025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57303110993979969895912033 42977333245484977421934025)
          ·
            refine ⟨32232999934113733066450519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42977333245484977421934025 32232999934113733066450519)
            ·
              refine ⟨48349499901170599599675779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32232999934113733066450519 48349499901170599599675779)
              ·
                refine ⟨72524249851755899399513669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48349499901170599599675779 72524249851755899399513669)
                ·
                  refine ⟨13598296847204231137408813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72524249851755899399513669 13598296847204231137408813)
                  ·
                    refine ⟨5099361317701586676528305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13598296847204231137408813 5099361317701586676528305)
                    ·
                      refine ⟨3824520988276190007396229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5099361317701586676528305 3824520988276190007396229)
                      ·
                        rfl

theorem cell23_7448228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_7448228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448228 prefixEnd_7448228 := by exact prefixLift 7448228
  have htrace : WordTrace (prefixWord ++ tailWord_7448228) baseStart_7448228 baseEnd_7448228 := by
    simpa [prefixWord, tailWord_7448228, baseEnd_7448228] using wordTrace_append hprefix tailTrace_7448228
  have hstable : (prefixWord ++ tailWord_7448228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448228).length < 2 ^ (prefixWord ++ tailWord_7448228).sum := by decide
  have hdescent : baseEnd_7448228 < baseStart_7448228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448261 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 3, 2, 3]
def baseStart_7448261 : Nat := 118140960795 + 7448261 * 2 ^ 59
def prefixEnd_7448261 : Nat := 4983230072969 + 3 ^ 40 * 7448261 * 2
def baseEnd_7448261 : Nat := 3824537933137788378283577

theorem tailTrace_7448261 : CollatzResearch.WordTrace tailWord_7448261 prefixEnd_7448261 3824537933137788378283577 := by
  unfold tailWord_7448261
  simp only [CollatzResearch.WordTrace]
  refine ⟨271660396469229933549904637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181106930979486622366603091 271660396469229933549904637)
  ·
    refine ⟨101872648675961225081214239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271660396469229933549904637 101872648675961225081214239)
    ·
      refine ⟨152808973013941837621821359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101872648675961225081214239 152808973013941837621821359)
      ·
        refine ⟨229213459520912756432732039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152808973013941837621821359 229213459520912756432732039)
        ·
          refine ⟨343820189281369134649098059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229213459520912756432732039 343820189281369134649098059)
          ·
            refine ⟨515730283922053701973647089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343820189281369134649098059 515730283922053701973647089)
            ·
              refine ⟨386797712941540276480235317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515730283922053701973647089 386797712941540276480235317)
              ·
                refine ⟨36262285588269400920022061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 386797712941540276480235317 36262285588269400920022061)
                ·
                  refine ⟨13598357095601025345008273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36262285588269400920022061 13598357095601025345008273)
                  ·
                    refine ⟨10198767821700769008756205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13598357095601025345008273 10198767821700769008756205)
                    ·
                      refine ⟨3824537933137788378283577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10198767821700769008756205 3824537933137788378283577)
                      ·
                        rfl

theorem cell23_7448261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_7448261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448261 prefixEnd_7448261 := by exact prefixLift 7448261
  have htrace : WordTrace (prefixWord ++ tailWord_7448261) baseStart_7448261 baseEnd_7448261 := by
    simpa [prefixWord, tailWord_7448261, baseEnd_7448261] using wordTrace_append hprefix tailTrace_7448261
  have hstable : (prefixWord ++ tailWord_7448261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448261).length < 2 ^ (prefixWord ++ tailWord_7448261).sum := by decide
  have hdescent : baseEnd_7448261 < baseStart_7448261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448264 : List Nat := [2, 1, 3, 1, 2, 2, 1, 11]
def baseStart_7448264 : Nat := 118140960795 + 7448264 * 2 ^ 59
def prefixEnd_7448264 : Nat := 4983230072969 + 3 ^ 40 * 7448264 * 2
def baseEnd_7448264 : Nat := 141649610132583402464669

theorem tailTrace_7448264 : CollatzResearch.WordTrace tailWord_7448264 prefixEnd_7448264 141649610132583402464669 := by
  unfold tailWord_7448264
  simp only [CollatzResearch.WordTrace]
  refine ⟨135830252944109532531131923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181107003925479376708175897 135830252944109532531131923)
  ·
    refine ⟨203745379416164298796697885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135830252944109532531131923 203745379416164298796697885)
    ·
      refine ⟨76404517281061612048761707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203745379416164298796697885 76404517281061612048761707)
      ·
        refine ⟨114606775921592418073142561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76404517281061612048761707 114606775921592418073142561)
        ·
          refine ⟨85955081941194313554856921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114606775921592418073142561 85955081941194313554856921)
          ·
            refine ⟨64466311455895735166142691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85955081941194313554856921 64466311455895735166142691)
            ·
              refine ⟨96699467183843602749214037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64466311455895735166142691 96699467183843602749214037)
              ·
                refine ⟨141649610132583402464669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 96699467183843602749214037 141649610132583402464669)
                ·
                  rfl

theorem cell23_7448264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 11].length) (baseStart_7448264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448264 prefixEnd_7448264 := by exact prefixLift 7448264
  have htrace : WordTrace (prefixWord ++ tailWord_7448264) baseStart_7448264 baseEnd_7448264 := by
    simpa [prefixWord, tailWord_7448264, baseEnd_7448264] using wordTrace_append hprefix tailTrace_7448264
  have hstable : (prefixWord ++ tailWord_7448264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448264).length < 2 ^ (prefixWord ++ tailWord_7448264).sum := by decide
  have hdescent : baseEnd_7448264 < baseStart_7448264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448268 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 1, 6]
def baseStart_7448268 : Nat := 118140960795 + 7448268 * 2 ^ 59
def prefixEnd_7448268 : Nat := 4983230072969 + 3 ^ 40 * 7448268 * 2
def baseEnd_7448268 : Nat := 1274847175834123283632015

theorem tailTrace_7448268 : CollatzResearch.WordTrace tailWord_7448268 prefixEnd_7448268 1274847175834123283632015 := by
  unfold tailWord_7448268
  simp only [CollatzResearch.WordTrace]
  refine ⟨135830325890102286872704729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181107101186803049163606305 135830325890102286872704729)
  ·
    refine ⟨101872744417576715154528547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135830325890102286872704729 101872744417576715154528547)
    ·
      refine ⟨152809116626365072731792821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101872744417576715154528547 152809116626365072731792821)
      ·
        refine ⟨14325854683721725568605577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152809116626365072731792821 14325854683721725568605577)
        ·
          refine ⟨10744391012791294176454183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14325854683721725568605577 10744391012791294176454183)
          ·
            refine ⟨16116586519186941264681275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10744391012791294176454183 16116586519186941264681275)
            ·
              refine ⟨24174879778780411897021913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16116586519186941264681275 24174879778780411897021913)
              ·
                refine ⟨18131159834085308922766435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24174879778780411897021913 18131159834085308922766435)
                ·
                  refine ⟨27196739751127963384149653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18131159834085308922766435 27196739751127963384149653)
                  ·
                    refine ⟨1274847175834123283632015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27196739751127963384149653 1274847175834123283632015)
                    ·
                      rfl

theorem cell23_7448268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_7448268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448268 prefixEnd_7448268 := by exact prefixLift 7448268
  have htrace : WordTrace (prefixWord ++ tailWord_7448268) baseStart_7448268 baseEnd_7448268 := by
    simpa [prefixWord, tailWord_7448268, baseEnd_7448268] using wordTrace_append hprefix tailTrace_7448268
  have hstable : (prefixWord ++ tailWord_7448268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448268).length < 2 ^ (prefixWord ++ tailWord_7448268).sum := by decide
  have hdescent : baseEnd_7448268 < baseStart_7448268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448292 : List Nat := [2, 3, 1, 1, 1, 3, 3, 4, 1, 2, 2]
def baseStart_7448292 : Nat := 118140960795 + 7448292 * 2 ^ 59
def prefixEnd_7448292 : Nat := 4983230072969 + 3 ^ 40 * 7448292 * 2
def baseEnd_7448292 : Nat := 3824553851038077756995935

theorem tailTrace_7448292 : CollatzResearch.WordTrace tailWord_7448292 prefixEnd_7448292 3824553851038077756995935 := by
  unfold tailWord_7448292
  simp only [CollatzResearch.WordTrace]
  refine ⟨135830763566058812922141565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181107684754745083896188753 135830763566058812922141565)
  ·
    refine ⟨50936536337272054845803087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135830763566058812922141565 50936536337272054845803087)
    ·
      refine ⟨76404804505908082268704631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50936536337272054845803087 76404804505908082268704631)
      ·
        refine ⟨114607206758862123403056947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76404804505908082268704631 114607206758862123403056947)
        ·
          refine ⟨171910810138293185104585421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114607206758862123403056947 171910810138293185104585421)
          ·
            refine ⟨64466553801859944414219533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171910810138293185104585421 64466553801859944414219533)
            ·
              refine ⟨24174957675697479155332325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64466553801859944414219533 24174957675697479155332325)
              ·
                refine ⟨4532804564193277341624811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24174957675697479155332325 4532804564193277341624811)
                ·
                  refine ⟨6799206846289916012437217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4532804564193277341624811 6799206846289916012437217)
                  ·
                    refine ⟨5099405134717437009327913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6799206846289916012437217 5099405134717437009327913)
                    ·
                      refine ⟨3824553851038077756995935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5099405134717437009327913 3824553851038077756995935)
                      ·
                        rfl

theorem cell23_7448292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_7448292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448292 prefixEnd_7448292 := by exact prefixLift 7448292
  have htrace : WordTrace (prefixWord ++ tailWord_7448292) baseStart_7448292 baseEnd_7448292 := by
    simpa [prefixWord, tailWord_7448292, baseEnd_7448292] using wordTrace_append hprefix tailTrace_7448292
  have hstable : (prefixWord ++ tailWord_7448292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448292).length < 2 ^ (prefixWord ++ tailWord_7448292).sum := by decide
  have hdescent : baseEnd_7448292 < baseStart_7448292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448341 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 2, 6]
def baseStart_7448341 : Nat := 118140960795 + 7448341 * 2 ^ 59
def prefixEnd_7448341 : Nat := 4983230072969 + 3 ^ 40 * 7448341 * 2
def baseEnd_7448341 : Nat := 1274859670530049355094403

theorem tailTrace_7448341 : CollatzResearch.WordTrace tailWord_7448341 prefixEnd_7448341 1274859670530049355094403 := by
  unfold tailWord_7448341
  simp only [CollatzResearch.WordTrace]
  refine ⟨271663314308940107212816877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181108876205960071475211251 271663314308940107212816877)
  ·
    refine ⟨101873742865852540204806329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271663314308940107212816877 101873742865852540204806329)
    ·
      refine ⟨76405307149389405153604747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101873742865852540204806329 76405307149389405153604747)
      ·
        refine ⟨114607960724084107730407121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76405307149389405153604747 114607960724084107730407121)
        ·
          refine ⟨85955970543063080797805341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114607960724084107730407121 85955970543063080797805341)
          ·
            refine ⟨32233488953648655299177003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85955970543063080797805341 32233488953648655299177003)
            ·
              refine ⟨48350233430472982948765505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32233488953648655299177003 48350233430472982948765505)
              ·
                refine ⟨36262675072854737211574129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48350233430472982948765505 36262675072854737211574129)
                ·
                  refine ⟨27197006304641052908680597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36262675072854737211574129 27197006304641052908680597)
                  ·
                    refine ⟨1274859670530049355094403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27197006304641052908680597 1274859670530049355094403)
                    ·
                      rfl

theorem cell23_7448341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_7448341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448341 prefixEnd_7448341 := by exact prefixLift 7448341
  have htrace : WordTrace (prefixWord ++ tailWord_7448341) baseStart_7448341 baseEnd_7448341 := by
    simpa [prefixWord, tailWord_7448341, baseEnd_7448341] using wordTrace_append hprefix tailTrace_7448341
  have hstable : (prefixWord ++ tailWord_7448341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448341).length < 2 ^ (prefixWord ++ tailWord_7448341).sum := by decide
  have hdescent : baseEnd_7448341 < baseStart_7448341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448382 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 4, 2, 2]
def baseStart_7448382 : Nat := 118140960795 + 7448382 * 2 ^ 59
def prefixEnd_7448382 : Nat := 4983230072969 + 3 ^ 40 * 7448382 * 2
def baseEnd_7448382 : Nat := 3824600064296982404870521

theorem tailTrace_7448382 : CollatzResearch.WordTrace tailWord_7448382 prefixEnd_7448382 3824600064296982404870521 := by
  unfold tailWord_7448382
  simp only [CollatzResearch.WordTrace]
  refine ⟨33958101212723946401882425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181109873134527714143372933 33958101212723946401882425)
  ·
    refine ⟨25468575909542959801411819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33958101212723946401882425 25468575909542959801411819)
    ·
      refine ⟨38202863864314439702117729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25468575909542959801411819 38202863864314439702117729)
      ·
        refine ⟨28652147898235829776588297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38202863864314439702117729 28652147898235829776588297)
        ·
          refine ⟨21489110923676872332441223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28652147898235829776588297 21489110923676872332441223)
          ·
            refine ⟨32233666385515308498661835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21489110923676872332441223 32233666385515308498661835)
            ·
              refine ⟨48350499578272962747992753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32233666385515308498661835 48350499578272962747992753)
              ·
                refine ⟨36262874683704722060994565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48350499578272962747992753 36262874683704722060994565)
                ·
                  refine ⟨6799289003194635386436481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36262874683704722060994565 6799289003194635386436481)
                  ·
                    refine ⟨5099466752395976539827361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6799289003194635386436481 5099466752395976539827361)
                    ·
                      refine ⟨3824600064296982404870521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5099466752395976539827361 3824600064296982404870521)
                      ·
                        rfl

theorem cell23_7448382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_7448382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448382 prefixEnd_7448382 := by exact prefixLift 7448382
  have htrace : WordTrace (prefixWord ++ tailWord_7448382) baseStart_7448382 baseEnd_7448382 := by
    simpa [prefixWord, tailWord_7448382, baseEnd_7448382] using wordTrace_append hprefix tailTrace_7448382
  have hstable : (prefixWord ++ tailWord_7448382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448382).length < 2 ^ (prefixWord ++ tailWord_7448382).sum := by decide
  have hdescent : baseEnd_7448382 < baseStart_7448382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448482 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_7448482 : Nat := 118140960795 + 7448482 * 2 ^ 59
def prefixEnd_7448482 : Nat := 4983230072969 + 3 ^ 40 * 7448482 * 2
def baseEnd_7448482 : Nat := 1274883804120810671206687

theorem tailTrace_7448482 : CollatzResearch.WordTrace tailWord_7448482 prefixEnd_7448482 1274883804120810671206687 := by
  unfold tailWord_7448482
  simp only [CollatzResearch.WordTrace]
  refine ⟨67917114250357322073424925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181112304667619525529133133 67917114250357322073424925)
  ·
    refine ⟨25468917843883995777534347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67917114250357322073424925 25468917843883995777534347)
    ·
      refine ⟨38203376765825993666301521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25468917843883995777534347 38203376765825993666301521)
      ·
        refine ⟨28652532574369495249726141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38203376765825993666301521 28652532574369495249726141)
        ·
          refine ⟨10744699715388560718647303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28652532574369495249726141 10744699715388560718647303)
          ·
            refine ⟨16117049573082841077970955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10744699715388560718647303 16117049573082841077970955)
            ·
              refine ⟨24175574359624261616956433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16117049573082841077970955 24175574359624261616956433)
              ·
                refine ⟨18131680769718196212717325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24175574359624261616956433 18131680769718196212717325)
                ·
                  refine ⟨6799380288644323579768997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18131680769718196212717325 6799380288644323579768997)
                  ·
                    refine ⟨1274883804120810671206687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6799380288644323579768997 1274883804120810671206687)
                    ·
                      rfl

theorem cell23_7448482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_7448482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448482 prefixEnd_7448482 := by exact prefixLift 7448482
  have htrace : WordTrace (prefixWord ++ tailWord_7448482) baseStart_7448482 baseEnd_7448482 := by
    simpa [prefixWord, tailWord_7448482, baseEnd_7448482] using wordTrace_append hprefix tailTrace_7448482
  have hstable : (prefixWord ++ tailWord_7448482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448482).length < 2 ^ (prefixWord ++ tailWord_7448482).sum := by decide
  have hdescent : baseEnd_7448482 < baseStart_7448482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448505 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 5, 1, 3]
def baseStart_7448505 : Nat := 118140960795 + 7448505 * 2 ^ 59
def prefixEnd_7448505 : Nat := 4983230072969 + 3 ^ 40 * 7448505 * 2
def baseEnd_7448505 : Nat := 3824663222417485423632455

theorem tailTrace_7448505 : CollatzResearch.WordTrace tailWord_7448505 prefixEnd_7448505 3824663222417485423632455 := by
  unfold tailWord_7448505
  simp only [CollatzResearch.WordTrace]
  refine ⟨271669295880345963221786969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181112863920230642147857979 271669295880345963221786969)
  ·
    refine ⟨203751971910259472416340227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271669295880345963221786969 203751971910259472416340227)
    ·
      refine ⟨305627957865389208624510341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203751971910259472416340227 305627957865389208624510341)
      ·
        refine ⟨57305242099760476617095689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305627957865389208624510341 57305242099760476617095689)
        ·
          refine ⟨42978931574820357462821767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57305242099760476617095689 42978931574820357462821767)
          ·
            refine ⟨64468397362230536194232651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42978931574820357462821767 64468397362230536194232651)
            ·
              refine ⟨96702596043345804291348977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64468397362230536194232651 96702596043345804291348977)
              ·
                refine ⟨72526947032509353218511733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96702596043345804291348977 72526947032509353218511733)
                ·
                  refine ⟨6799401284297751864235475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72526947032509353218511733 6799401284297751864235475)
                  ·
                    refine ⟨10199101926446627796353213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6799401284297751864235475 10199101926446627796353213)
                    ·
                      refine ⟨3824663222417485423632455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10199101926446627796353213 3824663222417485423632455)
                      ·
                        rfl

theorem cell23_7448505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_7448505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448505 prefixEnd_7448505 := by exact prefixLift 7448505
  have htrace : WordTrace (prefixWord ++ tailWord_7448505) baseStart_7448505 baseEnd_7448505 := by
    simpa [prefixWord, tailWord_7448505, baseEnd_7448505] using wordTrace_append hprefix tailTrace_7448505
  have hstable : (prefixWord ++ tailWord_7448505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448505).length < 2 ^ (prefixWord ++ tailWord_7448505).sum := by decide
  have hdescent : baseEnd_7448505 < baseStart_7448505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448528 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 4]
def baseStart_7448528 : Nat := 118140960795 + 7448528 * 2 ^ 59
def prefixEnd_7448528 : Nat := 4983230072969 + 3 ^ 40 * 7448528 * 2
def baseEnd_7448528 : Nat := 3824675032472538833644849

theorem tailTrace_7448528 : CollatzResearch.WordTrace tailWord_7448528 prefixEnd_7448528 3824675032472538833644849 := by
  unfold tailWord_7448528
  simp only [CollatzResearch.WordTrace]
  refine ⟨135835067379631319074937119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181113423172841758766582825 135835067379631319074937119)
  ·
    refine ⟨203752601069446978612405679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135835067379631319074937119 203752601069446978612405679)
    ·
      refine ⟨305628901604170467918608519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203752601069446978612405679 305628901604170467918608519)
      ·
        refine ⟨458443352406255701877912779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305628901604170467918608519 458443352406255701877912779)
        ·
          refine ⟨687665028609383552816869169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458443352406255701877912779 687665028609383552816869169)
          ·
            refine ⟨515748771457037664612651877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 687665028609383552816869169 515748771457037664612651877)
            ·
              refine ⟨96702894648194562114872227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 515748771457037664612651877 96702894648194562114872227)
              ·
                refine ⟨145054341972291843172308341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96702894648194562114872227 145054341972291843172308341)
                ·
                  refine ⟨13598844559902360297403907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145054341972291843172308341 13598844559902360297403907)
                  ·
                    refine ⟨20398266839853540446105861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13598844559902360297403907 20398266839853540446105861)
                    ·
                      refine ⟨3824675032472538833644849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20398266839853540446105861 3824675032472538833644849)
                      ·
                        rfl

theorem cell23_7448528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 4].length) (baseStart_7448528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448528 prefixEnd_7448528 := by exact prefixLift 7448528
  have htrace : WordTrace (prefixWord ++ tailWord_7448528) baseStart_7448528 baseEnd_7448528 := by
    simpa [prefixWord, tailWord_7448528, baseEnd_7448528] using wordTrace_append hprefix tailTrace_7448528
  have hstable : (prefixWord ++ tailWord_7448528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448528).length < 2 ^ (prefixWord ++ tailWord_7448528).sum := by decide
  have hdescent : baseEnd_7448528 < baseStart_7448528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448545 : List Nat := [1, 2, 3, 1, 2, 1, 3, 4, 1, 1, 4]
def baseStart_7448545 : Nat := 118140960795 + 7448545 * 2 ^ 59
def prefixEnd_7448545 : Nat := 4983230072969 + 3 ^ 40 * 7448545 * 2
def baseEnd_7448545 : Nat := 3824683761643665267132271

theorem tailTrace_7448545 : CollatzResearch.WordTrace tailWord_7448545 prefixEnd_7448545 3824683761643665267132271 := by
  unfold tailWord_7448545
  simp only [CollatzResearch.WordTrace]
  refine ⟨271670754800201050053243089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181113836533467366702162059 271670754800201050053243089)
  ·
    refine ⟨203753066100150787539932317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271670754800201050053243089 203753066100150787539932317)
    ·
      refine ⟨76407399787556545327474619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203753066100150787539932317 76407399787556545327474619)
      ·
        refine ⟨114611099681334817991211929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76407399787556545327474619 114611099681334817991211929)
        ·
          refine ⟨85958324761001113493408947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114611099681334817991211929 85958324761001113493408947)
          ·
            refine ⟨128937487141501670240113421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85958324761001113493408947 128937487141501670240113421)
            ·
              refine ⟨48351557678063126340042533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128937487141501670240113421 48351557678063126340042533)
              ·
                refine ⟨9065917064636836188757975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48351557678063126340042533 9065917064636836188757975)
                ·
                  refine ⟨13598875596955254283136963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9065917064636836188757975 13598875596955254283136963)
                  ·
                    refine ⟨20398313395432881424705445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13598875596955254283136963 20398313395432881424705445)
                    ·
                      refine ⟨3824683761643665267132271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20398313395432881424705445 3824683761643665267132271)
                      ·
                        rfl

theorem cell23_7448545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_7448545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448545 prefixEnd_7448545 := by exact prefixLift 7448545
  have htrace : WordTrace (prefixWord ++ tailWord_7448545) baseStart_7448545 baseEnd_7448545 := by
    simpa [prefixWord, tailWord_7448545, baseEnd_7448545] using wordTrace_append hprefix tailTrace_7448545
  have hstable : (prefixWord ++ tailWord_7448545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448545).length < 2 ^ (prefixWord ++ tailWord_7448545).sum := by decide
  have hdescent : baseEnd_7448545 < baseStart_7448545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448548 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_7448548 : Nat := 118140960795 + 7448548 * 2 ^ 59
def prefixEnd_7448548 : Nat := 4983230072969 + 3 ^ 40 * 7448548 * 2
def baseEnd_7448548 : Nat := 3824685302085628755394757

theorem tailTrace_7448548 : CollatzResearch.WordTrace tailWord_7448548 prefixEnd_7448548 3824685302085628755394757 := by
  unfold tailWord_7448548
  simp only [CollatzResearch.WordTrace]
  refine ⟨135835432109595090782801149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181113909479460121043734865 135835432109595090782801149)
  ·
    refine ⟨50938287041098159043550431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135835432109595090782801149 50938287041098159043550431)
    ·
      refine ⟨76407430561647238565325647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50938287041098159043550431 76407430561647238565325647)
      ·
        refine ⟨114611145842470857847988471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76407430561647238565325647 114611145842470857847988471)
        ·
          refine ⟨171916718763706286771982707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114611145842470857847988471 171916718763706286771982707)
          ·
            refine ⟨257875078145559430157974061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171916718763706286771982707 257875078145559430157974061)
            ·
              refine ⟨96703154304584786309240273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257875078145559430157974061 96703154304584786309240273)
              ·
                refine ⟨72527365728438589731930205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96703154304584786309240273 72527365728438589731930205)
                ·
                  refine ⟨27197762148164471149473827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72527365728438589731930205 27197762148164471149473827)
                  ·
                    refine ⟨40796643222246706724210741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27197762148164471149473827 40796643222246706724210741)
                    ·
                      refine ⟨3824685302085628755394757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40796643222246706724210741 3824685302085628755394757)
                      ·
                        rfl

theorem cell23_7448548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_7448548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448548 prefixEnd_7448548 := by exact prefixLift 7448548
  have htrace : WordTrace (prefixWord ++ tailWord_7448548) baseStart_7448548 baseEnd_7448548 := by
    simpa [prefixWord, tailWord_7448548, baseEnd_7448548] using wordTrace_append hprefix tailTrace_7448548
  have hstable : (prefixWord ++ tailWord_7448548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448548).length < 2 ^ (prefixWord ++ tailWord_7448548).sum := by decide
  have hdescent : baseEnd_7448548 < baseStart_7448548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448579 : List Nat := [1, 1, 1, 3, 2, 1, 1, 8, 1, 2, 2]
def baseStart_7448579 : Nat := 118140960795 + 7448579 * 2 ^ 59
def prefixEnd_7448579 : Nat := 4983230072969 + 3 ^ 40 * 7448579 * 2
def baseEnd_7448579 : Nat := 3824701219985918134107115

theorem tailTrace_7448579 : CollatzResearch.WordTrace tailWord_7448579 prefixEnd_7448579 3824701219985918134107115 := by
  unfold tailWord_7448579
  simp only [CollatzResearch.WordTrace]
  refine ⟨271671994882077873859980791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181114663254718582573320527 271671994882077873859980791)
  ·
    refine ⟨407507992323116810789971187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271671994882077873859980791 407507992323116810789971187)
    ·
      refine ⟨611261988484675216184956781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407507992323116810789971187 611261988484675216184956781)
      ·
        refine ⟨229223245681753206069358793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 611261988484675216184956781 229223245681753206069358793)
        ·
          refine ⟨171917434261314904552019095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229223245681753206069358793 171917434261314904552019095)
          ·
            refine ⟨257876151391972356828028643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171917434261314904552019095 257876151391972356828028643)
            ·
              refine ⟨386814227087958535242042965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257876151391972356828028643 386814227087958535242042965)
              ·
                refine ⟨4532979223687014084867691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 386814227087958535242042965 4532979223687014084867691)
                ·
                  refine ⟨6799468835530521127301537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4532979223687014084867691 6799468835530521127301537)
                  ·
                    refine ⟨5099601626647890845476153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6799468835530521127301537 5099601626647890845476153)
                    ·
                      refine ⟨3824701219985918134107115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5099601626647890845476153 3824701219985918134107115)
                      ·
                        rfl

theorem cell23_7448579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 1, 2, 2].length) (baseStart_7448579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448579 prefixEnd_7448579 := by exact prefixLift 7448579
  have htrace : WordTrace (prefixWord ++ tailWord_7448579) baseStart_7448579 baseEnd_7448579 := by
    simpa [prefixWord, tailWord_7448579, baseEnd_7448579] using wordTrace_append hprefix tailTrace_7448579
  have hstable : (prefixWord ++ tailWord_7448579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448579).length < 2 ^ (prefixWord ++ tailWord_7448579).sum := by decide
  have hdescent : baseEnd_7448579 < baseStart_7448579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448588 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 2, 2, 6]
def baseStart_7448588 : Nat := 118140960795 + 7448588 * 2 ^ 59
def prefixEnd_7448588 : Nat := 4983230072969 + 3 ^ 40 * 7448588 * 2
def baseEnd_7448588 : Nat := 3824705841311808598894573

theorem tailTrace_7448588 : CollatzResearch.WordTrace tailWord_7448588 prefixEnd_7448588 3824705841311808598894573 := by
  unfold tailWord_7448588
  simp only [CollatzResearch.WordTrace]
  refine ⟨135836161569522634198529209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181114882092696845598038945 135836161569522634198529209)
  ·
    refine ⟨101877121177141975648896907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135836161569522634198529209 101877121177141975648896907)
    ·
      refine ⟨152815681765712963473345361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101877121177141975648896907 152815681765712963473345361)
      ·
        refine ⟨114611761324284722605009021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152815681765712963473345361 114611761324284722605009021)
        ·
          refine ⟨42979410496606770976878383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114611761324284722605009021 42979410496606770976878383)
          ·
            refine ⟨64469115744910156465317575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42979410496606770976878383 64469115744910156465317575)
            ·
              refine ⟨96703673617365234697976363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64469115744910156465317575 96703673617365234697976363)
              ·
                refine ⟨145055510426047852046964545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96703673617365234697976363 145055510426047852046964545)
                ·
                  refine ⟨108791632819535889035223409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145055510426047852046964545 108791632819535889035223409)
                  ·
                    refine ⟨81593724614651916776417557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108791632819535889035223409 81593724614651916776417557)
                    ·
                      refine ⟨3824705841311808598894573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81593724614651916776417557 3824705841311808598894573)
                      ·
                        rfl

theorem cell23_7448588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_7448588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448588 prefixEnd_7448588 := by exact prefixLift 7448588
  have htrace : WordTrace (prefixWord ++ tailWord_7448588) baseStart_7448588 baseEnd_7448588 := by
    simpa [prefixWord, tailWord_7448588, baseEnd_7448588] using wordTrace_append hprefix tailTrace_7448588
  have hstable : (prefixWord ++ tailWord_7448588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448588).length < 2 ^ (prefixWord ++ tailWord_7448588).sum := by decide
  have hdescent : baseEnd_7448588 < baseStart_7448588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448616 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_7448616 : Nat := 118140960795 + 7448616 * 2 ^ 59
def prefixEnd_7448616 : Nat := 4983230072969 + 3 ^ 40 * 7448616 * 2
def baseEnd_7448616 : Nat := 3824720218770134489344445

theorem tailTrace_7448616 : CollatzResearch.WordTrace tailWord_7448616 prefixEnd_7448616 3824720218770134489344445 := by
  unfold tailWord_7448616
  simp only [CollatzResearch.WordTrace]
  refine ⟨135836672191471914589538851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181115562921962552786051801 135836672191471914589538851)
  ·
    refine ⟨203755008287207871884308277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135836672191471914589538851 203755008287207871884308277)
    ·
      refine ⟨19102032026925737989153901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203755008287207871884308277 19102032026925737989153901)
      ·
        refine ⟨7163262010097151745932713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19102032026925737989153901 7163262010097151745932713)
        ·
          refine ⟨5372446507572863809449535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7163262010097151745932713 5372446507572863809449535)
          ·
            refine ⟨8058669761359295714174303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5372446507572863809449535 8058669761359295714174303)
            ·
              refine ⟨12088004642038943571261455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8058669761359295714174303 12088004642038943571261455)
              ·
                refine ⟨18132006963058415356892183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12088004642038943571261455 18132006963058415356892183)
                ·
                  refine ⟨27198010444587623035338275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18132006963058415356892183 27198010444587623035338275)
                  ·
                    refine ⟨40797015666881434553007413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27198010444587623035338275 40797015666881434553007413)
                    ·
                      refine ⟨3824720218770134489344445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40797015666881434553007413 3824720218770134489344445)
                      ·
                        rfl

theorem cell23_7448616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_7448616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448616 prefixEnd_7448616 := by exact prefixLift 7448616
  have htrace : WordTrace (prefixWord ++ tailWord_7448616) baseStart_7448616 baseEnd_7448616 := by
    simpa [prefixWord, tailWord_7448616, baseEnd_7448616] using wordTrace_append hprefix tailTrace_7448616
  have hstable : (prefixWord ++ tailWord_7448616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448616).length < 2 ^ (prefixWord ++ tailWord_7448616).sum := by decide
  have hdescent : baseEnd_7448616 < baseStart_7448616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448646 : List Nat := [6, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_7448646 : Nat := 118140960795 + 7448646 * 2 ^ 59
def prefixEnd_7448646 : Nat := 4983230072969 + 3 ^ 40 * 7448646 * 2
def baseEnd_7448646 : Nat := 3824735623189769371969307

theorem tailTrace_7448646 : CollatzResearch.WordTrace tailWord_7448646 prefixEnd_7448646 3824735623189769371969307 := by
  unfold tailWord_7448646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8489826205401098259458431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181116292381890096201779861 8489826205401098259458431)
  ·
    refine ⟨12734739308101647389187647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8489826205401098259458431 12734739308101647389187647)
    ·
      refine ⟨19102108962152471083781471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12734739308101647389187647 19102108962152471083781471)
      ·
        refine ⟨28653163443228706625672207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19102108962152471083781471 28653163443228706625672207)
        ·
          refine ⟨42979745164843059938508311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28653163443228706625672207 42979745164843059938508311)
          ·
            refine ⟨64469617747264589907762467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42979745164843059938508311 64469617747264589907762467)
            ·
              refine ⟨96704426620896884861643701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64469617747264589907762467 96704426620896884861643701)
              ·
                refine ⟨9066039995709082955779097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96704426620896884861643701 9066039995709082955779097)
                ·
                  refine ⟨6799529996781812216834323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9066039995709082955779097 6799529996781812216834323)
                  ·
                    refine ⟨10199294995172718325251485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6799529996781812216834323 10199294995172718325251485)
                    ·
                      refine ⟨3824735623189769371969307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10199294995172718325251485 3824735623189769371969307)
                      ·
                        rfl

theorem cell23_7448646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_7448646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448646 prefixEnd_7448646 := by exact prefixLift 7448646
  have htrace : WordTrace (prefixWord ++ tailWord_7448646) baseStart_7448646 baseEnd_7448646 := by
    simpa [prefixWord, tailWord_7448646, baseEnd_7448646] using wordTrace_append hprefix tailTrace_7448646
  have hstable : (prefixWord ++ tailWord_7448646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448646).length < 2 ^ (prefixWord ++ tailWord_7448646).sum := by decide
  have hdescent : baseEnd_7448646 < baseStart_7448646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448652 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 1, 4, 2]
def baseStart_7448652 : Nat := 118140960795 + 7448652 * 2 ^ 59
def prefixEnd_7448652 : Nat := 4983230072969 + 3 ^ 40 * 7448652 * 2
def baseEnd_7448652 : Nat := 3824738704073696348494279

theorem tailTrace_7448652 : CollatzResearch.WordTrace tailWord_7448652 prefixEnd_7448652 3824738704073696348494279 := by
  unfold tailWord_7448652
  simp only [CollatzResearch.WordTrace]
  refine ⟨135837328705406703663694105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181116438273875604884925473 135837328705406703663694105)
  ·
    refine ⟨101877996529055027747770579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135837328705406703663694105 101877996529055027747770579)
    ·
      refine ⟨152816994793582541621655869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101877996529055027747770579 152816994793582541621655869)
      ·
        refine ⟨57306373047593453108120951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152816994793582541621655869 57306373047593453108120951)
        ·
          refine ⟨85959559571390179662181427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57306373047593453108120951 85959559571390179662181427)
          ·
            refine ⟨128939339357085269493272141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85959559571390179662181427 128939339357085269493272141)
            ·
              refine ⟨48352252258906976059977053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128939339357085269493272141 48352252258906976059977053)
              ·
                refine ⟨18132094597090116022491395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48352252258906976059977053 18132094597090116022491395)
                ·
                  refine ⟨27198141895635174033737093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18132094597090116022491395 27198141895635174033737093)
                  ·
                    refine ⟨5099651605431595131325705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27198141895635174033737093 5099651605431595131325705)
                    ·
                      refine ⟨3824738704073696348494279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5099651605431595131325705 3824738704073696348494279)
                      ·
                        rfl

theorem cell23_7448652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_7448652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448652 prefixEnd_7448652 := by exact prefixLift 7448652
  have htrace : WordTrace (prefixWord ++ tailWord_7448652) baseStart_7448652 baseEnd_7448652 := by
    simpa [prefixWord, tailWord_7448652, baseEnd_7448652] using wordTrace_append hprefix tailTrace_7448652
  have hstable : (prefixWord ++ tailWord_7448652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448652).length < 2 ^ (prefixWord ++ tailWord_7448652).sum := by decide
  have hdescent : baseEnd_7448652 < baseStart_7448652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448722 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 2, 5]
def baseStart_7448722 : Nat := 118140960795 + 7448722 * 2 ^ 59
def prefixEnd_7448722 : Nat := 4983230072969 + 3 ^ 40 * 7448722 * 2
def baseEnd_7448722 : Nat := 1274924882573170358206319

theorem tailTrace_7448722 : CollatzResearch.WordTrace tailWord_7448722 prefixEnd_7448722 1274924882573170358206319 := by
  unfold tailWord_7448722
  simp only [CollatzResearch.WordTrace]
  refine ⟨67919302630139952320609105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181118140347039872854957613 67919302630139952320609105)
  ·
    refine ⟨50939476972604964240456829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67919302630139952320609105 50939476972604964240456829)
    ·
      refine ⟨19102303864726861590171311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50939476972604964240456829 19102303864726861590171311)
      ·
        refine ⟨28653455797090292385256967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19102303864726861590171311 28653455797090292385256967)
        ·
          refine ⟨42980183695635438577885451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28653455797090292385256967 42980183695635438577885451)
          ·
            refine ⟨64470275543453157866828177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42980183695635438577885451 64470275543453157866828177)
            ·
              refine ⟨48352706657589868400121133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64470275543453157866828177 48352706657589868400121133)
              ·
                refine ⟨18132264996596200650045425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48352706657589868400121133 18132264996596200650045425)
                ·
                  refine ⟨13599198747447150487534069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18132264996596200650045425 13599198747447150487534069)
                  ·
                    refine ⟨1274924882573170358206319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13599198747447150487534069 1274924882573170358206319)
                    ·
                      rfl

theorem cell23_7448722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_7448722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448722 prefixEnd_7448722 := by exact prefixLift 7448722
  have htrace : WordTrace (prefixWord ++ tailWord_7448722) baseStart_7448722 baseEnd_7448722 := by
    simpa [prefixWord, tailWord_7448722, baseEnd_7448722] using wordTrace_append hprefix tailTrace_7448722
  have hstable : (prefixWord ++ tailWord_7448722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448722).length < 2 ^ (prefixWord ++ tailWord_7448722).sum := by decide
  have hdescent : baseEnd_7448722 < baseStart_7448722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448725 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_7448725 : Nat := 118140960795 + 7448725 * 2 ^ 59
def prefixEnd_7448725 : Nat := 4983230072969 + 3 ^ 40 * 7448725 * 2
def baseEnd_7448725 : Nat := 3824776188161474562881443

theorem tailTrace_7448725 : CollatzResearch.WordTrace tailWord_7448725 prefixEnd_7448725 3824776188161474562881443 := by
  unfold tailWord_7448725
  simp only [CollatzResearch.WordTrace]
  refine ⟨271677319939548940794795629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181118213293032627196530419 271677319939548940794795629)
  ·
    refine ⟨101878994977330852798048361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271677319939548940794795629 101878994977330852798048361)
    ·
      refine ⟨76409246232998139598536271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101878994977330852798048361 76409246232998139598536271)
      ·
        refine ⟨114613869349497209397804407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76409246232998139598536271 114613869349497209397804407)
        ·
          refine ⟨171920804024245814096706611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114613869349497209397804407 171920804024245814096706611)
          ·
            refine ⟨257881206036368721145059917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171920804024245814096706611 257881206036368721145059917)
            ·
              refine ⟨96705452263638270429397469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257881206036368721145059917 96705452263638270429397469)
              ·
                refine ⟨36264544598864351411024051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96705452263638270429397469 36264544598864351411024051)
                ·
                  refine ⟨54396816898296527116536077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36264544598864351411024051 54396816898296527116536077)
                  ·
                    refine ⟨20398806336861197668701029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54396816898296527116536077 20398806336861197668701029)
                    ·
                      refine ⟨3824776188161474562881443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20398806336861197668701029 3824776188161474562881443)
                      ·
                        rfl

theorem cell23_7448725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_7448725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448725 prefixEnd_7448725 := by exact prefixLift 7448725
  have htrace : WordTrace (prefixWord ++ tailWord_7448725) baseStart_7448725 baseEnd_7448725 := by
    simpa [prefixWord, tailWord_7448725, baseEnd_7448725] using wordTrace_append hprefix tailTrace_7448725
  have hstable : (prefixWord ++ tailWord_7448725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448725).length < 2 ^ (prefixWord ++ tailWord_7448725).sum := by decide
  have hdescent : baseEnd_7448725 < baseStart_7448725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448795 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 5, 5]
def baseStart_7448795 : Nat := 118140960795 + 7448795 * 2 ^ 59
def prefixEnd_7448795 : Nat := 4983230072969 + 3 ^ 40 * 7448795 * 2
def baseEnd_7448795 : Nat := 1274937377269096429668707

theorem tailTrace_7448795 : CollatzResearch.WordTrace tailWord_7448795 prefixEnd_7448795 1274937377269096429668707 := by
  unfold tailWord_7448795
  simp only [CollatzResearch.WordTrace]
  refine ⟨271679873049295342749843839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181119915366196895166562559 271679873049295342749843839)
  ·
    refine ⟨407519809573943014124765759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271679873049295342749843839 407519809573943014124765759)
    ·
      refine ⟨611279714360914521187148639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407519809573943014124765759 611279714360914521187148639)
      ·
        refine ⟨916919571541371781780722959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611279714360914521187148639 916919571541371781780722959)
        ·
          refine ⟨1375379357312057672671084439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916919571541371781780722959 1375379357312057672671084439)
          ·
            refine ⟨2063069035968086509006626659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375379357312057672671084439 2063069035968086509006626659)
            ·
              refine ⟨3094603553952129763509939989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2063069035968086509006626659 3094603553952129763509939989)
              ·
                refine ⟨145059541591506082664528437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3094603553952129763509939989 145059541591506082664528437)
                ·
                  refine ⟨13599332024203695249799541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145059541591506082664528437 13599332024203695249799541)
                  ·
                    refine ⟨1274937377269096429668707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13599332024203695249799541 1274937377269096429668707)
                    ·
                      rfl

theorem cell23_7448795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 5].length) (baseStart_7448795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448795 prefixEnd_7448795 := by exact prefixLift 7448795
  have htrace : WordTrace (prefixWord ++ tailWord_7448795) baseStart_7448795 baseEnd_7448795 := by
    simpa [prefixWord, tailWord_7448795, baseEnd_7448795] using wordTrace_append hprefix tailTrace_7448795
  have hstable : (prefixWord ++ tailWord_7448795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448795).length < 2 ^ (prefixWord ++ tailWord_7448795).sum := by decide
  have hdescent : baseEnd_7448795 < baseStart_7448795 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448803 : List Nat := [1, 1, 1, 8, 1, 1, 1, 4, 1, 4]
def baseStart_7448803 : Nat := 118140960795 + 7448803 * 2 ^ 59
def prefixEnd_7448803 : Nat := 4983230072969 + 3 ^ 40 * 7448803 * 2
def baseEnd_7448803 : Nat := 1274938746550841752568695

theorem tailTrace_7448803 : CollatzResearch.WordTrace tailWord_7448803 prefixEnd_7448803 1274938746550841752568695 := by
  unfold tailWord_7448803
  simp only [CollatzResearch.WordTrace]
  refine ⟨271680164833266360116135063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181120109888844240077423375 271680164833266360116135063)
  ·
    refine ⟨407520247249899540174202595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271680164833266360116135063 407520247249899540174202595)
    ·
      refine ⟨611280370874849310261303893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407520247249899540174202595 611280370874849310261303893)
      ·
        refine ⟨7163441846189640354624655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 611280370874849310261303893 7163441846189640354624655)
        ·
          refine ⟨10745162769284460531936983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7163441846189640354624655 10745162769284460531936983)
          ·
            refine ⟨16117744153926690797905475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10745162769284460531936983 16117744153926690797905475)
            ·
              refine ⟨24176616230890036196858213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16117744153926690797905475 24176616230890036196858213)
              ·
                refine ⟨4533115543291881786910915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24176616230890036196858213 4533115543291881786910915)
                ·
                  refine ⟨6799673314937822680366373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533115543291881786910915 6799673314937822680366373)
                  ·
                    refine ⟨1274938746550841752568695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6799673314937822680366373 1274938746550841752568695)
                    ·
                      rfl

theorem cell23_7448803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 1, 4].length) (baseStart_7448803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448803 prefixEnd_7448803 := by exact prefixLift 7448803
  have htrace : WordTrace (prefixWord ++ tailWord_7448803) baseStart_7448803 baseEnd_7448803 := by
    simpa [prefixWord, tailWord_7448803, baseEnd_7448803] using wordTrace_append hprefix tailTrace_7448803
  have hstable : (prefixWord ++ tailWord_7448803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448803).length < 2 ^ (prefixWord ++ tailWord_7448803).sum := by decide
  have hdescent : baseEnd_7448803 < baseStart_7448803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448832 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 4]
def baseStart_7448832 : Nat := 118140960795 + 7448832 * 2 ^ 59
def prefixEnd_7448832 : Nat := 4983230072969 + 3 ^ 40 * 7448832 * 2
def baseEnd_7448832 : Nat := 3824831130591505644243451

theorem tailTrace_7448832 : CollatzResearch.WordTrace tailWord_7448832 prefixEnd_7448832 3824831130591505644243451 := by
  unfold tailWord_7448832
  simp only [CollatzResearch.WordTrace]
  refine ⟨135840611275080649034470375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181120815033440865379293833 135840611275080649034470375)
  ·
    refine ⟨203760916912620973551705563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135840611275080649034470375 203760916912620973551705563)
    ·
      refine ⟨305641375368931460327558345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203760916912620973551705563 305641375368931460327558345)
      ·
        refine ⟨229231031526698595245668759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305641375368931460327558345 229231031526698595245668759)
        ·
          refine ⟨343846547290047892868503139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229231031526698595245668759 343846547290047892868503139)
          ·
            refine ⟨515769820935071839302754709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343846547290047892868503139 515769820935071839302754709)
            ·
              refine ⟨24176710356331492467316627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 515769820935071839302754709 24176710356331492467316627)
              ·
                refine ⟨36265065534497238700974941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24176710356331492467316627 36265065534497238700974941)
                ·
                  refine ⟨13599399575436464512865603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36265065534497238700974941 13599399575436464512865603)
                  ·
                    refine ⟨20399099363154696769298405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13599399575436464512865603 20399099363154696769298405)
                    ·
                      refine ⟨3824831130591505644243451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20399099363154696769298405 3824831130591505644243451)
                      ·
                        rfl

theorem cell23_7448832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_7448832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448832 prefixEnd_7448832 := by exact prefixLift 7448832
  have htrace : WordTrace (prefixWord ++ tailWord_7448832) baseStart_7448832 baseEnd_7448832 := by
    simpa [prefixWord, tailWord_7448832, baseEnd_7448832] using wordTrace_append hprefix tailTrace_7448832
  have hstable : (prefixWord ++ tailWord_7448832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448832).length < 2 ^ (prefixWord ++ tailWord_7448832).sum := by decide
  have hdescent : baseEnd_7448832 < baseStart_7448832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448836 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 1, 5, 2]
def baseStart_7448836 : Nat := 118140960795 + 7448836 * 2 ^ 59
def prefixEnd_7448836 : Nat := 4983230072969 + 3 ^ 40 * 7448836 * 2
def baseEnd_7448836 : Nat := 3824833184514123628593433

theorem tailTrace_7448836 : CollatzResearch.WordTrace tailWord_7448836 prefixEnd_7448836 3824833184514123628593433 := by
  unfold tailWord_7448836
  simp only [CollatzResearch.WordTrace]
  refine ⟨135840684221073403376043181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181120912294764537834724241 135840684221073403376043181)
  ·
    refine ⟨50940256582902526266016193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135840684221073403376043181 50940256582902526266016193)
    ·
      refine ⟨38205192437176894699512145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50940256582902526266016193 38205192437176894699512145)
      ·
        refine ⟨28653894327882671024634109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38205192437176894699512145 28653894327882671024634109)
        ·
          refine ⟨10745210372956001634237791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28653894327882671024634109 10745210372956001634237791)
          ·
            refine ⟨16117815559434002451356687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10745210372956001634237791 16117815559434002451356687)
            ·
              refine ⟨24176723339151003677035031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16117815559434002451356687 24176723339151003677035031)
              ·
                refine ⟨36265085008726505515552547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24176723339151003677035031 36265085008726505515552547)
                ·
                  refine ⟨54397627513089758273328821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36265085008726505515552547 54397627513089758273328821)
                  ·
                    refine ⟨5099777579352164838124577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54397627513089758273328821 5099777579352164838124577)
                    ·
                      refine ⟨3824833184514123628593433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5099777579352164838124577 3824833184514123628593433)
                      ·
                        rfl

theorem cell23_7448836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_7448836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448836 prefixEnd_7448836 := by exact prefixLift 7448836
  have htrace : WordTrace (prefixWord ++ tailWord_7448836) baseStart_7448836 baseEnd_7448836 := by
    simpa [prefixWord, tailWord_7448836, baseEnd_7448836] using wordTrace_append hprefix tailTrace_7448836
  have hstable : (prefixWord ++ tailWord_7448836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448836).length < 2 ^ (prefixWord ++ tailWord_7448836).sum := by decide
  have hdescent : baseEnd_7448836 < baseStart_7448836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448842 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 1, 6]
def baseStart_7448842 : Nat := 118140960795 + 7448842 * 2 ^ 59
def prefixEnd_7448842 : Nat := 4983230072969 + 3 ^ 40 * 7448842 * 2
def baseEnd_7448842 : Nat := 1274945421799350201706135

theorem tailTrace_7448842 : CollatzResearch.WordTrace tailWord_7448842 prefixEnd_7448842 1274945421799350201706135 := by
  unfold tailWord_7448842
  simp only [CollatzResearch.WordTrace]
  refine ⟨67920396820031267444201195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181121058186750046517869853 67920396820031267444201195)
  ·
    refine ⟨101880595230046901166301793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67920396820031267444201195 101880595230046901166301793)
    ·
      refine ⟨76410446422535175874726345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101880595230046901166301793 76410446422535175874726345)
      ·
        refine ⟨57307834816901381906044759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76410446422535175874726345 57307834816901381906044759)
        ·
          refine ⟨85961752225352072859067139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57307834816901381906044759 85961752225352072859067139)
          ·
            refine ⟨128942628338028109288600709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85961752225352072859067139 128942628338028109288600709)
            ·
              refine ⟨24176742813380270491612633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128942628338028109288600709 24176742813380270491612633)
              ·
                refine ⟨18132557110035202868709475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24176742813380270491612633 18132557110035202868709475)
                ·
                  refine ⟨27198835665052804303064213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18132557110035202868709475 27198835665052804303064213)
                  ·
                    refine ⟨1274945421799350201706135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27198835665052804303064213 1274945421799350201706135)
                    ·
                      rfl

theorem cell23_7448842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_7448842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448842 prefixEnd_7448842 := by exact prefixLift 7448842
  have htrace : WordTrace (prefixWord ++ tailWord_7448842) baseStart_7448842 baseEnd_7448842 := by
    simpa [prefixWord, tailWord_7448842, baseEnd_7448842] using wordTrace_append hprefix tailTrace_7448842
  have hstable : (prefixWord ++ tailWord_7448842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448842).length < 2 ^ (prefixWord ++ tailWord_7448842).sum := by decide
  have hdescent : baseEnd_7448842 < baseStart_7448842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448849 : List Nat := [1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 4]
def baseStart_7448849 : Nat := 118140960795 + 7448849 * 2 ^ 59
def prefixEnd_7448849 : Nat := 4983230072969 + 3 ^ 40 * 7448849 * 2
def baseEnd_7448849 : Nat := 3824839859762632077730873

theorem tailTrace_7448849 : CollatzResearch.WordTrace tailWord_7448849 prefixEnd_7448849 3824839859762632077730873 := by
  unfold tailWord_7448849
  simp only [CollatzResearch.WordTrace]
  refine ⟨271681842591099709972309601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181121228394066473314873067 271681842591099709972309601)
  ·
    refine ⟨203761381943324782479232201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271681842591099709972309601 203761381943324782479232201)
    ·
      refine ⟨152821036457493586859424151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203761381943324782479232201 152821036457493586859424151)
      ·
        refine ⟨229231554686240380289136227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152821036457493586859424151 229231554686240380289136227)
        ·
          refine ⟨343847332029360570433704341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229231554686240380289136227 343847332029360570433704341)
          ·
            refine ⟨16117843688876276739079891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 343847332029360570433704341 16117843688876276739079891)
            ·
              refine ⟨24176765533314415108619837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16117843688876276739079891 24176765533314415108619837)
              ·
                refine ⟨9066287074992905665732439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24176765533314415108619837 9066287074992905665732439)
                ·
                  refine ⟨13599430612489358498598659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9066287074992905665732439 13599430612489358498598659)
                  ·
                    refine ⟨20399145918734037747897989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13599430612489358498598659 20399145918734037747897989)
                    ·
                      refine ⟨3824839859762632077730873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20399145918734037747897989 3824839859762632077730873)
                      ·
                        rfl

theorem cell23_7448849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_7448849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448849 prefixEnd_7448849 := by exact prefixLift 7448849
  have htrace : WordTrace (prefixWord ++ tailWord_7448849) baseStart_7448849 baseEnd_7448849 := by
    simpa [prefixWord, tailWord_7448849, baseEnd_7448849] using wordTrace_append hprefix tailTrace_7448849
  have hstable : (prefixWord ++ tailWord_7448849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448849).length < 2 ^ (prefixWord ++ tailWord_7448849).sum := by decide
  have hdescent : baseEnd_7448849 < baseStart_7448849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448859 : List Nat := [1, 1, 1, 1, 1, 1, 9, 2, 2, 4]
def baseStart_7448859 : Nat := 118140960795 + 7448859 * 2 ^ 59
def prefixEnd_7448859 : Nat := 4983230072969 + 3 ^ 40 * 7448859 * 2
def baseEnd_7448859 : Nat := 1274948331523059012868609

theorem tailTrace_7448859 : CollatzResearch.WordTrace tailWord_7448859 prefixEnd_7448859 1274948331523059012868609 := by
  unfold tailWord_7448859
  simp only [CollatzResearch.WordTrace]
  refine ⟨271682207321063481680173631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181121471547375654453449087 271682207321063481680173631)
  ·
    refine ⟨407523310981595222520260447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271682207321063481680173631 407523310981595222520260447)
    ·
      refine ⟨611284966472392833780390671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407523310981595222520260447 611284966472392833780390671)
      ·
        refine ⟨916927449708589250670586007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611284966472392833780390671 916927449708589250670586007)
        ·
          refine ⟨1375391174562883876005879011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916927449708589250670586007 1375391174562883876005879011)
          ·
            refine ⟨2063086761844325814008818517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375391174562883876005879011 2063086761844325814008818517)
            ·
              refine ⟨12088398995181596566457921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2063086761844325814008818517 12088398995181596566457921)
              ·
                refine ⟨9066299246386197424843441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12088398995181596566457921 9066299246386197424843441)
                ·
                  refine ⟨6799724434789648068632581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9066299246386197424843441 6799724434789648068632581)
                  ·
                    refine ⟨1274948331523059012868609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6799724434789648068632581 1274948331523059012868609)
                    ·
                      rfl

theorem cell23_7448859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 4].length) (baseStart_7448859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448859 prefixEnd_7448859 := by exact prefixLift 7448859
  have htrace : WordTrace (prefixWord ++ tailWord_7448859) baseStart_7448859 baseEnd_7448859 := by
    simpa [prefixWord, tailWord_7448859, baseEnd_7448859] using wordTrace_append hprefix tailTrace_7448859
  have hstable : (prefixWord ++ tailWord_7448859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448859).length < 2 ^ (prefixWord ++ tailWord_7448859).sum := by decide
  have hdescent : baseEnd_7448859 < baseStart_7448859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448869 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 1, 1, 5]
def baseStart_7448869 : Nat := 118140960795 + 7448869 * 2 ^ 59
def prefixEnd_7448869 : Nat := 4983230072969 + 3 ^ 40 * 7448869 * 2
def baseEnd_7448869 : Nat := 3824850129375721999480781

theorem tailTrace_7448869 : CollatzResearch.WordTrace tailWord_7448869 prefixEnd_7448869 3824850129375721999480781 := by
  unfold tailWord_7448869
  simp only [CollatzResearch.WordTrace]
  refine ⟨271682572051027253388037661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181121714700684835592025107 271682572051027253388037661)
  ·
    refine ⟨101880964519135220020514123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271682572051027253388037661 101880964519135220020514123)
    ·
      refine ⟨152821446778702830030771185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101880964519135220020514123 152821446778702830030771185)
      ·
        refine ⟨114616085084027122523078389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152821446778702830030771185 114616085084027122523078389)
        ·
          refine ⟨10745257976627542736538599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114616085084027122523078389 10745257976627542736538599)
          ·
            refine ⟨16117886964941314104807899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10745257976627542736538599 16117886964941314104807899)
            ·
              refine ⟨24176830447411971157211849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16117886964941314104807899 24176830447411971157211849)
              ·
                refine ⟨18132622835558978367908887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24176830447411971157211849 18132622835558978367908887)
                ·
                  refine ⟨27198934253338467551863331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18132622835558978367908887 27198934253338467551863331)
                  ·
                    refine ⟨40798401380007701327794997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27198934253338467551863331 40798401380007701327794997)
                    ·
                      refine ⟨3824850129375721999480781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40798401380007701327794997 3824850129375721999480781)
                      ·
                        rfl

theorem cell23_7448869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_7448869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448869 prefixEnd_7448869 := by exact prefixLift 7448869
  have htrace : WordTrace (prefixWord ++ tailWord_7448869) baseStart_7448869 baseEnd_7448869 := by
    simpa [prefixWord, tailWord_7448869, baseEnd_7448869] using wordTrace_append hprefix tailTrace_7448869
  have hstable : (prefixWord ++ tailWord_7448869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448869).length < 2 ^ (prefixWord ++ tailWord_7448869).sum := by decide
  have hdescent : baseEnd_7448869 < baseStart_7448869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448889 : List Nat := [1, 2, 1, 6, 1, 1, 4, 7]
def baseStart_7448889 : Nat := 118140960795 + 7448889 * 2 ^ 59
def prefixEnd_7448889 : Nat := 4983230072969 + 3 ^ 40 * 7448889 * 2
def baseEnd_7448889 : Nat := 141661496258844885971507

theorem tailTrace_7448889 : CollatzResearch.WordTrace tailWord_7448889 prefixEnd_7448889 141661496258844885971507 := by
  unfold tailWord_7448889
  simp only [CollatzResearch.WordTrace]
  refine ⟨271683301510954796803765721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181122201007303197869177147 271683301510954796803765721)
  ·
    refine ⟨203762476133216097602824291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271683301510954796803765721 203762476133216097602824291)
    ·
      refine ⟨305643714199824146404236437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203762476133216097602824291 305643714199824146404236437)
      ·
        refine ⟨14327049103116756862698583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 305643714199824146404236437 14327049103116756862698583)
        ·
          refine ⟨21490573654675135294047875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14327049103116756862698583 21490573654675135294047875)
          ·
            refine ⟨32235860482012702941071813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21490573654675135294047875 32235860482012702941071813)
            ·
              refine ⟨6044223840377381801450965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32235860482012702941071813 6044223840377381801450965)
              ·
                refine ⟨141661496258844885971507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6044223840377381801450965 141661496258844885971507)
                ·
                  rfl

theorem cell23_7448889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 7].length) (baseStart_7448889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448889 prefixEnd_7448889 := by exact prefixLift 7448889
  have htrace : WordTrace (prefixWord ++ tailWord_7448889) baseStart_7448889 baseEnd_7448889 := by
    simpa [prefixWord, tailWord_7448889, baseEnd_7448889] using wordTrace_append hprefix tailTrace_7448889
  have hstable : (prefixWord ++ tailWord_7448889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448889).length < 2 ^ (prefixWord ++ tailWord_7448889).sum := by decide
  have hdescent : baseEnd_7448889 < baseStart_7448889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448899 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 4, 1, 3]
def baseStart_7448899 : Nat := 118140960795 + 7448899 * 2 ^ 59
def prefixEnd_7448899 : Nat := 4983230072969 + 3 ^ 40 * 7448899 * 2
def baseEnd_7448899 : Nat := 3824865533795356882105643

theorem tailTrace_7448899 : CollatzResearch.WordTrace tailWord_7448899 prefixEnd_7448899 3824865533795356882105643 := by
  unfold tailWord_7448899
  simp only [CollatzResearch.WordTrace]
  refine ⟨271683666240918568511629751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181122444160612379007753167 271683666240918568511629751)
  ·
    refine ⟨407525499361377852767444627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271683666240918568511629751 407525499361377852767444627)
    ·
      refine ⟨611288249042066779151166941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407525499361377852767444627 611288249042066779151166941)
      ·
        refine ⟨229233093390775042181687603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 611288249042066779151166941 229233093390775042181687603)
        ·
          refine ⟨343849640086162563272531405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229233093390775042181687603 343849640086162563272531405)
          ·
            refine ⟨128943615032310961227199277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343849640086162563272531405 128943615032310961227199277)
            ·
              refine ⟨48353855637116610460199729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128943615032310961227199277 48353855637116610460199729)
              ·
                refine ⟨36265391727837457845149797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48353855637116610460199729 36265391727837457845149797)
                ·
                  refine ⟨6799760948969523345965587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36265391727837457845149797 6799760948969523345965587)
                  ·
                    refine ⟨10199641423454285018948381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6799760948969523345965587 10199641423454285018948381)
                    ·
                      refine ⟨3824865533795356882105643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10199641423454285018948381 3824865533795356882105643)
                      ·
                        rfl

theorem cell23_7448899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 1, 3].length) (baseStart_7448899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448899 prefixEnd_7448899 := by exact prefixLift 7448899
  have htrace : WordTrace (prefixWord ++ tailWord_7448899) baseStart_7448899 baseEnd_7448899 := by
    simpa [prefixWord, tailWord_7448899, baseEnd_7448899] using wordTrace_append hprefix tailTrace_7448899
  have hstable : (prefixWord ++ tailWord_7448899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448899).length < 2 ^ (prefixWord ++ tailWord_7448899).sum := by decide
  have hdescent : baseEnd_7448899 < baseStart_7448899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448916 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_7448916 : Nat := 118140960795 + 7448916 * 2 ^ 59
def prefixEnd_7448916 : Nat := 4983230072969 + 3 ^ 40 * 7448916 * 2
def baseEnd_7448916 : Nat := 3824874262966483315593065

theorem tailTrace_7448916 : CollatzResearch.WordTrace tailWord_7448916 prefixEnd_7448916 3824874262966483315593065 := by
  unfold tailWord_7448916
  simp only [CollatzResearch.WordTrace]
  refine ⟨135842143140928490207499301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181122857521237986943332401 135842143140928490207499301)
  ·
    refine ⟨25470401838924091913906119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135842143140928490207499301 25470401838924091913906119)
    ·
      refine ⟨38205602758386137870859179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25470401838924091913906119 38205602758386137870859179)
      ·
        refine ⟨57308404137579206806288769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38205602758386137870859179 57308404137579206806288769)
        ·
          refine ⟨42981303103184405104716577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57308404137579206806288769 42981303103184405104716577)
          ·
            refine ⟨32235977327388303828537433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42981303103184405104716577 32235977327388303828537433)
            ·
              refine ⟨24176982995541227871403075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32235977327388303828537433 24176982995541227871403075)
              ·
                refine ⟨36265474493311841807104613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24176982995541227871403075 36265474493311841807104613)
                ·
                  refine ⟨6799776467495970338832115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36265474493311841807104613 6799776467495970338832115)
                  ·
                    refine ⟨10199664701243955508248173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6799776467495970338832115 10199664701243955508248173)
                    ·
                      refine ⟨3824874262966483315593065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10199664701243955508248173 3824874262966483315593065)
                      ·
                        rfl

theorem cell23_7448916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_7448916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448916 prefixEnd_7448916 := by exact prefixLift 7448916
  have htrace : WordTrace (prefixWord ++ tailWord_7448916) baseStart_7448916 baseEnd_7448916 := by
    simpa [prefixWord, tailWord_7448916, baseEnd_7448916] using wordTrace_append hprefix tailTrace_7448916
  have hstable : (prefixWord ++ tailWord_7448916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448916).length < 2 ^ (prefixWord ++ tailWord_7448916).sum := by decide
  have hdescent : baseEnd_7448916 < baseStart_7448916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448917 : List Nat := [1, 3, 2, 2, 4, 1, 3, 2, 1, 2, 2]
def baseStart_7448917 : Nat := 118140960795 + 7448917 * 2 ^ 59
def prefixEnd_7448917 : Nat := 4983230072969 + 3 ^ 40 * 7448917 * 2
def baseEnd_7448917 : Nat := 3824874776447137811680561

theorem tailTrace_7448917 : CollatzResearch.WordTrace tailWord_7448917 prefixEnd_7448917 3824874776447137811680561 := by
  unfold tailWord_7448917
  simp only [CollatzResearch.WordTrace]
  refine ⟨271684322754853357585785005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181122881836568905057190003 271684322754853357585785005)
  ·
    refine ⟨101881621033070009094669377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271684322754853357585785005 101881621033070009094669377)
    ·
      refine ⟨76411215774802506821002033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101881621033070009094669377 76411215774802506821002033)
      ·
        refine ⟨57308411831101880115751525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76411215774802506821002033 57308411831101880115751525)
        ·
          refine ⟨10745327218331602521703411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57308411831101880115751525 10745327218331602521703411)
          ·
            refine ⟨16117990827497403782555117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10745327218331602521703411 16117990827497403782555117)
            ·
              refine ⟨6044246560311526418458169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16117990827497403782555117 6044246560311526418458169)
              ·
                refine ⟨4533184920233644813843627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6044246560311526418458169 4533184920233644813843627)
                ·
                  refine ⟨6799777380350467220765441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533184920233644813843627 6799777380350467220765441)
                  ·
                    refine ⟨5099833035262850415574081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6799777380350467220765441 5099833035262850415574081)
                    ·
                      refine ⟨3824874776447137811680561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5099833035262850415574081 3824874776447137811680561)
                      ·
                        rfl

theorem cell23_7448917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_7448917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448917 prefixEnd_7448917 := by exact prefixLift 7448917
  have htrace : WordTrace (prefixWord ++ tailWord_7448917) baseStart_7448917 baseEnd_7448917 := by
    simpa [prefixWord, tailWord_7448917, baseEnd_7448917] using wordTrace_append hprefix tailTrace_7448917
  have hstable : (prefixWord ++ tailWord_7448917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448917).length < 2 ^ (prefixWord ++ tailWord_7448917).sum := by decide
  have hdescent : baseEnd_7448917 < baseStart_7448917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448922 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4]
def baseStart_7448922 : Nat := 118140960795 + 7448922 * 2 ^ 59
def prefixEnd_7448922 : Nat := 4983230072969 + 3 ^ 40 * 7448922 * 2
def baseEnd_7448922 : Nat := 3824877343850410292118037

theorem tailTrace_7448922 : CollatzResearch.WordTrace tailWord_7448922 prefixEnd_7448922 3824877343850410292118037 := by
  unfold tailWord_7448922
  simp only [CollatzResearch.WordTrace]
  refine ⟨67921126279958810859929255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181123003413223495626478013 67921126279958810859929255)
  ·
    refine ⟨101881689419938216289893883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67921126279958810859929255 101881689419938216289893883)
    ·
      refine ⟨152822534129907324434840825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101881689419938216289893883 152822534129907324434840825)
      ·
        refine ⟨114616900597430493326130619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152822534129907324434840825 114616900597430493326130619)
        ·
          refine ⟨171925350896145739989195929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114616900597430493326130619 171925350896145739989195929)
          ·
            refine ⟨128944013172109304991896947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171925350896145739989195929 128944013172109304991896947)
            ·
              refine ⟨193416019758163957487845421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128944013172109304991896947 193416019758163957487845421)
              ·
                refine ⟨72531007409311484057942033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193416019758163957487845421 72531007409311484057942033)
                ·
                  refine ⟨54398255556983613043456525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72531007409311484057942033 54398255556983613043456525)
                  ·
                    refine ⟨20399345833868854891296197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54398255556983613043456525 20399345833868854891296197)
                    ·
                      refine ⟨3824877343850410292118037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20399345833868854891296197 3824877343850410292118037)
                      ·
                        rfl

theorem cell23_7448922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_7448922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448922 prefixEnd_7448922 := by exact prefixLift 7448922
  have htrace : WordTrace (prefixWord ++ tailWord_7448922) baseStart_7448922 baseEnd_7448922 := by
    simpa [prefixWord, tailWord_7448922, baseEnd_7448922] using wordTrace_append hprefix tailTrace_7448922
  have hstable : (prefixWord ++ tailWord_7448922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448922).length < 2 ^ (prefixWord ++ tailWord_7448922).sum := by decide
  have hdescent : baseEnd_7448922 < baseStart_7448922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448932 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 1, 8]
def baseStart_7448932 : Nat := 118140960795 + 7448932 * 2 ^ 59
def prefixEnd_7448932 : Nat := 4983230072969 + 3 ^ 40 * 7448932 * 2
def baseEnd_7448932 : Nat := 1274960826218985084330997

theorem tailTrace_7448932 : CollatzResearch.WordTrace tailWord_7448932 prefixEnd_7448932 1274960826218985084330997 := by
  unfold tailWord_7448932
  simp only [CollatzResearch.WordTrace]
  refine ⟨135842434924899507573790525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181123246566532676765054033 135842434924899507573790525)
  ·
    refine ⟨50940913096837315340171447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135842434924899507573790525 50940913096837315340171447)
    ·
      refine ⟨76411369645255973010257171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50940913096837315340171447 76411369645255973010257171)
      ·
        refine ⟨114617054467883959515385757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76411369645255973010257171 114617054467883959515385757)
        ·
          refine ⟨42981395425456484818269659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114617054467883959515385757 42981395425456484818269659)
          ·
            refine ⟨64472093138184727227404489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42981395425456484818269659 64472093138184727227404489)
            ·
              refine ⟨48354069853638545420553367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64472093138184727227404489 48354069853638545420553367)
              ·
                refine ⟨72531104780457818130830051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48354069853638545420553367 72531104780457818130830051)
                ·
                  refine ⟨108796657170686727196245077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72531104780457818130830051 108796657170686727196245077)
                  ·
                    refine ⟨1274960826218985084330997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108796657170686727196245077 1274960826218985084330997)
                    ·
                      rfl

theorem cell23_7448932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_7448932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448932 prefixEnd_7448932 := by exact prefixLift 7448932
  have htrace : WordTrace (prefixWord ++ tailWord_7448932) baseStart_7448932 baseEnd_7448932 := by
    simpa [prefixWord, tailWord_7448932, baseEnd_7448932] using wordTrace_append hprefix tailTrace_7448932
  have hstable : (prefixWord ++ tailWord_7448932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448932).length < 2 ^ (prefixWord ++ tailWord_7448932).sum := by decide
  have hdescent : baseEnd_7448932 < baseStart_7448932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448933 : List Nat := [1, 3, 1, 3, 1, 3, 4, 1, 2, 1, 3]
def baseStart_7448933 : Nat := 118140960795 + 7448933 * 2 ^ 59
def prefixEnd_7448933 : Nat := 4983230072969 + 3 ^ 40 * 7448933 * 2
def baseEnd_7448933 : Nat := 3824882992137609749080487

theorem tailTrace_7448933 : CollatzResearch.WordTrace tailWord_7448933 prefixEnd_7448933 3824882992137609749080487 := by
  unfold tailWord_7448933
  simp only [CollatzResearch.WordTrace]
  refine ⟨271684906322795392318367453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181123270881863594878911635 271684906322795392318367453)
  ·
    refine ⟨101881839871048272119387795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271684906322795392318367453 101881839871048272119387795)
    ·
      refine ⟨152822759806572408179081693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101881839871048272119387795 152822759806572408179081693)
      ·
        refine ⟨57308534927464653067155635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152822759806572408179081693 57308534927464653067155635)
        ·
          refine ⟨85962802391196979600733453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57308534927464653067155635 85962802391196979600733453)
          ·
            refine ⟨32236050896698867350275045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85962802391196979600733453 32236050896698867350275045)
            ·
              refine ⟨6044259543131037628176571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32236050896698867350275045 6044259543131037628176571)
              ·
                refine ⟨9066389314696556442264857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6044259543131037628176571 9066389314696556442264857)
                ·
                  refine ⟨6799791986022417331698643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9066389314696556442264857 6799791986022417331698643)
                  ·
                    refine ⟨10199687979033625997547965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6799791986022417331698643 10199687979033625997547965)
                    ·
                      refine ⟨3824882992137609749080487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10199687979033625997547965 3824882992137609749080487)
                      ·
                        rfl

theorem cell23_7448933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_7448933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448933 prefixEnd_7448933 := by exact prefixLift 7448933
  have htrace : WordTrace (prefixWord ++ tailWord_7448933) baseStart_7448933 baseEnd_7448933 := by
    simpa [prefixWord, tailWord_7448933, baseEnd_7448933] using wordTrace_append hprefix tailTrace_7448933
  have hstable : (prefixWord ++ tailWord_7448933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448933).length < 2 ^ (prefixWord ++ tailWord_7448933).sum := by decide
  have hdescent : baseEnd_7448933 < baseStart_7448933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448956 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 4, 2, 2]
def baseStart_7448956 : Nat := 118140960795 + 7448956 * 2 ^ 59
def prefixEnd_7448956 : Nat := 4983230072969 + 3 ^ 40 * 7448956 * 2
def baseEnd_7448956 : Nat := 3824894802192663159092881

theorem tailTrace_7448956 : CollatzResearch.WordTrace tailWord_7448956 prefixEnd_7448956 3824894802192663159092881 := by
  unfold tailWord_7448956
  simp only [CollatzResearch.WordTrace]
  refine ⟨135842872600856033623227361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181123830134474711497636481 135842872600856033623227361)
  ·
    refine ⟨101882154450642025217420521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135842872600856033623227361 101882154450642025217420521)
    ·
      refine ⟨76411615837981518913065391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101882154450642025217420521 76411615837981518913065391)
      ·
        refine ⟨114617423756972278369598087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76411615837981518913065391 114617423756972278369598087)
        ·
          refine ⟨171926135635458417554397131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114617423756972278369598087 171926135635458417554397131)
          ·
            refine ⟨257889203453187626331595697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171926135635458417554397131 257889203453187626331595697)
            ·
              refine ⟨193416902589890719748696773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257889203453187626331595697 193416902589890719748696773)
              ·
                refine ⟨36265669235604509952880645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193416902589890719748696773 36265669235604509952880645)
                ·
                  refine ⟨6799812981675845616165121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36265669235604509952880645 6799812981675845616165121)
                  ·
                    refine ⟨5099859736256884212123841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6799812981675845616165121 5099859736256884212123841)
                    ·
                      refine ⟨3824894802192663159092881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5099859736256884212123841 3824894802192663159092881)
                      ·
                        rfl

theorem cell23_7448956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_7448956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448956 prefixEnd_7448956 := by exact prefixLift 7448956
  have htrace : WordTrace (prefixWord ++ tailWord_7448956) baseStart_7448956 baseEnd_7448956 := by
    simpa [prefixWord, tailWord_7448956, baseEnd_7448956] using wordTrace_append hprefix tailTrace_7448956
  have hstable : (prefixWord ++ tailWord_7448956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448956).length < 2 ^ (prefixWord ++ tailWord_7448956).sum := by decide
  have hdescent : baseEnd_7448956 < baseStart_7448956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7448990 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_7448990 : Nat := 118140960795 + 7448990 * 2 ^ 59
def prefixEnd_7448990 : Nat := 4983230072969 + 3 ^ 40 * 7448990 * 2
def baseEnd_7448990 : Nat := 3824912260534916026067725

theorem tailTrace_7448990 : CollatzResearch.WordTrace tailWord_7448990 prefixEnd_7448990 3824912260534916026067725 := by
  unfold tailWord_7448990
  simp only [CollatzResearch.WordTrace]
  refine ⟨33960873160448611381649053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181124656855725927368794949 33960873160448611381649053)
  ·
    refine ⟨12735327435168229268118395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33960873160448611381649053 12735327435168229268118395)
    ·
      refine ⟨19102991152752343902177593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12735327435168229268118395 19102991152752343902177593)
      ·
        refine ⟨14327243364564257926633195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19102991152752343902177593 14327243364564257926633195)
        ·
          refine ⟨21490865046846386889949793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14327243364564257926633195 21490865046846386889949793)
          ·
            refine ⟨16118148785134790167462345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21490865046846386889949793 16118148785134790167462345)
            ·
              refine ⟨12088611588851092625596759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16118148785134790167462345 12088611588851092625596759)
              ·
                refine ⟨18132917383276638938395139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12088611588851092625596759 18132917383276638938395139)
                ·
                  refine ⟨27199376074914958407592709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18132917383276638938395139 27199376074914958407592709)
                  ·
                    refine ⟨5099883014046554701423633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27199376074914958407592709 5099883014046554701423633)
                    ·
                      refine ⟨3824912260534916026067725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5099883014046554701423633 3824912260534916026067725)
                      ·
                        rfl

theorem cell23_7448990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_7448990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7448990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7448990 prefixEnd_7448990 := by exact prefixLift 7448990
  have htrace : WordTrace (prefixWord ++ tailWord_7448990) baseStart_7448990 baseEnd_7448990 := by
    simpa [prefixWord, tailWord_7448990, baseEnd_7448990] using wordTrace_append hprefix tailTrace_7448990
  have hstable : (prefixWord ++ tailWord_7448990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7448990).length < 2 ^ (prefixWord ++ tailWord_7448990).sum := by decide
  have hdescent : baseEnd_7448990 < baseStart_7448990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7448990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449009 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 1, 7]
def baseStart_7449009 : Nat := 118140960795 + 7449009 * 2 ^ 59
def prefixEnd_7449009 : Nat := 4983230072969 + 3 ^ 40 * 7449009 * 2
def baseEnd_7449009 : Nat := 1274974005555783817243379

theorem tailTrace_7449009 : CollatzResearch.WordTrace tailWord_7449009 prefixEnd_7449009 1274974005555783817243379 := by
  unfold tailWord_7449009
  simp only [CollatzResearch.WordTrace]
  refine ⟨271687678270520057298134081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181125118847013371532089387 271687678270520057298134081)
  ·
    refine ⟨203765758702890042973600561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271687678270520057298134081 203765758702890042973600561)
    ·
      refine ⟨152824319027167532230200421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203765758702890042973600561 152824319027167532230200421)
      ·
        refine ⟨28654559817593912293162579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152824319027167532230200421 28654559817593912293162579)
        ·
          refine ⟨42981839726390868439743869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28654559817593912293162579 42981839726390868439743869)
          ·
            refine ⟨16118189897396575664903951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42981839726390868439743869 16118189897396575664903951)
            ·
              refine ⟨24177284846094863497355927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16118189897396575664903951 24177284846094863497355927)
              ·
                refine ⟨36265927269142295246033891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24177284846094863497355927 36265927269142295246033891)
                ·
                  refine ⟨54398890903713442869050837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36265927269142295246033891 54398890903713442869050837)
                  ·
                    refine ⟨1274974005555783817243379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54398890903713442869050837 1274974005555783817243379)
                    ·
                      rfl

theorem cell23_7449009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_7449009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449009 prefixEnd_7449009 := by exact prefixLift 7449009
  have htrace : WordTrace (prefixWord ++ tailWord_7449009) baseStart_7449009 baseEnd_7449009 := by
    simpa [prefixWord, tailWord_7449009, baseEnd_7449009] using wordTrace_append hprefix tailTrace_7449009
  have hstable : (prefixWord ++ tailWord_7449009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449009).length < 2 ^ (prefixWord ++ tailWord_7449009).sum := by decide
  have hdescent : baseEnd_7449009 < baseStart_7449009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449013 : List Nat := [1, 3, 3, 2, 3, 1, 2, 3, 5]
def baseStart_7449013 : Nat := 118140960795 + 7449013 * 2 ^ 59
def prefixEnd_7449013 : Nat := 4983230072969 + 3 ^ 40 * 7449013 * 2
def baseEnd_7449013 : Nat := 424991563398885492897791

theorem tailTrace_7449013 : CollatzResearch.WordTrace tailWord_7449013 prefixEnd_7449013 424991563398885492897791 := by
  unfold tailWord_7449013
  simp only [CollatzResearch.WordTrace]
  refine ⟨271687824162505565981279693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181125216108337043987519795 271687824162505565981279693)
  ·
    refine ⟨101882934060939587242979885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271687824162505565981279693 101882934060939587242979885)
    ·
      refine ⟨38206100272852345216117457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101882934060939587242979885 38206100272852345216117457)
      ·
        refine ⟨28654575204639258912088093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38206100272852345216117457 28654575204639258912088093)
        ·
          refine ⟨10745465701739722092033035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28654575204639258912088093 10745465701739722092033035)
          ·
            refine ⟨16118198552609583138049553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10745465701739722092033035 16118198552609583138049553)
            ·
              refine ⟨12088648914457187353537165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16118198552609583138049553 12088648914457187353537165)
              ·
                refine ⟨4533243342921445257576437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12088648914457187353537165 4533243342921445257576437)
                ·
                  refine ⟨424991563398885492897791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4533243342921445257576437 424991563398885492897791)
                  ·
                    rfl

theorem cell23_7449013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 5].length) (baseStart_7449013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449013 prefixEnd_7449013 := by exact prefixLift 7449013
  have htrace : WordTrace (prefixWord ++ tailWord_7449013) baseStart_7449013 baseEnd_7449013 := by
    simpa [prefixWord, tailWord_7449013, baseEnd_7449013] using wordTrace_append hprefix tailTrace_7449013
  have hstable : (prefixWord ++ tailWord_7449013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449013).length < 2 ^ (prefixWord ++ tailWord_7449013).sum := by decide
  have hdescent : baseEnd_7449013 < baseStart_7449013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449046 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_7449046 : Nat := 118140960795 + 7449046 * 2 ^ 59
def prefixEnd_7449046 : Nat := 4983230072969 + 3 ^ 40 * 7449046 * 2
def baseEnd_7449046 : Nat := 3824941015451567806967467

theorem tailTrace_7449046 : CollatzResearch.WordTrace tailWord_7449046 prefixEnd_7449046 3824941015451567806967467 := by
  unfold tailWord_7449046
  simp only [CollatzResearch.WordTrace]
  refine ⟨16980564235711625788576937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181126018514257341744820661 16980564235711625788576937)
  ·
    refine ⟨12735423176783719341432703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16980564235711625788576937 12735423176783719341432703)
    ·
      refine ⟨19103134765175579012149055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12735423176783719341432703 19103134765175579012149055)
      ·
        refine ⟨28654702147763368518223583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19103134765175579012149055 28654702147763368518223583)
        ·
          refine ⟨42982053221645052777335375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28654702147763368518223583 42982053221645052777335375)
          ·
            refine ⟨64473079832467579166003063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42982053221645052777335375 64473079832467579166003063)
            ·
              refine ⟨96709619748701368749004595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64473079832467579166003063 96709619748701368749004595)
              ·
                refine ⟨145064429623052053123506893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96709619748701368749004595 145064429623052053123506893)
                ·
                  refine ⟨54399161108644519921315085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145064429623052053123506893 54399161108644519921315085)
                  ·
                    refine ⟨20399685415741694970493157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54399161108644519921315085 20399685415741694970493157)
                    ·
                      refine ⟨3824941015451567806967467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20399685415741694970493157 3824941015451567806967467)
                      ·
                        rfl

theorem cell23_7449046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_7449046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449046 prefixEnd_7449046 := by exact prefixLift 7449046
  have htrace : WordTrace (prefixWord ++ tailWord_7449046) baseStart_7449046 baseEnd_7449046 := by
    simpa [prefixWord, tailWord_7449046, baseEnd_7449046] using wordTrace_append hprefix tailTrace_7449046
  have hstable : (prefixWord ++ tailWord_7449046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449046).length < 2 ^ (prefixWord ++ tailWord_7449046).sum := by decide
  have hdescent : baseEnd_7449046 < baseStart_7449046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449049 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 3, 4, 3]
def baseStart_7449049 : Nat := 118140960795 + 7449049 * 2 ^ 59
def prefixEnd_7449049 : Nat := 4983230072969 + 3 ^ 40 * 7449049 * 2
def baseEnd_7449049 : Nat := 3824942555893531295229953

theorem tailTrace_7449049 : CollatzResearch.WordTrace tailWord_7449049 prefixEnd_7449049 3824942555893531295229953 := by
  unfold tailWord_7449049
  simp only [CollatzResearch.WordTrace]
  refine ⟨271689137190375144129590201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181126091460250096086393467 271689137190375144129590201)
  ·
    refine ⟨203766852892781358097192651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271689137190375144129590201 203766852892781358097192651)
    ·
      refine ⟨305650279339172037145788977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203766852892781358097192651 305650279339172037145788977)
      ·
        refine ⟨229237709504379027859341733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305650279339172037145788977 229237709504379027859341733)
        ·
          refine ⟨42982070532071067723626575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229237709504379027859341733 42982070532071067723626575)
          ·
            refine ⟨64473105798106601585439863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42982070532071067723626575 64473105798106601585439863)
            ·
              refine ⟨96709658697159902378159795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64473105798106601585439863 96709658697159902378159795)
              ·
                refine ⟨145064488045739853567239693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96709658697159902378159795 145064488045739853567239693)
                ·
                  refine ⟨54399183017152445087714885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145064488045739853567239693 54399183017152445087714885)
                  ·
                    refine ⟨10199846815716083453946541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54399183017152445087714885 10199846815716083453946541)
                    ·
                      refine ⟨3824942555893531295229953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10199846815716083453946541 3824942555893531295229953)
                      ·
                        rfl

theorem cell23_7449049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_7449049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449049 prefixEnd_7449049 := by exact prefixLift 7449049
  have htrace : WordTrace (prefixWord ++ tailWord_7449049) baseStart_7449049 baseEnd_7449049 := by
    simpa [prefixWord, tailWord_7449049, baseEnd_7449049] using wordTrace_append hprefix tailTrace_7449049
  have hstable : (prefixWord ++ tailWord_7449049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449049).length < 2 ^ (prefixWord ++ tailWord_7449049).sum := by decide
  have hdescent : baseEnd_7449049 < baseStart_7449049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449066 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_7449066 : Nat := 118140960795 + 7449066 * 2 ^ 59
def prefixEnd_7449066 : Nat := 4983230072969 + 3 ^ 40 * 7449066 * 2
def baseEnd_7449066 : Nat := 3824951285064657728717375

theorem tailTrace_7449066 : CollatzResearch.WordTrace tailWord_7449066 prefixEnd_7449066 3824951285064657728717375 := by
  unfold tailWord_7449066
  simp only [CollatzResearch.WordTrace]
  refine ⟨67922439307828389008239763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181126504820875704021972701 67922439307828389008239763)
  ·
    refine ⟨101883658961742583512359645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67922439307828389008239763 101883658961742583512359645)
    ·
      refine ⟨38206372110653468817134867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101883658961742583512359645 38206372110653468817134867)
      ·
        refine ⟨57309558165980203225702301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38206372110653468817134867 57309558165980203225702301)
        ·
          refine ⟨21491084312242576209638363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57309558165980203225702301 21491084312242576209638363)
          ·
            refine ⟨32236626468363864314457545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21491084312242576209638363 32236626468363864314457545)
            ·
              refine ⟨24177469851272898235843159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32236626468363864314457545 24177469851272898235843159)
              ·
                refine ⟨36266204776909347353764739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24177469851272898235843159 36266204776909347353764739)
                ·
                  refine ⟨54399307165364021030647109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36266204776909347353764739 54399307165364021030647109)
                  ·
                    refine ⟨10199870093505753943246333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54399307165364021030647109 10199870093505753943246333)
                    ·
                      refine ⟨3824951285064657728717375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10199870093505753943246333 3824951285064657728717375)
                      ·
                        rfl

theorem cell23_7449066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_7449066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449066 prefixEnd_7449066 := by exact prefixLift 7449066
  have htrace : WordTrace (prefixWord ++ tailWord_7449066) baseStart_7449066 baseEnd_7449066 := by
    simpa [prefixWord, tailWord_7449066, baseEnd_7449066] using wordTrace_append hprefix tailTrace_7449066
  have hstable : (prefixWord ++ tailWord_7449066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449066).length < 2 ^ (prefixWord ++ tailWord_7449066).sum := by decide
  have hdescent : baseEnd_7449066 < baseStart_7449066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449116 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 3, 5]
def baseStart_7449116 : Nat := 118140960795 + 7449116 * 2 ^ 59
def prefixEnd_7449116 : Nat := 4983230072969 + 3 ^ 40 * 7449116 * 2
def baseEnd_7449116 : Nat := 1274992319699127511030715

theorem tailTrace_7449116 : CollatzResearch.WordTrace tailWord_7449116 prefixEnd_7449116 1274992319699127511030715 := by
  unfold tailWord_7449116
  simp only [CollatzResearch.WordTrace]
  refine ⟨135845790440566207286139601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181127720587421609714852801 135845790440566207286139601)
  ·
    refine ⟨101884342830424655464604701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135845790440566207286139601 101884342830424655464604701)
    ·
      refine ⟨38206628561409245799226763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101884342830424655464604701 38206628561409245799226763)
      ·
        refine ⟨57309942842113868698840145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38206628561409245799226763 57309942842113868698840145)
        ·
          refine ⟨42982457131585401524130109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57309942842113868698840145 42982457131585401524130109)
          ·
            refine ⟨16118421424344525571548791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42982457131585401524130109 16118421424344525571548791)
            ·
              refine ⟨24177632136516788357323187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16118421424344525571548791 24177632136516788357323187)
              ·
                refine ⟨36266448204775182535984781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24177632136516788357323187 36266448204775182535984781)
                ·
                  refine ⟨13599918076790693450994293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36266448204775182535984781 13599918076790693450994293)
                  ·
                    refine ⟨1274992319699127511030715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13599918076790693450994293 1274992319699127511030715)
                    ·
                      rfl

theorem cell23_7449116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_7449116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449116 prefixEnd_7449116 := by exact prefixLift 7449116
  have htrace : WordTrace (prefixWord ++ tailWord_7449116) baseStart_7449116 baseEnd_7449116 := by
    simpa [prefixWord, tailWord_7449116, baseEnd_7449116] using wordTrace_append hprefix tailTrace_7449116
  have hstable : (prefixWord ++ tailWord_7449116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449116).length < 2 ^ (prefixWord ++ tailWord_7449116).sum := by decide
  have hdescent : baseEnd_7449116 < baseStart_7449116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449123 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 2, 3, 2]
def baseStart_7449123 : Nat := 118140960795 + 7449123 * 2 ^ 59
def prefixEnd_7449123 : Nat := 4983230072969 + 3 ^ 40 * 7449123 * 2
def baseEnd_7449123 : Nat := 3824980553461964005704613

theorem tailTrace_7449123 : CollatzResearch.WordTrace tailWord_7449123 prefixEnd_7449123 3824980553461964005704613 := by
  unfold tailWord_7449123
  simp only [CollatzResearch.WordTrace]
  refine ⟨271691836192107054767784023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181127890794738036511856015 271691836192107054767784023)
  ·
    refine ⟨407537754288160582151676035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271691836192107054767784023 407537754288160582151676035)
    ·
      refine ⟨611306631432240873227514053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407537754288160582151676035 611306631432240873227514053)
      ·
        refine ⟨114619993393545163730158885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 611306631432240873227514053 114619993393545163730158885)
        ·
          refine ⟨21491248761289718199404791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114619993393545163730158885 21491248761289718199404791)
          ·
            refine ⟨32236873141934577299107187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21491248761289718199404791 32236873141934577299107187)
            ·
              refine ⟨48355309712901865948660781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32236873141934577299107187 48355309712901865948660781)
              ·
                refine ⟨18133241142338199730747793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48355309712901865948660781 18133241142338199730747793)
                ·
                  refine ⟨13599930856753649798060845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18133241142338199730747793 13599930856753649798060845)
                  ·
                    refine ⟨5099974071282618674272817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13599930856753649798060845 5099974071282618674272817)
                    ·
                      refine ⟨3824980553461964005704613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5099974071282618674272817 3824980553461964005704613)
                      ·
                        rfl

theorem cell23_7449123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_7449123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449123 prefixEnd_7449123 := by exact prefixLift 7449123
  have htrace : WordTrace (prefixWord ++ tailWord_7449123) baseStart_7449123 baseEnd_7449123 := by
    simpa [prefixWord, tailWord_7449123, baseEnd_7449123] using wordTrace_append hprefix tailTrace_7449123
  have hstable : (prefixWord ++ tailWord_7449123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449123).length < 2 ^ (prefixWord ++ tailWord_7449123).sum := by decide
  have hdescent : baseEnd_7449123 < baseStart_7449123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449136 : List Nat := [2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 4]
def baseStart_7449136 : Nat := 118140960795 + 7449136 * 2 ^ 59
def prefixEnd_7449136 : Nat := 4983230072969 + 3 ^ 40 * 7449136 * 2
def baseEnd_7449136 : Nat := 3824987228710472454842053

theorem tailTrace_7449136 : CollatzResearch.WordTrace tailWord_7449136 prefixEnd_7449136 3824987228710472454842053 := by
  unfold tailWord_7449136
  simp only [CollatzResearch.WordTrace]
  refine ⟨135846155170529978994003631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181128206894039971992004841 135846155170529978994003631)
  ·
    refine ⟨203769232755794968491005447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135846155170529978994003631 203769232755794968491005447)
    ·
      refine ⟨305653849133692452736508171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203769232755794968491005447 305653849133692452736508171)
      ·
        refine ⟨458480773700538679104762257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305653849133692452736508171 458480773700538679104762257)
        ·
          refine ⟨343860580275404009328571693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458480773700538679104762257 343860580275404009328571693)
          ·
            refine ⟨128947717603276503498214385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343860580275404009328571693 128947717603276503498214385)
            ·
              refine ⟨96710788202457377623660789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128947717603276503498214385 96710788202457377623660789)
              ·
                refine ⟨9066636393980379152218199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96710788202457377623660789 9066636393980379152218199)
                ·
                  refine ⟨13599954590970568728327299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9066636393980379152218199 13599954590970568728327299)
                  ·
                    refine ⟨20399931886455853092490949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13599954590970568728327299 20399931886455853092490949)
                    ·
                      refine ⟨3824987228710472454842053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20399931886455853092490949 3824987228710472454842053)
                      ·
                        rfl

theorem cell23_7449136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 4].length) (baseStart_7449136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449136 prefixEnd_7449136 := by exact prefixLift 7449136
  have htrace : WordTrace (prefixWord ++ tailWord_7449136) baseStart_7449136 baseEnd_7449136 := by
    simpa [prefixWord, tailWord_7449136, baseEnd_7449136] using wordTrace_append hprefix tailTrace_7449136
  have hstable : (prefixWord ++ tailWord_7449136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449136).length < 2 ^ (prefixWord ++ tailWord_7449136).sum := by decide
  have hdescent : baseEnd_7449136 < baseStart_7449136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449166 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_7449166 : Nat := 118140960795 + 7449166 * 2 ^ 59
def prefixEnd_7449166 : Nat := 4983230072969 + 3 ^ 40 * 7449166 * 2
def baseEnd_7449166 : Nat := 3825002633130107337466915

theorem tailTrace_7449166 : CollatzResearch.WordTrace tailWord_7449166 prefixEnd_7449166 3825002633130107337466915 := by
  unfold tailWord_7449166
  simp only [CollatzResearch.WordTrace]
  refine ⟨33961675566368909138949919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181128936353967515407732901 33961675566368909138949919)
  ·
    refine ⟨50942513349553363708424879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33961675566368909138949919 50942513349553363708424879)
    ·
      refine ⟨76413770024330045562637319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50942513349553363708424879 76413770024330045562637319)
      ·
        refine ⟨114620655036495068343955979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76413770024330045562637319 114620655036495068343955979)
        ·
          refine ⟨171930982554742602515933969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114620655036495068343955979 171930982554742602515933969)
          ·
            refine ⟨128948236916056951886950477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171930982554742602515933969 128948236916056951886950477)
            ·
              refine ⟨48355588843521356957606429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128948236916056951886950477 48355588843521356957606429)
              ·
                refine ⟨18133345816320508859102411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48355588843521356957606429 18133345816320508859102411)
                ·
                  refine ⟨27200018724480763288653617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18133345816320508859102411 27200018724480763288653617)
                  ·
                    refine ⟨20400014043360572466490213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27200018724480763288653617 20400014043360572466490213)
                    ·
                      refine ⟨3825002633130107337466915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20400014043360572466490213 3825002633130107337466915)
                      ·
                        rfl

theorem cell23_7449166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_7449166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449166 prefixEnd_7449166 := by exact prefixLift 7449166
  have htrace : WordTrace (prefixWord ++ tailWord_7449166) baseStart_7449166 baseEnd_7449166 := by
    simpa [prefixWord, tailWord_7449166, baseEnd_7449166] using wordTrace_append hprefix tailTrace_7449166
  have hstable : (prefixWord ++ tailWord_7449166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449166).length < 2 ^ (prefixWord ++ tailWord_7449166).sum := by decide
  have hdescent : baseEnd_7449166 < baseStart_7449166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449170 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 3, 2, 2]
def baseStart_7449170 : Nat := 118140960795 + 7449170 * 2 ^ 59
def prefixEnd_7449170 : Nat := 4983230072969 + 3 ^ 40 * 7449170 * 2
def baseEnd_7449170 : Nat := 3825004687052725321816897

theorem tailTrace_7449170 : CollatzResearch.WordTrace tailWord_7449170 prefixEnd_7449170 3825004687052725321816897 := by
  unfold tailWord_7449170
  simp only [CollatzResearch.WordTrace]
  refine ⟨67923387605734195448686241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181129033615291187863163309 67923387605734195448686241)
  ·
    refine ⟨50942540704300646586514681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67923387605734195448686241 50942540704300646586514681)
    ·
      refine ⟨38206905528225484939886011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50942540704300646586514681 38206905528225484939886011)
      ·
        refine ⟨57310358292338227409829017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38206905528225484939886011 57310358292338227409829017)
        ·
          refine ⟨42982768719253670557371763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57310358292338227409829017 42982768719253670557371763)
          ·
            refine ⟨64474153078880505836057645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42982768719253670557371763 64474153078880505836057645)
            ·
              refine ⟨24177807404580189688521617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64474153078880505836057645 24177807404580189688521617)
              ·
                refine ⟨18133355553435142266391213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24177807404580189688521617 18133355553435142266391213)
                ·
                  refine ⟨6800008332538178349896705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18133355553435142266391213 6800008332538178349896705)
                  ·
                    refine ⟨5100006249403633762422529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6800008332538178349896705 5100006249403633762422529)
                    ·
                      refine ⟨3825004687052725321816897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100006249403633762422529 3825004687052725321816897)
                      ·
                        rfl

theorem cell23_7449170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_7449170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449170 prefixEnd_7449170 := by exact prefixLift 7449170
  have htrace : WordTrace (prefixWord ++ tailWord_7449170) baseStart_7449170 baseEnd_7449170 := by
    simpa [prefixWord, tailWord_7449170, baseEnd_7449170] using wordTrace_append hprefix tailTrace_7449170
  have hstable : (prefixWord ++ tailWord_7449170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449170).length < 2 ^ (prefixWord ++ tailWord_7449170).sum := by decide
  have hdescent : baseEnd_7449170 < baseStart_7449170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449187 : List Nat := [1, 1, 1, 5, 1, 2, 4, 3, 1, 2, 2]
def baseStart_7449187 : Nat := 118140960795 + 7449187 * 2 ^ 59
def prefixEnd_7449187 : Nat := 4983230072969 + 3 ^ 40 * 7449187 * 2
def baseEnd_7449187 : Nat := 3825013416223851755304319

theorem tailTrace_7449187 : CollatzResearch.WordTrace tailWord_7449187 prefixEnd_7449187 3825013416223851755304319 := by
  unfold tailWord_7449187
  simp only [CollatzResearch.WordTrace]
  refine ⟨271694170463875193698113815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181129446975916795798742543 271694170463875193698113815)
  ·
    refine ⟨407541255695812790547170723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271694170463875193698113815 407541255695812790547170723)
    ·
      refine ⟨611311883543719185820756085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407541255695812790547170723 611311883543719185820756085)
      ·
        refine ⟨57310489082223673670695883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 611311883543719185820756085 57310489082223673670695883)
        ·
          refine ⟨85965733623335510506043825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57310489082223673670695883 85965733623335510506043825)
          ·
            refine ⟨64474300217501632879532869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85965733623335510506043825 64474300217501632879532869)
            ·
              refine ⟨12088931290781556164912413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64474300217501632879532869 12088931290781556164912413)
              ·
                refine ⟨4533349234043083561842155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12088931290781556164912413 4533349234043083561842155)
                ·
                  refine ⟨6800023851064625342763233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533349234043083561842155 6800023851064625342763233)
                  ·
                    refine ⟨5100017888298469007072425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6800023851064625342763233 5100017888298469007072425)
                    ·
                      refine ⟨3825013416223851755304319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100017888298469007072425 3825013416223851755304319)
                      ·
                        rfl

theorem cell23_7449187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_7449187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449187 prefixEnd_7449187 := by exact prefixLift 7449187
  have htrace : WordTrace (prefixWord ++ tailWord_7449187) baseStart_7449187 baseEnd_7449187 := by
    simpa [prefixWord, tailWord_7449187, baseEnd_7449187] using wordTrace_append hprefix tailTrace_7449187
  have hstable : (prefixWord ++ tailWord_7449187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449187).length < 2 ^ (prefixWord ++ tailWord_7449187).sum := by decide
  have hdescent : baseEnd_7449187 < baseStart_7449187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449203 : List Nat := [1, 1, 1, 2, 2, 1, 1, 8, 2, 1, 3]
def baseStart_7449203 : Nat := 118140960795 + 7449203 * 2 ^ 59
def prefixEnd_7449203 : Nat := 4983230072969 + 3 ^ 40 * 7449203 * 2
def baseEnd_7449203 : Nat := 3825021631914323692704245

theorem tailTrace_7449203 : CollatzResearch.WordTrace tailWord_7449203 prefixEnd_7449203 3825021631914323692704245 := by
  unfold tailWord_7449203
  simp only [CollatzResearch.WordTrace]
  refine ⟨271694754031817228430696263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181129836021211485620464175 271694754031817228430696263)
  ·
    refine ⟨407542131047725842646044395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271694754031817228430696263 407542131047725842646044395)
    ·
      refine ⟨611313196571588763969066593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407542131047725842646044395 611313196571588763969066593)
      ·
        refine ⟨458484897428691572976799945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 611313196571588763969066593 458484897428691572976799945)
        ·
          refine ⟨343863673071518679732599959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458484897428691572976799945 343863673071518679732599959)
          ·
            refine ⟨515795509607278019598899939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343863673071518679732599959 515795509607278019598899939)
            ·
              refine ⟨773693264410917029398349909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515795509607278019598899939 773693264410917029398349909)
              ·
                refine ⟨9066717942315433938261913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 773693264410917029398349909 9066717942315433938261913)
                ·
                  refine ⟨6800038456736575453696435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9066717942315433938261913 6800038456736575453696435)
                  ·
                    refine ⟨10200057685104863180544653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6800038456736575453696435 10200057685104863180544653)
                    ·
                      refine ⟨3825021631914323692704245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10200057685104863180544653 3825021631914323692704245)
                      ·
                        rfl

theorem cell23_7449203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 1, 3].length) (baseStart_7449203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449203 prefixEnd_7449203 := by exact prefixLift 7449203
  have htrace : WordTrace (prefixWord ++ tailWord_7449203) baseStart_7449203 baseEnd_7449203 := by
    simpa [prefixWord, tailWord_7449203, baseEnd_7449203] using wordTrace_append hprefix tailTrace_7449203
  have hstable : (prefixWord ++ tailWord_7449203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449203).length < 2 ^ (prefixWord ++ tailWord_7449203).sum := by decide
  have hdescent : baseEnd_7449203 < baseStart_7449203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449220 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_7449220 : Nat := 118140960795 + 7449220 * 2 ^ 59
def prefixEnd_7449220 : Nat := 4983230072969 + 3 ^ 40 * 7449220 * 2
def baseEnd_7449220 : Nat := 3825030361085450126191667

theorem tailTrace_7449220 : CollatzResearch.WordTrace tailWord_7449220 prefixEnd_7449220 3825030361085450126191667 := by
  unfold tailWord_7449220
  simp only [CollatzResearch.WordTrace]
  refine ⟨135847687036377820167032557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181130249381837093556043409 135847687036377820167032557)
  ·
    refine ⟨50942882638641682562637209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135847687036377820167032557 50942882638641682562637209)
    ·
      refine ⟨38207161978981261921977907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50942882638641682562637209 38207161978981261921977907)
      ·
        refine ⟨57310742968471892882966861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38207161978981261921977907 57310742968471892882966861)
        ·
          refine ⟨21491528613176959831112573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57310742968471892882966861 21491528613176959831112573)
          ·
            refine ⟨8059323229941359936667215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21491528613176959831112573 8059323229941359936667215)
            ·
              refine ⟨12088984844912039905000823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8059323229941359936667215 12088984844912039905000823)
              ·
                refine ⟨18133477267368059857501235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12088984844912039905000823 18133477267368059857501235)
                ·
                  refine ⟨27200215901052089786251853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18133477267368059857501235 27200215901052089786251853)
                  ·
                    refine ⟨10200080962894533669844445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27200215901052089786251853 10200080962894533669844445)
                    ·
                      refine ⟨3825030361085450126191667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10200080962894533669844445 3825030361085450126191667)
                      ·
                        rfl

theorem cell23_7449220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_7449220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449220 prefixEnd_7449220 := by exact prefixLift 7449220
  have htrace : WordTrace (prefixWord ++ tailWord_7449220) baseStart_7449220 baseEnd_7449220 := by
    simpa [prefixWord, tailWord_7449220, baseEnd_7449220] using wordTrace_append hprefix tailTrace_7449220
  have hstable : (prefixWord ++ tailWord_7449220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449220).length < 2 ^ (prefixWord ++ tailWord_7449220).sum := by decide
  have hdescent : baseEnd_7449220 < baseStart_7449220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449277 : List Nat := [1, 4, 1, 2, 1, 4, 1, 3, 2, 2, 2]
def baseStart_7449277 : Nat := 118140960795 + 7449277 * 2 ^ 59
def prefixEnd_7449277 : Nat := 4983230072969 + 3 ^ 40 * 7449277 * 2
def baseEnd_7449277 : Nat := 3825059629482756403178905

theorem tailTrace_7449277 : CollatzResearch.WordTrace tailWord_7449277 prefixEnd_7449277 3825059629482756403178905 := by
  unfold tailWord_7449277
  simp only [CollatzResearch.WordTrace]
  refine ⟨271697453033549139068890085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181131635355699426045926723 271697453033549139068890085)
  ·
    refine ⟨50943272443790463575416891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271697453033549139068890085 50943272443790463575416891)
    ·
      refine ⟨76414908665685695363125337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50943272443790463575416891 76414908665685695363125337)
      ·
        refine ⟨57311181499264271522344003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76414908665685695363125337 57311181499264271522344003)
        ·
          refine ⟨85966772248896407283516005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57311181499264271522344003 85966772248896407283516005)
          ·
            refine ⟨16118769796668076365659251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85966772248896407283516005 16118769796668076365659251)
            ·
              refine ⟨24178154695002114548488877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16118769796668076365659251 24178154695002114548488877)
              ·
                refine ⟨9066808010625792955683329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24178154695002114548488877 9066808010625792955683329)
                ·
                  refine ⟨6800106007969344716762497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9066808010625792955683329 6800106007969344716762497)
                  ·
                    refine ⟨5100079505977008537571873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6800106007969344716762497 5100079505977008537571873)
                    ·
                      refine ⟨3825059629482756403178905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100079505977008537571873 3825059629482756403178905)
                      ·
                        rfl

theorem cell23_7449277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_7449277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449277 prefixEnd_7449277 := by exact prefixLift 7449277
  have htrace : WordTrace (prefixWord ++ tailWord_7449277) baseStart_7449277 baseEnd_7449277 := by
    simpa [prefixWord, tailWord_7449277, baseEnd_7449277] using wordTrace_append hprefix tailTrace_7449277
  have hstable : (prefixWord ++ tailWord_7449277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449277).length < 2 ^ (prefixWord ++ tailWord_7449277).sum := by decide
  have hdescent : baseEnd_7449277 < baseStart_7449277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449281 : List Nat := [1, 2, 6, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_7449281 : Nat := 118140960795 + 7449281 * 2 ^ 59
def prefixEnd_7449281 : Nat := 4983230072969 + 3 ^ 40 * 7449281 * 2
def baseEnd_7449281 : Nat := 3825061683405374387528887

theorem tailTrace_7449281 : CollatzResearch.WordTrace tailWord_7449281 prefixEnd_7449281 3825061683405374387528887 := by
  unfold tailWord_7449281
  simp only [CollatzResearch.WordTrace]
  refine ⟨271697598925534647752035697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181131732617023098501357131 271697598925534647752035697)
  ·
    refine ⟨203773199194150985814026773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271697598925534647752035697 203773199194150985814026773)
    ·
      refine ⟨9551868712225827460032505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 203773199194150985814026773 9551868712225827460032505)
      ·
        refine ⟨7163901534169370595024379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9551868712225827460032505 7163901534169370595024379)
        ·
          refine ⟨10745852301254055892536569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7163901534169370595024379 10745852301254055892536569)
          ·
            refine ⟨8059389225940541919402427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10745852301254055892536569 8059389225940541919402427)
            ·
              refine ⟨12089083838910812879103641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8059389225940541919402427 12089083838910812879103641)
              ·
                refine ⟨9066812879183109659327731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12089083838910812879103641 9066812879183109659327731)
                ·
                  refine ⟨13600219318774664488991597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9066812879183109659327731 13600219318774664488991597)
                  ·
                    refine ⟨5100082244540499183371849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13600219318774664488991597 5100082244540499183371849)
                    ·
                      refine ⟨3825061683405374387528887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100082244540499183371849 3825061683405374387528887)
                      ·
                        rfl

theorem cell23_7449281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_7449281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449281 prefixEnd_7449281 := by exact prefixLift 7449281
  have htrace : WordTrace (prefixWord ++ tailWord_7449281) baseStart_7449281 baseEnd_7449281 := by
    simpa [prefixWord, tailWord_7449281, baseEnd_7449281] using wordTrace_append hprefix tailTrace_7449281
  have hstable : (prefixWord ++ tailWord_7449281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449281).length < 2 ^ (prefixWord ++ tailWord_7449281).sum := by decide
  have hdescent : baseEnd_7449281 < baseStart_7449281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449306 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5]
def baseStart_7449306 : Nat := 118140960795 + 7449306 * 2 ^ 59
def prefixEnd_7449306 : Nat := 4983230072969 + 3 ^ 40 * 7449306 * 2
def baseEnd_7449306 : Nat := 3825074520421736789716271

theorem tailTrace_7449306 : CollatzResearch.WordTrace tailWord_7449306 prefixEnd_7449306 3825074520421736789716271 := by
  unfold tailWord_7449306
  simp only [CollatzResearch.WordTrace]
  refine ⟨67924627687611019255423943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181132340500296051347797181 67924627687611019255423943)
  ·
    refine ⟨101886941531416528883135915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67924627687611019255423943 101886941531416528883135915)
    ·
      refine ⟨152830412297124793324703873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101886941531416528883135915 152830412297124793324703873)
      ·
        refine ⟨114622809222843594993527905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152830412297124793324703873 114622809222843594993527905)
        ·
          refine ⟨85967106917132696245145929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114622809222843594993527905 85967106917132696245145929)
          ·
            refine ⟨64475330187849522183859447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85967106917132696245145929 64475330187849522183859447)
            ·
              refine ⟨96712995281774283275789171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64475330187849522183859447 96712995281774283275789171)
              ·
                refine ⟨145069492922661424913683757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96712995281774283275789171 145069492922661424913683757)
                ·
                  refine ⟨54401059845998034342631409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145069492922661424913683757 54401059845998034342631409)
                  ·
                    refine ⟨40800794884498525756973557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54401059845998034342631409 40800794884498525756973557)
                    ·
                      refine ⟨3825074520421736789716271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40800794884498525756973557 3825074520421736789716271)
                      ·
                        rfl

theorem cell23_7449306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_7449306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449306 prefixEnd_7449306 := by exact prefixLift 7449306
  have htrace : WordTrace (prefixWord ++ tailWord_7449306) baseStart_7449306 baseEnd_7449306 := by
    simpa [prefixWord, tailWord_7449306, baseEnd_7449306] using wordTrace_append hprefix tailTrace_7449306
  have hstable : (prefixWord ++ tailWord_7449306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449306).length < 2 ^ (prefixWord ++ tailWord_7449306).sum := by decide
  have hdescent : baseEnd_7449306 < baseStart_7449306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449313 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 2, 5]
def baseStart_7449313 : Nat := 118140960795 + 7449313 * 2 ^ 59
def prefixEnd_7449313 : Nat := 4983230072969 + 3 ^ 40 * 7449313 * 2
def baseEnd_7449313 : Nat := 1275026038262106087442913

theorem tailTrace_7449313 : CollatzResearch.WordTrace tailWord_7449313 prefixEnd_7449313 1275026038262106087442913 := by
  unfold tailWord_7449313
  simp only [CollatzResearch.WordTrace]
  refine ⟨271698766061418717217200593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181132510707612478144800395 271698766061418717217200593)
  ·
    refine ⟨203774074546064037912900445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271698766061418717217200593 203774074546064037912900445)
    ·
      refine ⟨76415277954774014217337667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203774074546064037912900445 76415277954774014217337667)
      ·
        refine ⟨114622916932161021326006501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76415277954774014217337667 114622916932161021326006501)
        ·
          refine ⟨21491796924780191498626219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114622916932161021326006501 21491796924780191498626219)
          ·
            refine ⟨32237695387170287247939329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21491796924780191498626219 32237695387170287247939329)
            ·
              refine ⟨24178271540377715435954497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32237695387170287247939329 24178271540377715435954497)
              ·
                refine ⟨18133703655283286576965873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24178271540377715435954497 18133703655283286576965873)
                ·
                  refine ⟨13600277741462464932724405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18133703655283286576965873 13600277741462464932724405)
                  ·
                    refine ⟨1275026038262106087442913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13600277741462464932724405 1275026038262106087442913)
                    ·
                      rfl

theorem cell23_7449313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_7449313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449313 prefixEnd_7449313 := by exact prefixLift 7449313
  have htrace : WordTrace (prefixWord ++ tailWord_7449313) baseStart_7449313 baseEnd_7449313 := by
    simpa [prefixWord, tailWord_7449313, baseEnd_7449313] using wordTrace_append hprefix tailTrace_7449313
  have hstable : (prefixWord ++ tailWord_7449313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449313).length < 2 ^ (prefixWord ++ tailWord_7449313).sum := by decide
  have hdescent : baseEnd_7449313 < baseStart_7449313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449317 : List Nat := [1, 3, 1, 4, 1, 4, 2, 2, 5]
def baseStart_7449317 : Nat := 118140960795 + 7449317 * 2 ^ 59
def prefixEnd_7449317 : Nat := 4983230072969 + 3 ^ 40 * 7449317 * 2
def baseEnd_7449317 : Nat := 425008907634326249630969

theorem tailTrace_7449317 : CollatzResearch.WordTrace tailWord_7449317 prefixEnd_7449317 425008907634326249630969 := by
  unfold tailWord_7449317
  simp only [CollatzResearch.WordTrace]
  refine ⟨271698911953404225900346205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181132607968936150600230803 271698911953404225900346205)
  ·
    refine ⟨101887091982526584712629827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271698911953404225900346205 101887091982526584712629827)
    ·
      refine ⟨152830637973789877068944741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101887091982526584712629827 152830637973789877068944741)
      ·
        refine ⟨28655744620085601950427139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152830637973789877068944741 28655744620085601950427139)
        ·
          refine ⟨42983616930128402925640709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28655744620085601950427139 42983616930128402925640709)
          ·
            refine ⟨8059428174399075548557633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42983616930128402925640709 8059428174399075548557633)
            ·
              refine ⟨6044571130799306661418225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8059428174399075548557633 6044571130799306661418225)
              ·
                refine ⟨4533428348099479996063669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6044571130799306661418225 4533428348099479996063669)
                ·
                  refine ⟨425008907634326249630969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4533428348099479996063669 425008907634326249630969)
                  ·
                    rfl

theorem cell23_7449317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 5].length) (baseStart_7449317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449317 prefixEnd_7449317 := by exact prefixLift 7449317
  have htrace : WordTrace (prefixWord ++ tailWord_7449317) baseStart_7449317 baseEnd_7449317 := by
    simpa [prefixWord, tailWord_7449317, baseEnd_7449317] using wordTrace_append hprefix tailTrace_7449317
  have hstable : (prefixWord ++ tailWord_7449317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449317).length < 2 ^ (prefixWord ++ tailWord_7449317).sum := by decide
  have hdescent : baseEnd_7449317 < baseStart_7449317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449356 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 8]
def baseStart_7449356 : Nat := 118140960795 + 7449356 * 2 ^ 59
def prefixEnd_7449356 : Nat := 4983230072969 + 3 ^ 40 * 7449356 * 2
def baseEnd_7449356 : Nat := 425011132717162399343449

theorem tailTrace_7449356 : CollatzResearch.WordTrace tailWord_7449356 prefixEnd_7449356 425011132717162399343449 := by
  unfold tailWord_7449356
  simp only [CollatzResearch.WordTrace]
  refine ⟨135850167200131467780507961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181133556266841957040677281 135850167200131467780507961)
  ·
    refine ⟨101887625400098600835380971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135850167200131467780507961 101887625400098600835380971)
    ·
      refine ⟨152831438100147901253071457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101887625400098600835380971 152831438100147901253071457)
      ·
        refine ⟨114623578575110925939803593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152831438100147901253071457 114623578575110925939803593)
        ·
          refine ⟨85967683931333194454852695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114623578575110925939803593 85967683931333194454852695)
          ·
            refine ⟨128951525896999791682279043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85967683931333194454852695 128951525896999791682279043)
            ·
              refine ⟨193427288845499687523418565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128951525896999791682279043 193427288845499687523418565)
              ·
                refine ⟨36267616658531191410640981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193427288845499687523418565 36267616658531191410640981)
                ·
                  refine ⟨425011132717162399343449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36267616658531191410640981 425011132717162399343449)
                  ·
                    rfl

theorem cell23_7449356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 8].length) (baseStart_7449356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449356 prefixEnd_7449356 := by exact prefixLift 7449356
  have htrace : WordTrace (prefixWord ++ tailWord_7449356) baseStart_7449356 baseEnd_7449356 := by
    simpa [prefixWord, tailWord_7449356, baseEnd_7449356] using wordTrace_append hprefix tailTrace_7449356
  have hstable : (prefixWord ++ tailWord_7449356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449356).length < 2 ^ (prefixWord ++ tailWord_7449356).sum := by decide
  have hdescent : baseEnd_7449356 < baseStart_7449356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449400 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 3, 1, 3]
def baseStart_7449400 : Nat := 118140960795 + 7449400 * 2 ^ 59
def prefixEnd_7449400 : Nat := 4983230072969 + 3 ^ 40 * 7449400 * 2
def baseEnd_7449400 : Nat := 3825122787603259421940839

theorem tailTrace_7449400 : CollatzResearch.WordTrace tailWord_7449400 prefixEnd_7449400 3825122787603259421940839 := by
  unfold tailWord_7449400
  simp only [CollatzResearch.WordTrace]
  refine ⟨135850969606051765537808827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181134626141402354050411769 135850969606051765537808827)
  ·
    refine ⟨203776454409077648306713241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135850969606051765537808827 203776454409077648306713241)
    ·
      refine ⟨152832340806808236230034931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203776454409077648306713241 152832340806808236230034931)
      ·
        refine ⟨229248511210212354345052397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152832340806808236230034931 229248511210212354345052397)
        ·
          refine ⟨85968191703829632879394649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229248511210212354345052397 85968191703829632879394649)
          ·
            refine ⟨64476143777872224659545987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85968191703829632879394649 64476143777872224659545987)
            ·
              refine ⟨96714215666808336989318981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64476143777872224659545987 96714215666808336989318981)
              ·
                refine ⟨18133915437526563185497309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96714215666808336989318981 18133915437526563185497309)
                ·
                  refine ⟨6800218289072461194561491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18133915437526563185497309 6800218289072461194561491)
                  ·
                    refine ⟨10200327433608691791842237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6800218289072461194561491 10200327433608691791842237)
                    ·
                      refine ⟨3825122787603259421940839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10200327433608691791842237 3825122787603259421940839)
                      ·
                        rfl

theorem cell23_7449400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 3, 1, 3].length) (baseStart_7449400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449400 prefixEnd_7449400 := by exact prefixLift 7449400
  have htrace : WordTrace (prefixWord ++ tailWord_7449400) baseStart_7449400 baseEnd_7449400 := by
    simpa [prefixWord, tailWord_7449400, baseEnd_7449400] using wordTrace_append hprefix tailTrace_7449400
  have hstable : (prefixWord ++ tailWord_7449400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449400).length < 2 ^ (prefixWord ++ tailWord_7449400).sum := by decide
  have hdescent : baseEnd_7449400 < baseStart_7449400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449420 : List Nat := [2, 2, 1, 3, 3, 1, 2, 3, 1, 5]
def baseStart_7449420 : Nat := 118140960795 + 7449420 * 2 ^ 59
def prefixEnd_7449420 : Nat := 4983230072969 + 3 ^ 40 * 7449420 * 2
def baseEnd_7449420 : Nat := 1275044352405449781230249

theorem tailTrace_7449420 : CollatzResearch.WordTrace tailWord_7449420 prefixEnd_7449420 1275044352405449781230249 := by
  unfold tailWord_7449420
  simp only [CollatzResearch.WordTrace]
  refine ⟨135851334336015537245672857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181135112448020716327563809 135851334336015537245672857)
  ·
    refine ⟨101888500752011652934254643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135851334336015537245672857 101888500752011652934254643)
    ·
      refine ⟨152832751128017479401381965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101888500752011652934254643 152832751128017479401381965)
      ·
        refine ⟨57312281673006554775518237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152832751128017479401381965 57312281673006554775518237)
        ·
          refine ⟨21492105627377458040819339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57312281673006554775518237 21492105627377458040819339)
          ·
            refine ⟨32238158441066187061229009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21492105627377458040819339 32238158441066187061229009)
            ·
              refine ⟨24178618830799640295921757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32238158441066187061229009 24178618830799640295921757)
              ·
                refine ⟨9066982061549865110970659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24178618830799640295921757 9066982061549865110970659)
                ·
                  refine ⟨13600473092324797666455989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9066982061549865110970659 13600473092324797666455989)
                  ·
                    refine ⟨1275044352405449781230249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13600473092324797666455989 1275044352405449781230249)
                    ·
                      rfl

theorem cell23_7449420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_7449420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449420 prefixEnd_7449420 := by exact prefixLift 7449420
  have htrace : WordTrace (prefixWord ++ tailWord_7449420) baseStart_7449420 baseEnd_7449420 := by
    simpa [prefixWord, tailWord_7449420, baseEnd_7449420] using wordTrace_append hprefix tailTrace_7449420
  have hstable : (prefixWord ++ tailWord_7449420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449420).length < 2 ^ (prefixWord ++ tailWord_7449420).sum := by decide
  have hdescent : baseEnd_7449420 < baseStart_7449420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449454 : List Nat := [4, 1, 2, 3, 2, 2, 1, 2, 1, 5]
def baseStart_7449454 : Nat := 118140960795 + 7449454 * 2 ^ 59
def prefixEnd_7449454 : Nat := 4983230072969 + 3 ^ 40 * 7449454 * 2
def baseEnd_7449454 : Nat := 1275050171852867403555197

theorem tailTrace_7449454 : CollatzResearch.WordTrace tailWord_7449454 prefixEnd_7449454 1275050171852867403555197 := by
  unfold tailWord_7449454
  simp only [CollatzResearch.WordTrace]
  refine ⟨33962988594238487287260427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181135939169271932198722277 33962988594238487287260427)
  ·
    refine ⟨50944482891357730930890641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33962988594238487287260427 50944482891357730930890641)
    ·
      refine ⟨38208362168518298198167981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50944482891357730930890641 38208362168518298198167981)
      ·
        refine ⟨14328135813194361824312993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38208362168518298198167981 14328135813194361824312993)
        ·
          refine ⟨10746101859895771368234745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14328135813194361824312993 10746101859895771368234745)
          ·
            refine ⟨8059576394921828526176059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10746101859895771368234745 8059576394921828526176059)
            ·
              refine ⟨12089364592382742789264089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8059576394921828526176059 12089364592382742789264089)
              ·
                refine ⟨9067023444287057091948067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12089364592382742789264089 9067023444287057091948067)
                ·
                  refine ⟨13600535166430585637922101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9067023444287057091948067 13600535166430585637922101)
                  ·
                    refine ⟨1275050171852867403555197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13600535166430585637922101 1275050171852867403555197)
                    ·
                      rfl

theorem cell23_7449454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_7449454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449454 prefixEnd_7449454 := by exact prefixLift 7449454
  have htrace : WordTrace (prefixWord ++ tailWord_7449454) baseStart_7449454 baseEnd_7449454 := by
    simpa [prefixWord, tailWord_7449454, baseEnd_7449454] using wordTrace_append hprefix tailTrace_7449454
  have hstable : (prefixWord ++ tailWord_7449454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449454).length < 2 ^ (prefixWord ++ tailWord_7449454).sum := by decide
  have hdescent : baseEnd_7449454 < baseStart_7449454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449457 : List Nat := [1, 2, 2, 2, 1, 6, 1, 2, 1, 1, 4]
def baseStart_7449457 : Nat := 118140960795 + 7449457 * 2 ^ 59
def prefixEnd_7449457 : Nat := 4983230072969 + 3 ^ 40 * 7449457 * 2
def baseEnd_7449457 : Nat := 3825152056000565698928077

theorem tailTrace_7449457 : CollatzResearch.WordTrace tailWord_7449457 prefixEnd_7449457 3825152056000565698928077 := by
  unfold tailWord_7449457
  simp only [CollatzResearch.WordTrace]
  refine ⟨271704018172897029810442625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181136012115264686540295083 271704018172897029810442625)
  ·
    refine ⟨203778013629672772357831969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271704018172897029810442625 203778013629672772357831969)
    ·
      refine ⟨152833510222254579268373977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203778013629672772357831969 152833510222254579268373977)
      ·
        refine ⟨114625132666690934451280483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152833510222254579268373977 114625132666690934451280483)
        ·
          refine ⟨171937699000036401676920725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114625132666690934451280483 171937699000036401676920725)
          ·
            refine ⟨8059579640626706328605659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171937699000036401676920725 8059579640626706328605659)
            ·
              refine ⟨12089369460940059492908489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8059579640626706328605659 12089369460940059492908489)
              ·
                refine ⟨9067027095705044619681367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12089369460940059492908489 9067027095705044619681367)
                ·
                  refine ⟨13600540643557566929522051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9067027095705044619681367 13600540643557566929522051)
                  ·
                    refine ⟨20400810965336350394283077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13600540643557566929522051 20400810965336350394283077)
                    ·
                      refine ⟨3825152056000565698928077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20400810965336350394283077 3825152056000565698928077)
                      ·
                        rfl

theorem cell23_7449457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_7449457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449457 prefixEnd_7449457 := by exact prefixLift 7449457
  have htrace : WordTrace (prefixWord ++ tailWord_7449457) baseStart_7449457 baseEnd_7449457 := by
    simpa [prefixWord, tailWord_7449457, baseEnd_7449457] using wordTrace_append hprefix tailTrace_7449457
  have hstable : (prefixWord ++ tailWord_7449457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449457).length < 2 ^ (prefixWord ++ tailWord_7449457).sum := by decide
  have hdescent : baseEnd_7449457 < baseStart_7449457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449493 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 2, 7]
def baseStart_7449493 : Nat := 118140960795 + 7449493 * 2 ^ 59
def prefixEnd_7449493 : Nat := 4983230072969 + 3 ^ 40 * 7449493 * 2
def baseEnd_7449493 : Nat := 1275056847101375852692637

theorem tailTrace_7449493 : CollatzResearch.WordTrace tailWord_7449493 prefixEnd_7449493 1275056847101375852692637 := by
  unfold tailWord_7449493
  simp only [CollatzResearch.WordTrace]
  refine ⟨271705331200766607958753133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181136887467177738639168755 271705331200766607958753133)
  ·
    refine ⟨101889499200287477984532425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271705331200766607958753133 101889499200287477984532425)
    ·
      refine ⟨76417124400215608488399319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101889499200287477984532425 76417124400215608488399319)
      ·
        refine ⟨114625686600323412732598979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76417124400215608488399319 114625686600323412732598979)
        ·
          refine ⟨171938529900485119098898469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114625686600323412732598979 171938529900485119098898469)
          ·
            refine ⟨32238474356340959831043463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171938529900485119098898469 32238474356340959831043463)
            ·
              refine ⟨48357711534511439746565195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32238474356340959831043463 48357711534511439746565195)
              ·
                refine ⟨72536567301767159619847793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48357711534511439746565195 72536567301767159619847793)
                ·
                  refine ⟨54402425476325369714885845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72536567301767159619847793 54402425476325369714885845)
                  ·
                    refine ⟨1275056847101375852692637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54402425476325369714885845 1275056847101375852692637)
                    ·
                      rfl

theorem cell23_7449493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_7449493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449493 prefixEnd_7449493 := by exact prefixLift 7449493
  have htrace : WordTrace (prefixWord ++ tailWord_7449493) baseStart_7449493 baseEnd_7449493 := by
    simpa [prefixWord, tailWord_7449493, baseEnd_7449493] using wordTrace_append hprefix tailTrace_7449493
  have hstable : (prefixWord ++ tailWord_7449493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449493).length < 2 ^ (prefixWord ++ tailWord_7449493).sum := by decide
  have hdescent : baseEnd_7449493 < baseStart_7449493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449507 : List Nat := [1, 1, 1, 4, 1, 2, 4, 3, 2, 1, 3]
def baseStart_7449507 : Nat := 118140960795 + 7449507 * 2 ^ 59
def prefixEnd_7449507 : Nat := 4983230072969 + 3 ^ 40 * 7449507 * 2
def baseEnd_7449507 : Nat := 3825177730033290503302847

theorem tailTrace_7449507 : CollatzResearch.WordTrace tailWord_7449507 prefixEnd_7449507 3825177730033290503302847 := by
  unfold tailWord_7449507
  simp only [CollatzResearch.WordTrace]
  refine ⟨271705841822715888349762775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181137227881810592233175183 271705841822715888349762775)
  ·
    refine ⟨407558762734073832524644163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271705841822715888349762775 407558762734073832524644163)
    ·
      refine ⟨611338144101110748786966245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407558762734073832524644163 611338144101110748786966245)
      ·
        refine ⟨114625902018958265397556171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 611338144101110748786966245 114625902018958265397556171)
        ·
          refine ⟨171938853028437398096334257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114625902018958265397556171 171938853028437398096334257)
          ·
            refine ⟨128954139771328048572250693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171938853028437398096334257 128954139771328048572250693)
            ·
              refine ⟨24178901207124009107297005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128954139771328048572250693 24178901207124009107297005)
              ·
                refine ⟨9067087952671503415236377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24178901207124009107297005 9067087952671503415236377)
                ·
                  refine ⟨6800315964503627561427283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9067087952671503415236377 6800315964503627561427283)
                  ·
                    refine ⟨10200473946755441342140925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6800315964503627561427283 10200473946755441342140925)
                    ·
                      refine ⟨3825177730033290503302847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10200473946755441342140925 3825177730033290503302847)
                      ·
                        rfl

theorem cell23_7449507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_7449507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449507 prefixEnd_7449507 := by exact prefixLift 7449507
  have htrace : WordTrace (prefixWord ++ tailWord_7449507) baseStart_7449507 baseEnd_7449507 := by
    simpa [prefixWord, tailWord_7449507, baseEnd_7449507] using wordTrace_append hprefix tailTrace_7449507
  have hstable : (prefixWord ++ tailWord_7449507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449507).length < 2 ^ (prefixWord ++ tailWord_7449507).sum := by decide
  have hdescent : baseEnd_7449507 < baseStart_7449507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449513 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 2, 3, 4]
def baseStart_7449513 : Nat := 118140960795 + 7449513 * 2 ^ 59
def prefixEnd_7449513 : Nat := 4983230072969 + 3 ^ 40 * 7449513 * 2
def baseEnd_7449513 : Nat := 3825180810917217479827819

theorem tailTrace_7449513 : CollatzResearch.WordTrace tailWord_7449513 prefixEnd_7449513 3825180810917217479827819 := by
  unfold tailWord_7449513
  simp only [CollatzResearch.WordTrace]
  refine ⟨271706060660694151374481193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181137373773796100916320795 271706060660694151374481193)
  ·
    refine ⟨203779545495520613530860895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271706060660694151374481193 203779545495520613530860895)
    ·
      refine ⟨305669318243280920296291343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203779545495520613530860895 305669318243280920296291343)
      ·
        refine ⟨458503977364921380444437015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305669318243280920296291343 458503977364921380444437015)
        ·
          refine ⟨687755966047382070666655523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458503977364921380444437015 687755966047382070666655523)
          ·
            refine ⟨1031633949071073105999983285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687755966047382070666655523 1031633949071073105999983285)
            ·
              refine ⟨96715682725413103687498433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1031633949071073105999983285 96715682725413103687498433)
              ·
                refine ⟨72536762044059827765623825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96715682725413103687498433 72536762044059827765623825)
                ·
                  refine ⟨54402571533044870824217869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72536762044059827765623825 54402571533044870824217869)
                  ·
                    refine ⟨20400964324891826559081701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54402571533044870824217869 20400964324891826559081701)
                    ·
                      refine ⟨3825180810917217479827819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20400964324891826559081701 3825180810917217479827819)
                      ·
                        rfl

theorem cell23_7449513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_7449513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449513 prefixEnd_7449513 := by exact prefixLift 7449513
  have htrace : WordTrace (prefixWord ++ tailWord_7449513) baseStart_7449513 baseEnd_7449513 := by
    simpa [prefixWord, tailWord_7449513, baseEnd_7449513] using wordTrace_append hprefix tailTrace_7449513
  have hstable : (prefixWord ++ tailWord_7449513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449513).length < 2 ^ (prefixWord ++ tailWord_7449513).sum := by decide
  have hdescent : baseEnd_7449513 < baseStart_7449513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449524 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_7449524 : Nat := 118140960795 + 7449524 * 2 ^ 59
def prefixEnd_7449524 : Nat := 4983230072969 + 3 ^ 40 * 7449524 * 2
def baseEnd_7449524 : Nat := 3825186459204416936790269

theorem tailTrace_7449524 : CollatzResearch.WordTrace tailWord_7449524 prefixEnd_7449524 3825186459204416936790269 := by
  unfold tailWord_7449524
  simp only [CollatzResearch.WordTrace]
  refine ⟨135853230931827150126565813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181137641242436200168754417 135853230931827150126565813)
  ·
    refine ⟨12736240399858795324365545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135853230931827150126565813 12736240399858795324365545)
    ·
      refine ⟨9552180299894096493274159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12736240399858795324365545 9552180299894096493274159)
      ·
        refine ⟨14328270449841144739911239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9552180299894096493274159 14328270449841144739911239)
        ·
          refine ⟨21492405674761717109866859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14328270449841144739911239 21492405674761717109866859)
          ·
            refine ⟨32238608512142575664800289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21492405674761717109866859 32238608512142575664800289)
            ·
              refine ⟨24178956384106931748600217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32238608512142575664800289 24178956384106931748600217)
              ·
                refine ⟨18134217288080198811450163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24178956384106931748600217 18134217288080198811450163)
                ·
                  refine ⟨27201325932120298217175245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18134217288080198811450163 27201325932120298217175245)
                  ·
                    refine ⟨10200497224545111831440717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27201325932120298217175245 10200497224545111831440717)
                    ·
                      refine ⟨3825186459204416936790269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10200497224545111831440717 3825186459204416936790269)
                      ·
                        rfl

theorem cell23_7449524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_7449524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449524 prefixEnd_7449524 := by exact prefixLift 7449524
  have htrace : WordTrace (prefixWord ++ tailWord_7449524) baseStart_7449524 baseEnd_7449524 := by
    simpa [prefixWord, tailWord_7449524, baseEnd_7449524] using wordTrace_append hprefix tailTrace_7449524
  have hstable : (prefixWord ++ tailWord_7449524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449524).length < 2 ^ (prefixWord ++ tailWord_7449524).sum := by decide
  have hdescent : baseEnd_7449524 < baseStart_7449524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449534 : List Nat := [4, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2]
def baseStart_7449534 : Nat := 118140960795 + 7449534 * 2 ^ 59
def prefixEnd_7449534 : Nat := 4983230072969 + 3 ^ 40 * 7449534 * 2
def baseEnd_7449534 : Nat := 3825191594010961897665223

theorem tailTrace_7449534 : CollatzResearch.WordTrace tailWord_7449534 prefixEnd_7449534 3825191594010961897665223 := by
  unfold tailWord_7449534
  simp only [CollatzResearch.WordTrace]
  refine ⟨33963353324202258995124457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181137884395745381307330437 33963353324202258995124457)
  ·
    refine ⟨25472514993151694246343343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33963353324202258995124457 25472514993151694246343343)
    ·
      refine ⟨38208772489727541369515015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25472514993151694246343343 38208772489727541369515015)
      ·
        refine ⟨57313158734591312054272523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38208772489727541369515015 57313158734591312054272523)
        ·
          refine ⟨85969738101886968081408785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57313158734591312054272523 85969738101886968081408785)
          ·
            refine ⟨64477303576415226061056589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85969738101886968081408785 64477303576415226061056589)
            ·
              refine ⟨24178988841155709772896221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64477303576415226061056589 24178988841155709772896221)
              ·
                refine ⟨9067120815433391164836083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24178988841155709772896221 9067120815433391164836083)
                ·
                  refine ⟨13600681223150086747254125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9067120815433391164836083 13600681223150086747254125)
                  ·
                    refine ⟨5100255458681282530220297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13600681223150086747254125 5100255458681282530220297)
                    ·
                      refine ⟨3825191594010961897665223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100255458681282530220297 3825191594010961897665223)
                      ·
                        rfl

theorem cell23_7449534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_7449534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449534 prefixEnd_7449534 := by exact prefixLift 7449534
  have htrace : WordTrace (prefixWord ++ tailWord_7449534) baseStart_7449534 baseEnd_7449534 := by
    simpa [prefixWord, tailWord_7449534, baseEnd_7449534] using wordTrace_append hprefix tailTrace_7449534
  have hstable : (prefixWord ++ tailWord_7449534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449534).length < 2 ^ (prefixWord ++ tailWord_7449534).sum := by decide
  have hdescent : baseEnd_7449534 < baseStart_7449534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449542 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_7449542 : Nat := 118140960795 + 7449542 * 2 ^ 59
def prefixEnd_7449542 : Nat := 4983230072969 + 3 ^ 40 * 7449542 * 2
def baseEnd_7449542 : Nat := 3825195701856197866365187

theorem tailTrace_7449542 : CollatzResearch.WordTrace tailWord_7449542 prefixEnd_7449542 3825195701856197866365187 := by
  unfold tailWord_7449542
  simp only [CollatzResearch.WordTrace]
  refine ⟨8490847449299659041477715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 181138078918392726218191253 8490847449299659041477715)
  ·
    refine ⟨12736271173949488562216573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8490847449299659041477715 12736271173949488562216573)
    ·
      refine ⟨4776101690231058210831215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12736271173949488562216573 4776101690231058210831215)
      ·
        refine ⟨7164152535346587316246823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4776101690231058210831215 7164152535346587316246823)
        ·
          refine ⟨10746228803019880974370235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7164152535346587316246823 10746228803019880974370235)
          ·
            refine ⟨16119343204529821461555353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10746228803019880974370235 16119343204529821461555353)
            ·
              refine ⟨12089507403397366096166515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16119343204529821461555353 12089507403397366096166515)
              ·
                refine ⟨18134261105096049144249773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12089507403397366096166515 18134261105096049144249773)
                ·
                  refine ⟨6800347914411018429093665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18134261105096049144249773 6800347914411018429093665)
                  ·
                    refine ⟨5100260935808263821820249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6800347914411018429093665 5100260935808263821820249)
                    ·
                      refine ⟨3825195701856197866365187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100260935808263821820249 3825195701856197866365187)
                      ·
                        rfl

theorem cell23_7449542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_7449542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449542 prefixEnd_7449542 := by exact prefixLift 7449542
  have htrace : WordTrace (prefixWord ++ tailWord_7449542) baseStart_7449542 baseEnd_7449542 := by
    simpa [prefixWord, tailWord_7449542, baseEnd_7449542] using wordTrace_append hprefix tailTrace_7449542
  have hstable : (prefixWord ++ tailWord_7449542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449542).length < 2 ^ (prefixWord ++ tailWord_7449542).sum := by decide
  have hdescent : baseEnd_7449542 < baseStart_7449542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449558 : List Nat := [5, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_7449558 : Nat := 118140960795 + 7449558 * 2 ^ 59
def prefixEnd_7449558 : Nat := 4983230072969 + 3 ^ 40 * 7449558 * 2
def baseEnd_7449558 : Nat := 3825203917546669803765113

theorem tailTrace_7449558 : CollatzResearch.WordTrace tailWord_7449558 prefixEnd_7449558 3825203917546669803765113 := by
  unfold tailWord_7449558
  simp only [CollatzResearch.WordTrace]
  refine ⟨16981731371595695253741833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181138467963687416039912885 16981731371595695253741833)
  ·
    refine ⟨12736298528696771440306375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16981731371595695253741833 12736298528696771440306375)
    ·
      refine ⟨19104447793045157160459563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12736298528696771440306375 19104447793045157160459563)
      ·
        refine ⟨28656671689567735740689345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19104447793045157160459563 28656671689567735740689345)
        ·
          refine ⟨21492503767175801805517009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28656671689567735740689345 21492503767175801805517009)
          ·
            refine ⟨16119377825381851354137757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21492503767175801805517009 16119377825381851354137757)
            ·
              refine ⟨6044766684518194257801659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16119377825381851354137757 6044766684518194257801659)
              ·
                refine ⟨9067150026777291386702489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6044766684518194257801659 9067150026777291386702489)
                ·
                  refine ⟨6800362520082968540026867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9067150026777291386702489 6800362520082968540026867)
                  ·
                    refine ⟨10200543780124452810040301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6800362520082968540026867 10200543780124452810040301)
                    ·
                      refine ⟨3825203917546669803765113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10200543780124452810040301 3825203917546669803765113)
                      ·
                        rfl

theorem cell23_7449558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_7449558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449558 prefixEnd_7449558 := by exact prefixLift 7449558
  have htrace : WordTrace (prefixWord ++ tailWord_7449558) baseStart_7449558 baseEnd_7449558 := by
    simpa [prefixWord, tailWord_7449558, baseEnd_7449558] using wordTrace_append hprefix tailTrace_7449558
  have hstable : (prefixWord ++ tailWord_7449558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449558).length < 2 ^ (prefixWord ++ tailWord_7449558).sum := by decide
  have hdescent : baseEnd_7449558 < baseStart_7449558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449560 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 2, 2, 4]
def baseStart_7449560 : Nat := 118140960795 + 7449560 * 2 ^ 59
def prefixEnd_7449560 : Nat := 4983230072969 + 3 ^ 40 * 7449560 * 2
def baseEnd_7449560 : Nat := 3825204944507978795940103

theorem tailTrace_7449560 : CollatzResearch.WordTrace tailWord_7449560 prefixEnd_7449560 3825204944507978795940103 := by
  unfold tailWord_7449560
  simp only [CollatzResearch.WordTrace]
  refine ⟨135853887445761939200721067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181138516594349252267628089 135853887445761939200721067)
  ·
    refine ⟨203780831168642908801081601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135853887445761939200721067 203780831168642908801081601)
    ·
      refine ⟨152835623376482181600811201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203780831168642908801081601 152835623376482181600811201)
      ·
        refine ⟨114626717532361636200608401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152835623376482181600811201 114626717532361636200608401)
        ·
          refine ⟨85970038149271227150456301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114626717532361636200608401 85970038149271227150456301)
          ·
            refine ⟨32238764305976710181421113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85970038149271227150456301 32238764305976710181421113)
            ·
              refine ⟨24179073229482532636065835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32238764305976710181421113 24179073229482532636065835)
              ·
                refine ⟨36268609844223798954098753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24179073229482532636065835 36268609844223798954098753)
                ·
                  refine ⟨27201457383167849215574065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36268609844223798954098753 27201457383167849215574065)
                  ·
                    refine ⟨20401093037375886911680549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27201457383167849215574065 20401093037375886911680549)
                    ·
                      refine ⟨3825204944507978795940103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20401093037375886911680549 3825204944507978795940103)
                      ·
                        rfl

theorem cell23_7449560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_7449560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449560 prefixEnd_7449560 := by exact prefixLift 7449560
  have htrace : WordTrace (prefixWord ++ tailWord_7449560) baseStart_7449560 baseEnd_7449560 := by
    simpa [prefixWord, tailWord_7449560, baseEnd_7449560] using wordTrace_append hprefix tailTrace_7449560
  have hstable : (prefixWord ++ tailWord_7449560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449560).length < 2 ^ (prefixWord ++ tailWord_7449560).sum := by decide
  have hdescent : baseEnd_7449560 < baseStart_7449560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449603 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 8]
def baseStart_7449603 : Nat := 118140960795 + 7449603 * 2 ^ 59
def prefixEnd_7449603 : Nat := 4983230072969 + 3 ^ 40 * 7449603 * 2
def baseEnd_7449603 : Nat := 3825227024176122127702405

theorem tailTrace_7449603 : CollatzResearch.WordTrace tailWord_7449603 prefixEnd_7449603 3825227024176122127702405 := by
  unfold tailWord_7449603
  simp only [CollatzResearch.WordTrace]
  refine ⟨271709343230368096745257463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181139562153578731163504975 271709343230368096745257463)
  ·
    refine ⟨407564014845552145117886195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271709343230368096745257463 407564014845552145117886195)
    ·
      refine ⟨611346022268328217676829293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407564014845552145117886195 611346022268328217676829293)
      ·
        refine ⟨229254758350623081628810985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 611346022268328217676829293 229254758350623081628810985)
        ·
          refine ⟨171941068762967311221608239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229254758350623081628810985 171941068762967311221608239)
          ·
            refine ⟨257911603144450966832412359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171941068762967311221608239 257911603144450966832412359)
            ·
              refine ⟨386867404716676450248618539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257911603144450966832412359 386867404716676450248618539)
              ·
                refine ⟨580301107075014675372927809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386867404716676450248618539 580301107075014675372927809)
                ·
                  refine ⟨435225830306261006529695857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 580301107075014675372927809 435225830306261006529695857)
                  ·
                    refine ⟨326419372729695754897271893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 435225830306261006529695857 326419372729695754897271893)
                    ·
                      refine ⟨3825227024176122127702405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 326419372729695754897271893 3825227024176122127702405)
                      ·
                        rfl

theorem cell23_7449603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_7449603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449603 prefixEnd_7449603 := by exact prefixLift 7449603
  have htrace : WordTrace (prefixWord ++ tailWord_7449603) baseStart_7449603 baseEnd_7449603 := by
    simpa [prefixWord, tailWord_7449603, baseEnd_7449603] using wordTrace_append hprefix tailTrace_7449603
  have hstable : (prefixWord ++ tailWord_7449603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449603).length < 2 ^ (prefixWord ++ tailWord_7449603).sum := by decide
  have hdescent : baseEnd_7449603 < baseStart_7449603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449607 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 2, 5, 2]
def baseStart_7449607 : Nat := 118140960795 + 7449607 * 2 ^ 59
def prefixEnd_7449607 : Nat := 4983230072969 + 3 ^ 40 * 7449607 * 2
def baseEnd_7449607 : Nat := 3825229078098740112052387

theorem tailTrace_7449607 : CollatzResearch.WordTrace tailWord_7449607 prefixEnd_7449607 3825229078098740112052387 := by
  unfold tailWord_7449607
  simp only [CollatzResearch.WordTrace]
  refine ⟨271709489122353605428403075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181139659414902403618935383 271709489122353605428403075)
  ·
    refine ⟨407564233683530408142604613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271709489122353605428403075 407564233683530408142604613)
    ·
      refine ⟨76418293815661951526738365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 407564233683530408142604613 76418293815661951526738365)
      ·
        refine ⟨28656860180873231822526887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76418293815661951526738365 28656860180873231822526887)
        ·
          refine ⟨42985290271309847733790331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28656860180873231822526887 42985290271309847733790331)
          ·
            refine ⟨64477935406964771600685497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42985290271309847733790331 64477935406964771600685497)
            ·
              refine ⟨48358451555223578700514123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64477935406964771600685497 48358451555223578700514123)
              ·
                refine ⟨72537677332835368050771185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48358451555223578700514123 72537677332835368050771185)
                ·
                  refine ⟨54403257999626526038078389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72537677332835368050771185 54403257999626526038078389)
                  ·
                    refine ⟨5100305437464986816069849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54403257999626526038078389 5100305437464986816069849)
                    ·
                      refine ⟨3825229078098740112052387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100305437464986816069849 3825229078098740112052387)
                      ·
                        rfl

theorem cell23_7449607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_7449607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449607 prefixEnd_7449607 := by exact prefixLift 7449607
  have htrace : WordTrace (prefixWord ++ tailWord_7449607) baseStart_7449607 baseEnd_7449607 := by
    simpa [prefixWord, tailWord_7449607, baseEnd_7449607] using wordTrace_append hprefix tailTrace_7449607
  have hstable : (prefixWord ++ tailWord_7449607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449607).length < 2 ^ (prefixWord ++ tailWord_7449607).sum := by decide
  have hdescent : baseEnd_7449607 < baseStart_7449607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449610 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_7449610 : Nat := 118140960795 + 7449610 * 2 ^ 59
def prefixEnd_7449610 : Nat := 4983230072969 + 3 ^ 40 * 7449610 * 2
def baseEnd_7449610 : Nat := 3825230618540703600314873

theorem tailTrace_7449610 : CollatzResearch.WordTrace tailWord_7449610 prefixEnd_7449610 3825230618540703600314873 := by
  unfold tailWord_7449610
  simp only [CollatzResearch.WordTrace]
  refine ⟨67927399635335684235190571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181139732360895157960508189 67927399635335684235190571)
  ·
    refine ⟨101891099453003526352785857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67927399635335684235190571 101891099453003526352785857)
    ·
      refine ⟨76418324589752644764589393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101891099453003526352785857 76418324589752644764589393)
      ·
        refine ⟨57313743442314483573442045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76418324589752644764589393 57313743442314483573442045)
        ·
          refine ⟨21492653790867931340040767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57313743442314483573442045 21492653790867931340040767)
          ·
            refine ⟨32238980686301897010061151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21492653790867931340040767 32238980686301897010061151)
            ·
              refine ⟨48358471029452845515091727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32238980686301897010061151 48358471029452845515091727)
              ·
                refine ⟨72537706544179268272637591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48358471029452845515091727 72537706544179268272637591)
                ·
                  refine ⟨108806559816268902408956387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72537706544179268272637591 108806559816268902408956387)
                  ·
                    refine ⟨163209839724403353613434581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108806559816268902408956387 163209839724403353613434581)
                    ·
                      refine ⟨3825230618540703600314873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163209839724403353613434581 3825230618540703600314873)
                      ·
                        rfl

theorem cell23_7449610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_7449610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449610 prefixEnd_7449610 := by exact prefixLift 7449610
  have htrace : WordTrace (prefixWord ++ tailWord_7449610) baseStart_7449610 baseEnd_7449610 := by
    simpa [prefixWord, tailWord_7449610, baseEnd_7449610] using wordTrace_append hprefix tailTrace_7449610
  have hstable : (prefixWord ++ tailWord_7449610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449610).length < 2 ^ (prefixWord ++ tailWord_7449610).sum := by decide
  have hdescent : baseEnd_7449610 < baseStart_7449610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449637 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 2, 1, 4]
def baseStart_7449637 : Nat := 118140960795 + 7449637 * 2 ^ 59
def prefixEnd_7449637 : Nat := 4983230072969 + 3 ^ 40 * 7449637 * 2
def baseEnd_7449637 : Nat := 3825244482518374994677249

theorem tailTrace_7449637 : CollatzResearch.WordTrace tailWord_7449637 prefixEnd_7449637 3825244482518374994677249 := by
  unfold tailWord_7449637
  simp only [CollatzResearch.WordTrace]
  refine ⟨271710583312244920551995165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181140388874829947034663443 271710583312244920551995165)
  ·
    refine ⟨101891468742091845206998187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271710583312244920551995165 101891468742091845206998187)
    ·
      refine ⟨152837203113137767810497281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101891468742091845206998187 152837203113137767810497281)
      ·
        refine ⟨114627902334853325857872961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152837203113137767810497281 114627902334853325857872961)
        ·
          refine ⟨85970926751139994393404721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114627902334853325857872961 85970926751139994393404721)
          ·
            refine ⟨64478195063354995795053541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85970926751139994393404721 64478195063354995795053541)
            ·
              refine ⟨12089661574379061711572539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64478195063354995795053541 12089661574379061711572539)
              ·
                refine ⟨18134492361568592567358809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12089661574379061711572539 18134492361568592567358809)
                ·
                  refine ⟨13600869271176444425519107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18134492361568592567358809 13600869271176444425519107)
                  ·
                    refine ⟨20401303906764666638278661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13600869271176444425519107 20401303906764666638278661)
                    ·
                      refine ⟨3825244482518374994677249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20401303906764666638278661 3825244482518374994677249)
                      ·
                        rfl

theorem cell23_7449637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_7449637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449637 prefixEnd_7449637 := by exact prefixLift 7449637
  have htrace : WordTrace (prefixWord ++ tailWord_7449637) baseStart_7449637 baseEnd_7449637 := by
    simpa [prefixWord, tailWord_7449637, baseEnd_7449637] using wordTrace_append hprefix tailTrace_7449637
  have hstable : (prefixWord ++ tailWord_7449637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449637).length < 2 ^ (prefixWord ++ tailWord_7449637).sum := by decide
  have hdescent : baseEnd_7449637 < baseStart_7449637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449650 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_7449650 : Nat := 118140960795 + 7449650 * 2 ^ 59
def prefixEnd_7449650 : Nat := 4983230072969 + 3 ^ 40 * 7449650 * 2
def baseEnd_7449650 : Nat := 3825251157766883443814689

theorem tailTrace_7449650 : CollatzResearch.WordTrace tailWord_7449650 prefixEnd_7449650 3825251157766883443814689 := by
  unfold tailWord_7449650
  simp only [CollatzResearch.WordTrace]
  refine ⟨67927764365299455943054601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181140704974131882514812269 67927764365299455943054601)
  ·
    refine ⟨50945823273974591957290951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67927764365299455943054601 50945823273974591957290951)
    ·
      refine ⟨76418734910961887935936427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50945823273974591957290951 76418734910961887935936427)
      ·
        refine ⟨114628102366442831903904641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76418734910961887935936427 114628102366442831903904641)
        ·
          refine ⟨85971076774832123927928481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114628102366442831903904641 85971076774832123927928481)
          ·
            refine ⟨64478307581124092945946361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85971076774832123927928481 64478307581124092945946361)
            ·
              refine ⟨48358730685843069709459771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64478307581124092945946361 48358730685843069709459771)
              ·
                refine ⟨72538096028764604564189657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48358730685843069709459771 72538096028764604564189657)
                ·
                  refine ⟨54403572021573453423142243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72538096028764604564189657 54403572021573453423142243)
                  ·
                    refine ⟨81605358032360180134713365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54403572021573453423142243 81605358032360180134713365)
                    ·
                      refine ⟨3825251157766883443814689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81605358032360180134713365 3825251157766883443814689)
                      ·
                        rfl

theorem cell23_7449650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_7449650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449650 prefixEnd_7449650 := by exact prefixLift 7449650
  have htrace : WordTrace (prefixWord ++ tailWord_7449650) baseStart_7449650 baseEnd_7449650 := by
    simpa [prefixWord, tailWord_7449650, baseEnd_7449650] using wordTrace_append hprefix tailTrace_7449650
  have hstable : (prefixWord ++ tailWord_7449650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449650).length < 2 ^ (prefixWord ++ tailWord_7449650).sum := by decide
  have hdescent : baseEnd_7449650 < baseStart_7449650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449654 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_7449654 : Nat := 118140960795 + 7449654 * 2 ^ 59
def prefixEnd_7449654 : Nat := 4983230072969 + 3 ^ 40 * 7449654 * 2
def baseEnd_7449654 : Nat := 3825253211689501428164671

theorem tailTrace_7449654 : CollatzResearch.WordTrace tailWord_7449654 prefixEnd_7449654 3825253211689501428164671 := by
  unfold tailWord_7449654
  simp only [CollatzResearch.WordTrace]
  refine ⟨16981950209573958278460251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181140802235455554970242677 16981950209573958278460251)
  ·
    refine ⟨25472925314360937417690377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16981950209573958278460251 25472925314360937417690377)
    ·
      refine ⟨19104693985770703063267783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25472925314360937417690377 19104693985770703063267783)
      ·
        refine ⟨28657040978656054594901675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19104693985770703063267783 28657040978656054594901675)
        ·
          refine ⟨42985561467984081892352513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28657040978656054594901675 42985561467984081892352513)
          ·
            refine ⟨32239171100988061419264385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42985561467984081892352513 32239171100988061419264385)
            ·
              refine ⟨24179378325741046064448289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32239171100988061419264385 24179378325741046064448289)
              ·
                refine ⟨18134533744305784548336217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24179378325741046064448289 18134533744305784548336217)
                ·
                  refine ⟨13600900308229338411252163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18134533744305784548336217 13600900308229338411252163)
                  ·
                    refine ⟨20401350462344007616878245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13600900308229338411252163 20401350462344007616878245)
                    ·
                      refine ⟨3825253211689501428164671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20401350462344007616878245 3825253211689501428164671)
                      ·
                        rfl

theorem cell23_7449654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_7449654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449654 prefixEnd_7449654 := by exact prefixLift 7449654
  have htrace : WordTrace (prefixWord ++ tailWord_7449654) baseStart_7449654 baseEnd_7449654 := by
    simpa [prefixWord, tailWord_7449654, baseEnd_7449654] using wordTrace_append hprefix tailTrace_7449654
  have hstable : (prefixWord ++ tailWord_7449654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449654).length < 2 ^ (prefixWord ++ tailWord_7449654).sum := by decide
  have hdescent : baseEnd_7449654 < baseStart_7449654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449664 : List Nat := [2, 1, 1, 2, 2, 3, 3, 4, 1, 4]
def baseStart_7449664 : Nat := 118140960795 + 7449664 * 2 ^ 59
def prefixEnd_7449664 : Nat := 4983230072969 + 3 ^ 40 * 7449664 * 2
def baseEnd_7449664 : Nat := 1275086115498682129679875

theorem tailTrace_7449664 : CollatzResearch.WordTrace tailWord_7449664 prefixEnd_7449664 1275086115498682129679875 := by
  unfold tailWord_7449664
  simp only [CollatzResearch.WordTrace]
  refine ⟨135855784041573552081614023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181141045388764736108818697 135855784041573552081614023)
  ·
    refine ⟨203783676062360328122421035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135855784041573552081614023 203783676062360328122421035)
    ·
      refine ⟨305675514093540492183631553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203783676062360328122421035 305675514093540492183631553)
      ·
        refine ⟨229256635570155369137723665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305675514093540492183631553 229256635570155369137723665)
        ·
          refine ⟨171942476677616526853292749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229256635570155369137723665 171942476677616526853292749)
          ·
            refine ⟨64478428754106197569984781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171942476677616526853292749 64478428754106197569984781)
            ·
              refine ⟨24179410782789824088744293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64478428754106197569984781 24179410782789824088744293)
              ·
                refine ⟨4533639521773092016639555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24179410782789824088744293 4533639521773092016639555)
                ·
                  refine ⟨6800459282659638024959333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533639521773092016639555 6800459282659638024959333)
                  ·
                    refine ⟨1275086115498682129679875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6800459282659638024959333 1275086115498682129679875)
                    ·
                      rfl

theorem cell23_7449664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 1, 4].length) (baseStart_7449664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449664 prefixEnd_7449664 := by exact prefixLift 7449664
  have htrace : WordTrace (prefixWord ++ tailWord_7449664) baseStart_7449664 baseEnd_7449664 := by
    simpa [prefixWord, tailWord_7449664, baseEnd_7449664] using wordTrace_append hprefix tailTrace_7449664
  have hstable : (prefixWord ++ tailWord_7449664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449664).length < 2 ^ (prefixWord ++ tailWord_7449664).sum := by decide
  have hdescent : baseEnd_7449664 < baseStart_7449664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449698 : List Nat := [3, 3, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_7449698 : Nat := 118140960795 + 7449698 * 2 ^ 59
def prefixEnd_7449698 : Nat := 4983230072969 + 3 ^ 40 * 7449698 * 2
def baseEnd_7449698 : Nat := 1275091934946099752004823

theorem tailTrace_7449698 : CollatzResearch.WordTrace tailWord_7449698 prefixEnd_7449698 1275091934946099752004823 := by
  unfold tailWord_7449698
  simp only [CollatzResearch.WordTrace]
  refine ⟨67928202041255981992491437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181141872110015951979977165 67928202041255981992491437)
  ·
    refine ⟨25473075765470993247184289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67928202041255981992491437 25473075765470993247184289)
    ·
      refine ⟨19104806824103244935388217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25473075765470993247184289 19104806824103244935388217)
      ·
        refine ⟨14328605118077433701541163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19104806824103244935388217 14328605118077433701541163)
        ·
          refine ⟨21492907677116150552311745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14328605118077433701541163 21492907677116150552311745)
          ·
            refine ⟨16119680757837112914233809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21492907677116150552311745 16119680757837112914233809)
            ·
              refine ⟨12089760568377834685675357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16119680757837112914233809 12089760568377834685675357)
              ·
                refine ⟨4533660213141688007128259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12089760568377834685675357 4533660213141688007128259)
                ·
                  refine ⟨6800490319712532010692389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533660213141688007128259 6800490319712532010692389)
                  ·
                    refine ⟨1275091934946099752004823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6800490319712532010692389 1275091934946099752004823)
                    ·
                      rfl

theorem cell23_7449698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_7449698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449698 prefixEnd_7449698 := by exact prefixLift 7449698
  have htrace : WordTrace (prefixWord ++ tailWord_7449698) baseStart_7449698 baseEnd_7449698 := by
    simpa [prefixWord, tailWord_7449698, baseEnd_7449698] using wordTrace_append hprefix tailTrace_7449698
  have hstable : (prefixWord ++ tailWord_7449698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449698).length < 2 ^ (prefixWord ++ tailWord_7449698).sum := by decide
  have hdescent : baseEnd_7449698 < baseStart_7449698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449700 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_7449700 : Nat := 118140960795 + 7449700 * 2 ^ 59
def prefixEnd_7449700 : Nat := 4983230072969 + 3 ^ 40 * 7449700 * 2
def baseEnd_7449700 : Nat := 3825276831799608248189459

theorem tailTrace_7449700 : CollatzResearch.WordTrace tailWord_7449700 prefixEnd_7449700 3825276831799608248189459 := by
  unfold tailWord_7449700
  simp only [CollatzResearch.WordTrace]
  refine ⟨135856440555508341155769277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181141920740677788207692369 135856440555508341155769277)
  ·
    refine ⟨50946165208315627933413479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135856440555508341155769277 50946165208315627933413479)
    ·
      refine ⟨76419247812473441900120219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50946165208315627933413479 76419247812473441900120219)
      ·
        refine ⟨114628871718710162850180329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76419247812473441900120219 114628871718710162850180329)
        ·
          refine ⟨85971653789032622137635247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114628871718710162850180329 85971653789032622137635247)
          ·
            refine ⟨128957480683548933206452871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85971653789032622137635247 128957480683548933206452871)
            ·
              refine ⟨193436221025323399809679307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128957480683548933206452871 193436221025323399809679307)
              ·
                refine ⟨290154331537985099714518961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193436221025323399809679307 290154331537985099714518961)
                ·
                  refine ⟨217615748653488824785889221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290154331537985099714518961 217615748653488824785889221)
                  ·
                    refine ⟨40802952872529154647354229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 217615748653488824785889221 40802952872529154647354229)
                    ·
                      refine ⟨3825276831799608248189459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40802952872529154647354229 3825276831799608248189459)
                      ·
                        rfl

theorem cell23_7449700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_7449700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449700 prefixEnd_7449700 := by exact prefixLift 7449700
  have htrace : WordTrace (prefixWord ++ tailWord_7449700) baseStart_7449700 baseEnd_7449700 := by
    simpa [prefixWord, tailWord_7449700, baseEnd_7449700] using wordTrace_append hprefix tailTrace_7449700
  have hstable : (prefixWord ++ tailWord_7449700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449700).length < 2 ^ (prefixWord ++ tailWord_7449700).sum := by decide
  have hdescent : baseEnd_7449700 < baseStart_7449700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449714 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 4, 3, 2]
def baseStart_7449714 : Nat := 118140960795 + 7449714 * 2 ^ 59
def prefixEnd_7449714 : Nat := 4983230072969 + 3 ^ 40 * 7449714 * 2
def baseEnd_7449714 : Nat := 3825284020528771193414395

theorem tailTrace_7449714 : CollatzResearch.WordTrace tailWord_7449714 prefixEnd_7449714 3825284020528771193414395 := by
  unfold tailWord_7449714
  simp only [CollatzResearch.WordTrace]
  refine ⟨67928347933241490675637049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181142261155310641801698797 67928347933241490675637049)
  ·
    refine ⟨50946260949931118006727787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67928347933241490675637049 50946260949931118006727787)
    ·
      refine ⟨76419391424896677010091681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50946260949931118006727787 76419391424896677010091681)
      ·
        refine ⟨57314543568672507757568761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76419391424896677010091681 57314543568672507757568761)
        ·
          refine ⟨42985907676504380818176571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57314543568672507757568761 42985907676504380818176571)
          ·
            refine ⟨64478861514756571227264857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42985907676504380818176571 64478861514756571227264857)
            ·
              refine ⟨48359146136067428420448643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64478861514756571227264857 48359146136067428420448643)
              ·
                refine ⟨72538719204101142630672965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48359146136067428420448643 72538719204101142630672965)
                ·
                  refine ⟨13601009850768964243251181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72538719204101142630672965 13601009850768964243251181)
                  ·
                    refine ⟨5100378694038361591219193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13601009850768964243251181 5100378694038361591219193)
                    ·
                      refine ⟨3825284020528771193414395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100378694038361591219193 3825284020528771193414395)
                      ·
                        rfl

theorem cell23_7449714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_7449714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449714 prefixEnd_7449714 := by exact prefixLift 7449714
  have htrace : WordTrace (prefixWord ++ tailWord_7449714) baseStart_7449714 baseEnd_7449714 := by
    simpa [prefixWord, tailWord_7449714, baseEnd_7449714] using wordTrace_append hprefix tailTrace_7449714
  have hstable : (prefixWord ++ tailWord_7449714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449714).length < 2 ^ (prefixWord ++ tailWord_7449714).sum := by decide
  have hdescent : baseEnd_7449714 < baseStart_7449714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449720 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 3, 6]
def baseStart_7449720 : Nat := 118140960795 + 7449720 * 2 ^ 59
def prefixEnd_7449720 : Nat := 4983230072969 + 3 ^ 40 * 7449720 * 2
def baseEnd_7449720 : Nat := 1275095700470899389979789

theorem tailTrace_7449720 : CollatzResearch.WordTrace tailWord_7449720 prefixEnd_7449720 1275095700470899389979789 := by
  unfold tailWord_7449720
  simp only [CollatzResearch.WordTrace]
  refine ⟨135856805285472112863633307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181142407047296150484844409 135856805285472112863633307)
  ·
    refine ⟨203785207928208169295449961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135856805285472112863633307 203785207928208169295449961)
    ·
      refine ⟨152838905946156126971587471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203785207928208169295449961 152838905946156126971587471)
      ·
        refine ⟨229258358919234190457381207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152838905946156126971587471 229258358919234190457381207)
        ·
          refine ⟨343887538378851285686071811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229258358919234190457381207 343887538378851285686071811)
          ·
            refine ⟨515831307568276928529107717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343887538378851285686071811 515831307568276928529107717)
            ·
              refine ⟨96718370169051924099207697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 515831307568276928529107717 96718370169051924099207697)
              ·
                refine ⟨72538777626788943074405773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96718370169051924099207697 72538777626788943074405773)
                ·
                  refine ⟨27202041610045853652902165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72538777626788943074405773 27202041610045853652902165)
                  ·
                    refine ⟨1275095700470899389979789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27202041610045853652902165 1275095700470899389979789)
                    ·
                      rfl

theorem cell23_7449720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_7449720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449720 prefixEnd_7449720 := by exact prefixLift 7449720
  have htrace : WordTrace (prefixWord ++ tailWord_7449720) baseStart_7449720 baseEnd_7449720 := by
    simpa [prefixWord, tailWord_7449720, baseEnd_7449720] using wordTrace_append hprefix tailTrace_7449720
  have hstable : (prefixWord ++ tailWord_7449720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449720).length < 2 ^ (prefixWord ++ tailWord_7449720).sum := by decide
  have hdescent : baseEnd_7449720 < baseStart_7449720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449721 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 3, 1, 3]
def baseStart_7449721 : Nat := 118140960795 + 7449721 * 2 ^ 59
def prefixEnd_7449721 : Nat := 4983230072969 + 3 ^ 40 * 7449721 * 2
def baseEnd_7449721 : Nat := 3825287614893352666026863

theorem tailTrace_7449721 : CollatzResearch.WordTrace tailWord_7449721 prefixEnd_7449721 3825287614893352666026863 := by
  unfold tailWord_7449721
  simp only [CollatzResearch.WordTrace]
  refine ⟨271713647043940602898053017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181142431362627068598702011 271713647043940602898053017)
  ·
    refine ⟨203785235282955452173539763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271713647043940602898053017 203785235282955452173539763)
    ·
      refine ⟨305677852924433178260309645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203785235282955452173539763 305677852924433178260309645)
      ·
        refine ⟨114629194846662441847616117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 305677852924433178260309645 114629194846662441847616117)
        ·
          refine ⟨10746487016874603923214011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114629194846662441847616117 10746487016874603923214011)
          ·
            refine ⟨16119730525311905884821017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10746487016874603923214011 16119730525311905884821017)
            ·
              refine ⟨12089797893983929413615763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16119730525311905884821017 12089797893983929413615763)
              ·
                refine ⟨18134696840975894120423645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12089797893983929413615763 18134696840975894120423645)
                ·
                  refine ⟨6800511315365960295158867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18134696840975894120423645 6800511315365960295158867)
                  ·
                    refine ⟨10200766973048940442738301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6800511315365960295158867 10200766973048940442738301)
                    ·
                      refine ⟨3825287614893352666026863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10200766973048940442738301 3825287614893352666026863)
                      ·
                        rfl

theorem cell23_7449721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_7449721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449721 prefixEnd_7449721 := by exact prefixLift 7449721
  have htrace : WordTrace (prefixWord ++ tailWord_7449721) baseStart_7449721 baseEnd_7449721 := by
    simpa [prefixWord, tailWord_7449721, baseEnd_7449721] using wordTrace_append hprefix tailTrace_7449721
  have hstable : (prefixWord ++ tailWord_7449721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449721).length < 2 ^ (prefixWord ++ tailWord_7449721).sum := by decide
  have hdescent : baseEnd_7449721 < baseStart_7449721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449737 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 1, 6]
def baseStart_7449737 : Nat := 118140960795 + 7449737 * 2 ^ 59
def prefixEnd_7449737 : Nat := 4983230072969 + 3 ^ 40 * 7449737 * 2
def baseEnd_7449737 : Nat := 1275098610194608201142263

theorem tailTrace_7449737 : CollatzResearch.WordTrace tailWord_7449737 prefixEnd_7449737 1275098610194608201142263 := by
  unfold tailWord_7449737
  simp only [CollatzResearch.WordTrace]
  refine ⟨271714230611882637630635465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181142820407921758420423643 271714230611882637630635465)
  ·
    refine ⟨203785672958911978222976599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271714230611882637630635465 203785672958911978222976599)
    ·
      refine ⟨305678509438367967334464899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203785672958911978222976599 305678509438367967334464899)
      ·
        refine ⟨458517764157551951001697349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305678509438367967334464899 458517764157551951001697349)
        ·
          refine ⟨85972080779540990812818253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 458517764157551951001697349 85972080779540990812818253)
          ·
            refine ⟨32239530292327871554806845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85972080779540990812818253 32239530292327871554806845)
            ·
              refine ⟨12089823859622951833052567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32239530292327871554806845 12089823859622951833052567)
              ·
                refine ⟨18134735789434427749578851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12089823859622951833052567 18134735789434427749578851)
                ·
                  refine ⟨27202103684151641624368277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18134735789434427749578851 27202103684151641624368277)
                  ·
                    refine ⟨1275098610194608201142263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27202103684151641624368277 1275098610194608201142263)
                    ·
                      rfl

theorem cell23_7449737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 6].length) (baseStart_7449737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449737 prefixEnd_7449737 := by exact prefixLift 7449737
  have htrace : WordTrace (prefixWord ++ tailWord_7449737) baseStart_7449737 baseEnd_7449737 := by
    simpa [prefixWord, tailWord_7449737, baseEnd_7449737] using wordTrace_append hprefix tailTrace_7449737
  have hstable : (prefixWord ++ tailWord_7449737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449737).length < 2 ^ (prefixWord ++ tailWord_7449737).sum := by decide
  have hdescent : baseEnd_7449737 < baseStart_7449737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449744 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 5, 2, 2]
def baseStart_7449744 : Nat := 118140960795 + 7449744 * 2 ^ 59
def prefixEnd_7449744 : Nat := 4983230072969 + 3 ^ 40 * 7449744 * 2
def baseEnd_7449744 : Nat := 3825299424948406076039257

theorem tailTrace_7449744 : CollatzResearch.WordTrace tailWord_7449744 prefixEnd_7449744 3825299424948406076039257 := by
  unfold tailWord_7449744
  simp only [CollatzResearch.WordTrace]
  refine ⟨135857242961428638913070143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181142990615238185217426857 135857242961428638913070143)
  ·
    refine ⟨203785864442142958369605215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135857242961428638913070143 203785864442142958369605215)
    ·
      refine ⟨305678796663214437554407823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203785864442142958369605215 305678796663214437554407823)
      ·
        refine ⟨458518194994821656331611735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305678796663214437554407823 458518194994821656331611735)
        ·
          refine ⟨687777292492232484497417603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458518194994821656331611735 687777292492232484497417603)
          ·
            refine ⟨1031665938738348726746126405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687777292492232484497417603 1031665938738348726746126405)
            ·
              refine ⟨193437363513440386264898701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1031665938738348726746126405 193437363513440386264898701)
              ·
                refine ⟨72539011317540144849337013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193437363513440386264898701 72539011317540144849337013)
                ·
                  refine ⟨6800532311019388579625345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72539011317540144849337013 6800532311019388579625345)
                  ·
                    refine ⟨5100399233264541434719009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6800532311019388579625345 5100399233264541434719009)
                    ·
                      refine ⟨3825299424948406076039257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100399233264541434719009 3825299424948406076039257)
                      ·
                        rfl

theorem cell23_7449744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 5, 2, 2].length) (baseStart_7449744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449744 prefixEnd_7449744 := by exact prefixLift 7449744
  have htrace : WordTrace (prefixWord ++ tailWord_7449744) baseStart_7449744 baseEnd_7449744 := by
    simpa [prefixWord, tailWord_7449744, baseEnd_7449744] using wordTrace_append hprefix tailTrace_7449744
  have hstable : (prefixWord ++ tailWord_7449744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449744).length < 2 ^ (prefixWord ++ tailWord_7449744).sum := by decide
  have hdescent : baseEnd_7449744 < baseStart_7449744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449747 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 3]
def baseStart_7449747 : Nat := 118140960795 + 7449747 * 2 ^ 59
def prefixEnd_7449747 : Nat := 4983230072969 + 3 ^ 40 * 7449747 * 2
def baseEnd_7449747 : Nat := 3825300965390369564301743

theorem tailTrace_7449747 : CollatzResearch.WordTrace tailWord_7449747 prefixEnd_7449747 3825300965390369564301743 := by
  unfold tailWord_7449747
  simp only [CollatzResearch.WordTrace]
  refine ⟨271714595341846409338499495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181143063561230939558999663 271714595341846409338499495)
  ·
    refine ⟨407571893012769614007749243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271714595341846409338499495 407571893012769614007749243)
    ·
      refine ⟨611357839519154421011623865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407571893012769614007749243 611357839519154421011623865)
      ·
        refine ⟨458518379639365815758717899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 611357839519154421011623865 458518379639365815758717899)
        ·
          refine ⟨687777569459048723638076849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458518379639365815758717899 687777569459048723638076849)
          ·
            refine ⟨515833177094286542728557637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 687777569459048723638076849 515833177094286542728557637)
            ·
              refine ⟨96718720705178726761604557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 515833177094286542728557637 96718720705178726761604557)
              ·
                refine ⟨36269520264442022535601709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96718720705178726761604557 36269520264442022535601709)
                ·
                  refine ⟨13601070099165758450850641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36269520264442022535601709 13601070099165758450850641)
                  ·
                    refine ⟨10200802574374318838137981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13601070099165758450850641 10200802574374318838137981)
                    ·
                      refine ⟨3825300965390369564301743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10200802574374318838137981 3825300965390369564301743)
                      ·
                        rfl

theorem cell23_7449747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 3].length) (baseStart_7449747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449747 prefixEnd_7449747 := by exact prefixLift 7449747
  have htrace : WordTrace (prefixWord ++ tailWord_7449747) baseStart_7449747 baseEnd_7449747 := by
    simpa [prefixWord, tailWord_7449747, baseEnd_7449747] using wordTrace_append hprefix tailTrace_7449747
  have hstable : (prefixWord ++ tailWord_7449747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449747).length < 2 ^ (prefixWord ++ tailWord_7449747).sum := by decide
  have hdescent : baseEnd_7449747 < baseStart_7449747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449754 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 4, 4]
def baseStart_7449754 : Nat := 118140960795 + 7449754 * 2 ^ 59
def prefixEnd_7449754 : Nat := 4983230072969 + 3 ^ 40 * 7449754 * 2
def baseEnd_7449754 : Nat := 1275101519918317012304737

theorem tailTrace_7449754 : CollatzResearch.WordTrace tailWord_7449754 prefixEnd_7449754 1275101519918317012304737 := by
  unfold tailWord_7449754
  simp only [CollatzResearch.WordTrace]
  refine ⟨67928712663205262383501079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181143233768547366356002877 67928712663205262383501079)
  ·
    refine ⟨101893068994807893575251619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67928712663205262383501079 101893068994807893575251619)
    ·
      refine ⟨152839603492211840362877429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101893068994807893575251619 152839603492211840362877429)
      ·
        refine ⟨14328712827394860034019759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152839603492211840362877429 14328712827394860034019759)
        ·
          refine ⟨21493069241092290051029639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14328712827394860034019759 21493069241092290051029639)
          ·
            refine ⟨32239603861638435076544459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21493069241092290051029639 32239603861638435076544459)
            ·
              refine ⟨48359405792457652614816689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32239603861638435076544459 48359405792457652614816689)
              ·
                refine ⟨36269554344343239461112517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48359405792457652614816689 36269554344343239461112517)
                ·
                  refine ⟨6800541439564357398958597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36269554344343239461112517 6800541439564357398958597)
                  ·
                    refine ⟨1275101519918317012304737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6800541439564357398958597 1275101519918317012304737)
                    ·
                      rfl

theorem cell23_7449754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_7449754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449754 prefixEnd_7449754 := by exact prefixLift 7449754
  have htrace : WordTrace (prefixWord ++ tailWord_7449754) baseStart_7449754 baseEnd_7449754 := by
    simpa [prefixWord, tailWord_7449754, baseEnd_7449754] using wordTrace_append hprefix tailTrace_7449754
  have hstable : (prefixWord ++ tailWord_7449754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449754).length < 2 ^ (prefixWord ++ tailWord_7449754).sum := by decide
  have hdescent : baseEnd_7449754 < baseStart_7449754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449757 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_7449757 : Nat := 118140960795 + 7449757 * 2 ^ 59
def prefixEnd_7449757 : Nat := 4983230072969 + 3 ^ 40 * 7449757 * 2
def baseEnd_7449757 : Nat := 3825306100196914525176697

theorem tailTrace_7449757 : CollatzResearch.WordTrace tailWord_7449757 prefixEnd_7449757 3825306100196914525176697 := by
  unfold tailWord_7449757
  simp only [CollatzResearch.WordTrace]
  refine ⟨271714960071810181046363525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181143306714540120697575683 271714960071810181046363525)
  ·
    refine ⟨50946555013464408946193161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271714960071810181046363525 50946555013464408946193161)
    ·
      refine ⟨38209916260098306709644871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50946555013464408946193161 38209916260098306709644871)
      ·
        refine ⟨57314874390147460064467307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38209916260098306709644871 57314874390147460064467307)
        ·
          refine ⟨85972311585221190096700961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57314874390147460064467307 85972311585221190096700961)
          ·
            refine ⟨64479233688915892572525721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85972311585221190096700961 64479233688915892572525721)
            ·
              refine ⟨48359425266686919429394291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64479233688915892572525721 48359425266686919429394291)
              ·
                refine ⟨72539137900030379144091437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48359425266686919429394291 72539137900030379144091437)
                ·
                  refine ⟨27202176712511392179034289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72539137900030379144091437 27202176712511392179034289)
                  ·
                    refine ⟨20401632534383544134275717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27202176712511392179034289 20401632534383544134275717)
                    ·
                      refine ⟨3825306100196914525176697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20401632534383544134275717 3825306100196914525176697)
                      ·
                        rfl

theorem cell23_7449757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_7449757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449757 prefixEnd_7449757 := by exact prefixLift 7449757
  have htrace : WordTrace (prefixWord ++ tailWord_7449757) baseStart_7449757 baseEnd_7449757 := by
    simpa [prefixWord, tailWord_7449757, baseEnd_7449757] using wordTrace_append hprefix tailTrace_7449757
  have hstable : (prefixWord ++ tailWord_7449757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449757).length < 2 ^ (prefixWord ++ tailWord_7449757).sum := by decide
  have hdescent : baseEnd_7449757 < baseStart_7449757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449764 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 1, 1, 5]
def baseStart_7449764 : Nat := 118140960795 + 7449764 * 2 ^ 59
def prefixEnd_7449764 : Nat := 4983230072969 + 3 ^ 40 * 7449764 * 2
def baseEnd_7449764 : Nat := 3825309694561495997789165

theorem tailTrace_7449764 : CollatzResearch.WordTrace tailWord_7449764 prefixEnd_7449764 3825309694561495997789165 := by
  unfold tailWord_7449764
  simp only [CollatzResearch.WordTrace]
  refine ⟨135857607691392410620934173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181143476921856547494578897 135857607691392410620934173)
  ·
    refine ⟨50946602884272153982850315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135857607691392410620934173 50946602884272153982850315)
    ·
      refine ⟨76419904326408230974275473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50946602884272153982850315 76419904326408230974275473)
      ·
        refine ⟨57314928244806173230706605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76419904326408230974275473 57314928244806173230706605)
        ·
          refine ⟨21493098091802314961514977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57314928244806173230706605 21493098091802314961514977)
          ·
            refine ⟨16119823568851736221136233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21493098091802314961514977 16119823568851736221136233)
            ·
              refine ⟨12089867676638802165852175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16119823568851736221136233 12089867676638802165852175)
              ·
                refine ⟨18134801514958203248778263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12089867676638802165852175 18134801514958203248778263)
                ·
                  refine ⟨27202202272437304873167395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18134801514958203248778263 27202202272437304873167395)
                  ·
                    refine ⟨40803303408655957309751093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27202202272437304873167395 40803303408655957309751093)
                    ·
                      refine ⟨3825309694561495997789165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40803303408655957309751093 3825309694561495997789165)
                      ·
                        rfl

theorem cell23_7449764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_7449764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449764 prefixEnd_7449764 := by exact prefixLift 7449764
  have htrace : WordTrace (prefixWord ++ tailWord_7449764) baseStart_7449764 baseEnd_7449764 := by
    simpa [prefixWord, tailWord_7449764, baseEnd_7449764] using wordTrace_append hprefix tailTrace_7449764
  have hstable : (prefixWord ++ tailWord_7449764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449764).length < 2 ^ (prefixWord ++ tailWord_7449764).sum := by decide
  have hdescent : baseEnd_7449764 < baseStart_7449764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449767 : List Nat := [1, 1, 6, 2, 1, 1, 11]
def baseStart_7449767 : Nat := 118140960795 + 7449767 * 2 ^ 59
def prefixEnd_7449767 : Nat := 4983230072969 + 3 ^ 40 * 7449767 * 2
def baseEnd_7449767 : Nat := 47226064629672339333971

theorem tailTrace_7449767 : CollatzResearch.WordTrace tailWord_7449767 prefixEnd_7449767 47226064629672339333971 := by
  unfold tailWord_7449767
  simp only [CollatzResearch.WordTrace]
  refine ⟨271715324801773952754227555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181143549867849301836151703 271715324801773952754227555)
  ·
    refine ⟨407572987202660929131341333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271715324801773952754227555 407572987202660929131341333)
    ·
      refine ⟨19104983775124731053031625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 407572987202660929131341333 19104983775124731053031625)
      ·
        refine ⟨14328737831343548289773719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19104983775124731053031625 14328737831343548289773719)
        ·
          refine ⟨21493106747015322434660579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14328737831343548289773719 21493106747015322434660579)
          ·
            refine ⟨32239660120522983651990869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21493106747015322434660579 32239660120522983651990869)
            ·
              refine ⟨47226064629672339333971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32239660120522983651990869 47226064629672339333971)
              ·
                rfl

theorem cell23_7449767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 11].length) (baseStart_7449767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449767 prefixEnd_7449767 := by exact prefixLift 7449767
  have htrace : WordTrace (prefixWord ++ tailWord_7449767) baseStart_7449767 baseEnd_7449767 := by
    simpa [prefixWord, tailWord_7449767, baseEnd_7449767] using wordTrace_append hprefix tailTrace_7449767
  have hstable : (prefixWord ++ tailWord_7449767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449767).length < 2 ^ (prefixWord ++ tailWord_7449767).sum := by decide
  have hdescent : baseEnd_7449767 < baseStart_7449767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449778 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2]
def baseStart_7449778 : Nat := 118140960795 + 7449778 * 2 ^ 59
def prefixEnd_7449778 : Nat := 4983230072969 + 3 ^ 40 * 7449778 * 2
def baseEnd_7449778 : Nat := 3825316883290658943014101

theorem tailTrace_7449778 : CollatzResearch.WordTrace tailWord_7449778 prefixEnd_7449778 3825316883290658943014101 := by
  unfold tailWord_7449778
  simp only [CollatzResearch.WordTrace]
  refine ⟨67928931501183525408219497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181143817336489401088585325 67928931501183525408219497)
  ·
    refine ⟨50946698625887644056164623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67928931501183525408219497 50946698625887644056164623)
    ·
      refine ⟨76420047938831466084246935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50946698625887644056164623 76420047938831466084246935)
      ·
        refine ⟨114630071908247199126370403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76420047938831466084246935 114630071908247199126370403)
        ·
          refine ⟨171945107862370798689555605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114630071908247199126370403 171945107862370798689555605)
          ·
            refine ⟨8059926931048631188572919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 171945107862370798689555605 8059926931048631188572919)
            ·
              refine ⟨12089890396572946782859379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8059926931048631188572919 12089890396572946782859379)
              ·
                refine ⟨18134835594859420174289069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12089890396572946782859379 18134835594859420174289069)
                ·
                  refine ⟨6800563348072282565358401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18134835594859420174289069 6800563348072282565358401)
                  ·
                    refine ⟨5100422511054211924018801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6800563348072282565358401 5100422511054211924018801)
                    ·
                      refine ⟨3825316883290658943014101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100422511054211924018801 3825316883290658943014101)
                      ·
                        rfl

theorem cell23_7449778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_7449778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449778 prefixEnd_7449778 := by exact prefixLift 7449778
  have htrace : WordTrace (prefixWord ++ tailWord_7449778) baseStart_7449778 baseEnd_7449778 := by
    simpa [prefixWord, tailWord_7449778, baseEnd_7449778] using wordTrace_append hprefix tailTrace_7449778
  have hstable : (prefixWord ++ tailWord_7449778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449778).length < 2 ^ (prefixWord ++ tailWord_7449778).sum := by decide
  have hdescent : baseEnd_7449778 < baseStart_7449778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449788 : List Nat := [2, 2, 2, 3, 2, 3, 2, 1, 2, 4]
def baseStart_7449788 : Nat := 118140960795 + 7449788 * 2 ^ 59
def prefixEnd_7449788 : Nat := 4983230072969 + 3 ^ 40 * 7449788 * 2
def baseEnd_7449788 : Nat := 1275107339365734634629685

theorem tailTrace_7449788 : CollatzResearch.WordTrace tailWord_7449788 prefixEnd_7449788 1275107339365734634629685 := by
  unfold tailWord_7449788
  simp only [CollatzResearch.WordTrace]
  refine ⟨135858045367348936670371009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181144060489798582227161345 135858045367348936670371009)
  ·
    refine ⟨101893534025511702502778257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135858045367348936670371009 101893534025511702502778257)
    ·
      refine ⟨76420150519133776877083693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101893534025511702502778257 76420150519133776877083693)
      ·
        refine ⟨28657556444675166328906385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76420150519133776877083693 28657556444675166328906385)
        ·
          refine ⟨21493167333506374746679789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28657556444675166328906385 21493167333506374746679789)
          ·
            refine ⟨8059937750064890530004921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21493167333506374746679789 8059937750064890530004921)
            ·
              refine ⟨6044953312548667897503691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8059937750064890530004921 6044953312548667897503691)
              ·
                refine ⟨9067429968823001846255537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6044953312548667897503691 9067429968823001846255537)
                ·
                  refine ⟨6800572476617251384691653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9067429968823001846255537 6800572476617251384691653)
                  ·
                    refine ⟨1275107339365734634629685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6800572476617251384691653 1275107339365734634629685)
                    ·
                      rfl

theorem cell23_7449788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_7449788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449788 prefixEnd_7449788 := by exact prefixLift 7449788
  have htrace : WordTrace (prefixWord ++ tailWord_7449788) baseStart_7449788 baseEnd_7449788 := by
    simpa [prefixWord, tailWord_7449788, baseEnd_7449788] using wordTrace_append hprefix tailTrace_7449788
  have hstable : (prefixWord ++ tailWord_7449788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449788).length < 2 ^ (prefixWord ++ tailWord_7449788).sum := by decide
  have hdescent : baseEnd_7449788 < baseStart_7449788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449829 : List Nat := [1, 3, 1, 4, 4, 1, 2, 2, 1, 2, 2]
def baseStart_7449829 : Nat := 118140960795 + 7449829 * 2 ^ 59
def prefixEnd_7449829 : Nat := 4983230072969 + 3 ^ 40 * 7449829 * 2
def baseEnd_7449829 : Nat := 3825343070804038243476367

theorem tailTrace_7449829 : CollatzResearch.WordTrace tailWord_7449829 prefixEnd_7449829 3825343070804038243476367 := by
  unfold tailWord_7449829
  simp only [CollatzResearch.WordTrace]
  refine ⟨271717586127549337342984541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181145057418366224895323027 271717586127549337342984541)
  ·
    refine ⟨101894094797831001503619203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271717586127549337342984541 101894094797831001503619203)
    ·
      refine ⟨152841142196746502255428805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101894094797831001503619203 152841142196746502255428805)
      ·
        refine ⟨28657714161889969172892901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152841142196746502255428805 28657714161889969172892901)
        ·
          refine ⟨5373321405354369219917419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28657714161889969172892901 5373321405354369219917419)
          ·
            refine ⟨8059982108031553829876129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5373321405354369219917419 8059982108031553829876129)
            ·
              refine ⟨6044986581023665372407097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8059982108031553829876129 6044986581023665372407097)
              ·
                refine ⟨4533739935767749029305323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6044986581023665372407097 4533739935767749029305323)
                ·
                  refine ⟨6800609903651623543957985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533739935767749029305323 6800609903651623543957985)
                  ·
                    refine ⟨5100457427738717657968489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6800609903651623543957985 5100457427738717657968489)
                    ·
                      refine ⟨3825343070804038243476367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100457427738717657968489 3825343070804038243476367)
                      ·
                        rfl

theorem cell23_7449829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_7449829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449829 prefixEnd_7449829 := by exact prefixLift 7449829
  have htrace : WordTrace (prefixWord ++ tailWord_7449829) baseStart_7449829 baseEnd_7449829 := by
    simpa [prefixWord, tailWord_7449829, baseEnd_7449829] using wordTrace_append hprefix tailTrace_7449829
  have hstable : (prefixWord ++ tailWord_7449829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449829).length < 2 ^ (prefixWord ++ tailWord_7449829).sum := by decide
  have hdescent : baseEnd_7449829 < baseStart_7449829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449847 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 4]
def baseStart_7449847 : Nat := 118140960795 + 7449847 * 2 ^ 59
def prefixEnd_7449847 : Nat := 4983230072969 + 3 ^ 40 * 7449847 * 2
def baseEnd_7449847 : Nat := 3825352313455819173051283

theorem tailTrace_7449847 : CollatzResearch.WordTrace tailWord_7449847 prefixEnd_7449847 3825352313455819173051283 := by
  unfold tailWord_7449847
  simp only [CollatzResearch.WordTrace]
  refine ⟨271718242641484126417139795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181145495094322750944759863 271718242641484126417139795)
  ·
    refine ⟨407577363962226189625709693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271718242641484126417139795 407577363962226189625709693)
    ·
      refine ⟨152841511485834821109641135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 407577363962226189625709693 152841511485834821109641135)
      ·
        refine ⟨229262267228752231664461703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152841511485834821109641135 229262267228752231664461703)
        ·
          refine ⟨343893400843128347496692555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229262267228752231664461703 343893400843128347496692555)
          ·
            refine ⟨515840101264692521245038833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343893400843128347496692555 515840101264692521245038833)
            ·
              refine ⟨386880075948519390933779125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515840101264692521245038833 386880075948519390933779125)
              ·
                refine ⟨36270007120173692900041793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 386880075948519390933779125 36270007120173692900041793)
                ·
                  refine ⟨27202505340130269675031345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36270007120173692900041793 27202505340130269675031345)
                  ·
                    refine ⟨20401879005097702256273509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27202505340130269675031345 20401879005097702256273509)
                    ·
                      refine ⟨3825352313455819173051283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20401879005097702256273509 3825352313455819173051283)
                      ·
                        rfl

theorem cell23_7449847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_7449847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449847 prefixEnd_7449847 := by exact prefixLift 7449847
  have htrace : WordTrace (prefixWord ++ tailWord_7449847) baseStart_7449847 baseEnd_7449847 := by
    simpa [prefixWord, tailWord_7449847, baseEnd_7449847] using wordTrace_append hprefix tailTrace_7449847
  have hstable : (prefixWord ++ tailWord_7449847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449847).length < 2 ^ (prefixWord ++ tailWord_7449847).sum := by decide
  have hdescent : baseEnd_7449847 < baseStart_7449847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449857 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 9]
def baseStart_7449857 : Nat := 118140960795 + 7449857 * 2 ^ 59
def prefixEnd_7449857 : Nat := 4983230072969 + 3 ^ 40 * 7449857 * 2
def baseEnd_7449857 : Nat := 425039716473596014880693

theorem tailTrace_7449857 : CollatzResearch.WordTrace tailWord_7449857 prefixEnd_7449857 425039716473596014880693 := by
  unfold tailWord_7449857
  simp only [CollatzResearch.WordTrace]
  refine ⟨271718607371447898125003825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181145738247631932083335883 271718607371447898125003825)
  ·
    refine ⟨203788955528585923593752869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271718607371447898125003825 203788955528585923593752869)
    ·
      refine ⟨38210429161609860673828663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203788955528585923593752869 38210429161609860673828663)
      ·
        refine ⟨57315643742414791010742995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38210429161609860673828663 57315643742414791010742995)
        ·
          refine ⟨85973465613622186516114493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57315643742414791010742995 85973465613622186516114493)
          ·
            refine ⟨32240049605108319943542935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85973465613622186516114493 32240049605108319943542935)
            ·
              refine ⟨48360074407662479915314403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32240049605108319943542935 48360074407662479915314403)
              ·
                refine ⟨72540111611493719872971605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48360074407662479915314403 72540111611493719872971605)
                ·
                  refine ⟨425039716473596014880693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72540111611493719872971605 425039716473596014880693)
                  ·
                    rfl

theorem cell23_7449857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 9].length) (baseStart_7449857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449857 prefixEnd_7449857 := by exact prefixLift 7449857
  have htrace : WordTrace (prefixWord ++ tailWord_7449857) baseStart_7449857 baseEnd_7449857 := by
    simpa [prefixWord, tailWord_7449857, baseEnd_7449857] using wordTrace_append hprefix tailTrace_7449857
  have hstable : (prefixWord ++ tailWord_7449857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449857).length < 2 ^ (prefixWord ++ tailWord_7449857).sum := by decide
  have hdescent : baseEnd_7449857 < baseStart_7449857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449884 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_7449884 : Nat := 118140960795 + 7449884 * 2 ^ 59
def prefixEnd_7449884 : Nat := 4983230072969 + 3 ^ 40 * 7449884 * 2
def baseEnd_7449884 : Nat := 3825371312240035528288613

theorem tailTrace_7449884 : CollatzResearch.WordTrace tailWord_7449884 prefixEnd_7449884 3825371312240035528288613 := by
  unfold tailWord_7449884
  simp only [CollatzResearch.WordTrace]
  refine ⟨135859796071175040868118353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181146394761566721157491137 135859796071175040868118353)
  ·
    refine ⟨101894847053381280651088765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135859796071175040868118353 101894847053381280651088765)
    ·
      refine ⟨38210567645017980244158287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101894847053381280651088765 38210567645017980244158287)
      ·
        refine ⟨57315851467526970366237431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38210567645017980244158287 57315851467526970366237431)
        ·
          refine ⟨85973777201290455549356147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57315851467526970366237431 85973777201290455549356147)
          ·
            refine ⟨128960665801935683324034221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85973777201290455549356147 128960665801935683324034221)
            ·
              refine ⟨48360249675725881246512833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128960665801935683324034221 48360249675725881246512833)
              ·
                refine ⟨36270187256794410934884625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48360249675725881246512833 36270187256794410934884625)
                ·
                  refine ⟨27202640442595808201163469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36270187256794410934884625 27202640442595808201163469)
                  ·
                    refine ⟨10200990165973428075436301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27202640442595808201163469 10200990165973428075436301)
                    ·
                      refine ⟨3825371312240035528288613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10200990165973428075436301 3825371312240035528288613)
                      ·
                        rfl

theorem cell23_7449884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_7449884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449884 prefixEnd_7449884 := by exact prefixLift 7449884
  have htrace : WordTrace (prefixWord ++ tailWord_7449884) baseStart_7449884 baseEnd_7449884 := by
    simpa [prefixWord, tailWord_7449884, baseEnd_7449884] using wordTrace_append hprefix tailTrace_7449884
  have hstable : (prefixWord ++ tailWord_7449884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449884).length < 2 ^ (prefixWord ++ tailWord_7449884).sum := by decide
  have hdescent : baseEnd_7449884 < baseStart_7449884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449885 : List Nat := [1, 4, 2, 3, 1, 1, 3, 2, 2, 2, 2]
def baseStart_7449885 : Nat := 118140960795 + 7449885 * 2 ^ 59
def prefixEnd_7449885 : Nat := 4983230072969 + 3 ^ 40 * 7449885 * 2
def baseEnd_7449885 : Nat := 3825371825720690024376109

theorem tailTrace_7449885 : CollatzResearch.WordTrace tailWord_7449885 prefixEnd_7449885 3825371825720690024376109 := by
  unfold tailWord_7449885
  simp only [CollatzResearch.WordTrace]
  refine ⟨271719628615346458907023109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181146419076897639271348739 271719628615346458907023109)
  ·
    refine ⟨50947430365377461045066833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271719628615346458907023109 50947430365377461045066833)
    ·
      refine ⟨38210572774033095783800125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50947430365377461045066833 38210572774033095783800125)
      ·
        refine ⟨14328964790262410918925047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38210572774033095783800125 14328964790262410918925047)
        ·
          refine ⟨21493447185393616378387571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14328964790262410918925047 21493447185393616378387571)
          ·
            refine ⟨32240170778090424567581357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21493447185393616378387571 32240170778090424567581357)
            ·
              refine ⟨12090064041783909212843009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32240170778090424567581357 12090064041783909212843009)
              ·
                refine ⟨9067548031337931909632257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12090064041783909212843009 9067548031337931909632257)
                ·
                  refine ⟨6800661023503448932224193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9067548031337931909632257 6800661023503448932224193)
                  ·
                    refine ⟨5100495767627586699168145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6800661023503448932224193 5100495767627586699168145)
                    ·
                      refine ⟨3825371825720690024376109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100495767627586699168145 3825371825720690024376109)
                      ·
                        rfl

theorem cell23_7449885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_7449885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449885 prefixEnd_7449885 := by exact prefixLift 7449885
  have htrace : WordTrace (prefixWord ++ tailWord_7449885) baseStart_7449885 baseEnd_7449885 := by
    simpa [prefixWord, tailWord_7449885, baseEnd_7449885] using wordTrace_append hprefix tailTrace_7449885
  have hstable : (prefixWord ++ tailWord_7449885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449885).length < 2 ^ (prefixWord ++ tailWord_7449885).sum := by decide
  have hdescent : baseEnd_7449885 < baseStart_7449885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449941 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_7449941 : Nat := 118140960795 + 7449941 * 2 ^ 59
def prefixEnd_7449941 : Nat := 4983230072969 + 3 ^ 40 * 7449941 * 2
def baseEnd_7449941 : Nat := 3825400580637341805275851

theorem tailTrace_7449941 : CollatzResearch.WordTrace tailWord_7449941 prefixEnd_7449941 3825400580637341805275851 := by
  unfold tailWord_7449941
  simp only [CollatzResearch.WordTrace]
  refine ⟨271721671103143580471061677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181147780735429053647374451 271721671103143580471061677)
  ·
    refine ⟨101895626663678842676648129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271721671103143580471061677 101895626663678842676648129)
    ·
      refine ⟨76421719997759132007486097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101895626663678842676648129 76421719997759132007486097)
      ·
        refine ⟨57316289998319349005614573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76421719997759132007486097 57316289998319349005614573)
        ·
          refine ⟨21493608749369755877105465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57316289998319349005614573 21493608749369755877105465)
          ·
            refine ⟨16120206562027316907829099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21493608749369755877105465 16120206562027316907829099)
            ·
              refine ⟨24180309843040975361743649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16120206562027316907829099 24180309843040975361743649)
              ·
                refine ⟨18135232382280731521307737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24180309843040975361743649 18135232382280731521307737)
                ·
                  refine ⟨13601424286710548640980803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18135232382280731521307737 13601424286710548640980803)
                  ·
                    refine ⟨20402136430065822961471205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13601424286710548640980803 20402136430065822961471205)
                    ·
                      refine ⟨3825400580637341805275851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20402136430065822961471205 3825400580637341805275851)
                      ·
                        rfl

theorem cell23_7449941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_7449941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449941 prefixEnd_7449941 := by exact prefixLift 7449941
  have htrace : WordTrace (prefixWord ++ tailWord_7449941) baseStart_7449941 baseEnd_7449941 := by
    simpa [prefixWord, tailWord_7449941, baseEnd_7449941] using wordTrace_append hprefix tailTrace_7449941
  have hstable : (prefixWord ++ tailWord_7449941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449941).length < 2 ^ (prefixWord ++ tailWord_7449941).sum := by decide
  have hdescent : baseEnd_7449941 < baseStart_7449941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449942 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 7]
def baseStart_7449942 : Nat := 118140960795 + 7449942 * 2 ^ 59
def prefixEnd_7449942 : Nat := 4983230072969 + 3 ^ 40 * 7449942 * 2
def baseEnd_7449942 : Nat := 425044566013110700151483

theorem tailTrace_7449942 : CollatzResearch.WordTrace tailWord_7449942 prefixEnd_7449942 425044566013110700151483 := by
  unfold tailWord_7449942
  simp only [CollatzResearch.WordTrace]
  refine ⟨16982606723508747352615505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 181147805050759971761232053 16982606723508747352615505)
  ·
    refine ⟨12736955042631560514461629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16982606723508747352615505 12736955042631560514461629)
    ·
      refine ⟨4776358140986835192923111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12736955042631560514461629 4776358140986835192923111)
      ·
        refine ⟨7164537211480252789384667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4776358140986835192923111 7164537211480252789384667)
        ·
          refine ⟨10746805817220379184077001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7164537211480252789384667 10746805817220379184077001)
          ·
            refine ⟨8060104362915284388057751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10746805817220379184077001 8060104362915284388057751)
            ·
              refine ⟨12090156544372926582086627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8060104362915284388057751 12090156544372926582086627)
              ·
                refine ⟨18135234816559389873129941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12090156544372926582086627 18135234816559389873129941)
                ·
                  refine ⟨425044566013110700151483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18135234816559389873129941 425044566013110700151483)
                  ·
                    rfl

theorem cell23_7449942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_7449942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449942 prefixEnd_7449942 := by exact prefixLift 7449942
  have htrace : WordTrace (prefixWord ++ tailWord_7449942) baseStart_7449942 baseEnd_7449942 := by
    simpa [prefixWord, tailWord_7449942, baseEnd_7449942] using wordTrace_append hprefix tailTrace_7449942
  have hstable : (prefixWord ++ tailWord_7449942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449942).length < 2 ^ (prefixWord ++ tailWord_7449942).sum := by decide
  have hdescent : baseEnd_7449942 < baseStart_7449942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7449998 : List Nat := [4, 1, 1, 4, 2, 1, 2, 2, 6]
def baseStart_7449998 : Nat := 118140960795 + 7449998 * 2 ^ 59
def prefixEnd_7449998 : Nat := 4983230072969 + 3 ^ 40 * 7449998 * 2
def baseEnd_7449998 : Nat := 425047761003849786918121

theorem tailTrace_7449998 : CollatzResearch.WordTrace tailWord_7449998 prefixEnd_7449998 425047761003849786918121 := by
  unfold tailWord_7449998
  simp only [CollatzResearch.WordTrace]
  refine ⟨33965468757992134900735831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181149166709291386137257765 33965468757992134900735831)
  ·
    refine ⟨50948203136988202351103747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33965468757992134900735831 50948203136988202351103747)
    ·
      refine ⟨76422304705482303526655621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50948203136988202351103747 76422304705482303526655621)
      ·
        refine ⟨14329182132277931911247929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76422304705482303526655621 14329182132277931911247929)
        ·
          refine ⟨10746886599208448933435947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14329182132277931911247929 10746886599208448933435947)
          ·
            refine ⟨16120329898812673400153921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10746886599208448933435947 16120329898812673400153921)
            ·
              refine ⟨12090247424109505050115441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16120329898812673400153921 12090247424109505050115441)
              ·
                refine ⟨9067685568082128787586581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12090247424109505050115441 9067685568082128787586581)
                ·
                  refine ⟨425047761003849786918121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9067685568082128787586581 425047761003849786918121)
                  ·
                    rfl

theorem cell23_7449998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_7449998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7449998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7449998 prefixEnd_7449998 := by exact prefixLift 7449998
  have htrace : WordTrace (prefixWord ++ tailWord_7449998) baseStart_7449998 baseEnd_7449998 := by
    simpa [prefixWord, tailWord_7449998, baseEnd_7449998] using wordTrace_append hprefix tailTrace_7449998
  have hstable : (prefixWord ++ tailWord_7449998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7449998).length < 2 ^ (prefixWord ++ tailWord_7449998).sum := by decide
  have hdescent : baseEnd_7449998 < baseStart_7449998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7449998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450002 : List Nat := [3, 2, 3, 3, 1, 1, 1, 4, 1, 4]
def baseStart_7450002 : Nat := 118140960795 + 7450002 * 2 ^ 59
def prefixEnd_7450002 : Nat := 4983230072969 + 3 ^ 40 * 7450002 * 2
def baseEnd_7450002 : Nat := 1275143967652422022204357

theorem tailTrace_7450002 : CollatzResearch.WordTrace tailWord_7450002 prefixEnd_7450002 1275143967652422022204357 := by
  unfold tailWord_7450002
  simp only [CollatzResearch.WordTrace]
  refine ⟨67930973988980646972258065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181149263970615058592688173 67930973988980646972258065)
  ·
    refine ⟨50948230491735485229193549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67930973988980646972258065 50948230491735485229193549)
    ·
      refine ⟨19105586434400806960947581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50948230491735485229193549 19105586434400806960947581)
      ·
        refine ⟨7164594912900302610355343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19105586434400806960947581 7164594912900302610355343)
        ·
          refine ⟨10746892369350453915533015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7164594912900302610355343 10746892369350453915533015)
          ·
            refine ⟨16120338554025680873299523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10746892369350453915533015 16120338554025680873299523)
            ·
              refine ⟨24180507831038521309949285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16120338554025680873299523 24180507831038521309949285)
              ·
                refine ⟨4533845218319722745615491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24180507831038521309949285 4533845218319722745615491)
                ·
                  refine ⟨6800767827479584118423237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533845218319722745615491 6800767827479584118423237)
                  ·
                    refine ⟨1275143967652422022204357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6800767827479584118423237 1275143967652422022204357)
                    ·
                      rfl

theorem cell23_7450002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_7450002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450002 prefixEnd_7450002 := by exact prefixLift 7450002
  have htrace : WordTrace (prefixWord ++ tailWord_7450002) baseStart_7450002 baseEnd_7450002 := by
    simpa [prefixWord, tailWord_7450002, baseEnd_7450002] using wordTrace_append hprefix tailTrace_7450002
  have hstable : (prefixWord ++ tailWord_7450002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450002).length < 2 ^ (prefixWord ++ tailWord_7450002).sum := by decide
  have hdescent : baseEnd_7450002 < baseStart_7450002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450034 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_7450034 : Nat := 118140960795 + 7450034 * 2 ^ 59
def prefixEnd_7450034 : Nat := 4983230072969 + 3 ^ 40 * 7450034 * 2
def baseEnd_7450034 : Nat := 3825448334338209941412923

theorem tailTrace_7450034 : CollatzResearch.WordTrace tailWord_7450034 prefixEnd_7450034 3825448334338209941412923 := by
  unfold tailWord_7450034
  simp only [CollatzResearch.WordTrace]
  refine ⟨67931265772951664338549289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181150042061204438236131437 67931265772951664338549289)
  ·
    refine ⟨50948449329713748253911967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67931265772951664338549289 50948449329713748253911967)
    ·
      refine ⟨76422673994570622380867951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50948449329713748253911967 76422673994570622380867951)
      ·
        refine ⟨114634010991855933571301927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76422673994570622380867951 114634010991855933571301927)
        ·
          refine ⟨171951016487783900356952891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114634010991855933571301927 171951016487783900356952891)
          ·
            refine ⟨257926524731675850535429337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171951016487783900356952891 257926524731675850535429337)
            ·
              refine ⟨193444893548756887901572003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257926524731675850535429337 193444893548756887901572003)
              ·
                refine ⟨290167340323135331852358005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193444893548756887901572003 290167340323135331852358005)
                ·
                  refine ⟨27203188155293937361158563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 290167340323135331852358005 27203188155293937361158563)
                  ·
                    refine ⟨40804782232940906041737845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27203188155293937361158563 40804782232940906041737845)
                    ·
                      refine ⟨3825448334338209941412923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40804782232940906041737845 3825448334338209941412923)
                      ·
                        rfl

theorem cell23_7450034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_7450034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450034 prefixEnd_7450034 := by exact prefixLift 7450034
  have htrace : WordTrace (prefixWord ++ tailWord_7450034) baseStart_7450034 baseEnd_7450034 := by
    simpa [prefixWord, tailWord_7450034, baseEnd_7450034] using wordTrace_append hprefix tailTrace_7450034
  have hstable : (prefixWord ++ tailWord_7450034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450034).length < 2 ^ (prefixWord ++ tailWord_7450034).sum := by decide
  have hdescent : baseEnd_7450034 < baseStart_7450034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450048 : List Nat := [2, 1, 1, 2, 3, 1, 6, 1, 1, 1, 4]
def baseStart_7450048 : Nat := 118140960795 + 7450048 * 2 ^ 59
def prefixEnd_7450048 : Nat := 4983230072969 + 3 ^ 40 * 7450048 * 2
def baseEnd_7450048 : Nat := 3825455523067372886637859

theorem tailTrace_7450048 : CollatzResearch.WordTrace tailWord_7450048 prefixEnd_7450048 3825455523067372886637859 := by
  unfold tailWord_7450048
  simp only [CollatzResearch.WordTrace]
  refine ⟨135862786856877968872603399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181150382475837291830137865 135862786856877968872603399)
  ·
    refine ⟨203794180285316953308905099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135862786856877968872603399 203794180285316953308905099)
    ·
      refine ⟨305691270427975429963357649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203794180285316953308905099 305691270427975429963357649)
      ·
        refine ⟨229268452820981572472518237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305691270427975429963357649 229268452820981572472518237)
        ·
          refine ⟨85975669807868089677194339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229268452820981572472518237 85975669807868089677194339)
          ·
            refine ⟨128963504711802134515791509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85975669807868089677194339 128963504711802134515791509)
            ·
              refine ⟨6045164283365725055427727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128963504711802134515791509 6045164283365725055427727)
              ·
                refine ⟨9067746425048587583141591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6045164283365725055427727 9067746425048587583141591)
                ·
                  refine ⟨13601619637572881374712387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9067746425048587583141591 13601619637572881374712387)
                  ·
                    refine ⟨20402429456359322062068581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13601619637572881374712387 20402429456359322062068581)
                    ·
                      refine ⟨3825455523067372886637859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20402429456359322062068581 3825455523067372886637859)
                      ·
                        rfl

theorem cell23_7450048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 1, 1, 4].length) (baseStart_7450048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450048 prefixEnd_7450048 := by exact prefixLift 7450048
  have htrace : WordTrace (prefixWord ++ tailWord_7450048) baseStart_7450048 baseEnd_7450048 := by
    simpa [prefixWord, tailWord_7450048, baseEnd_7450048] using wordTrace_append hprefix tailTrace_7450048
  have hstable : (prefixWord ++ tailWord_7450048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450048).length < 2 ^ (prefixWord ++ tailWord_7450048).sum := by decide
  have hdescent : baseEnd_7450048 < baseStart_7450048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450058 : List Nat := [3, 1, 2, 1, 2, 3, 3, 2, 2, 4]
def baseStart_7450058 : Nat := 118140960795 + 7450058 * 2 ^ 59
def prefixEnd_7450058 : Nat := 4983230072969 + 3 ^ 40 * 7450058 * 2
def baseEnd_7450058 : Nat := 1275153552624639282504271

theorem tailTrace_7450058 : CollatzResearch.WordTrace tailWord_7450058 prefixEnd_7450058 1275153552624639282504271 := by
  unfold tailWord_7450058
  simp only [CollatzResearch.WordTrace]
  refine ⟨67931484610929927363267707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181150625629146472968713885 67931484610929927363267707)
  ·
    refine ⟨101897226916394891044901561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67931484610929927363267707 101897226916394891044901561)
    ·
      refine ⟨76422920187296168283676171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101897226916394891044901561 76422920187296168283676171)
      ·
        refine ⟨114634380280944252425514257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76422920187296168283676171 114634380280944252425514257)
        ·
          refine ⟨85975785210708189319135693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114634380280944252425514257 85975785210708189319135693)
          ·
            refine ⟨32240919454015570994675885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85975785210708189319135693 32240919454015570994675885)
            ·
              refine ⟨12090344795255839123003457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32240919454015570994675885 12090344795255839123003457)
              ·
                refine ⟨9067758596441879342252593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12090344795255839123003457 9067758596441879342252593)
                ·
                  refine ⟨6800818947331409506689445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9067758596441879342252593 6800818947331409506689445)
                  ·
                    refine ⟨1275153552624639282504271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6800818947331409506689445 1275153552624639282504271)
                    ·
                      rfl

theorem cell23_7450058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_7450058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450058 prefixEnd_7450058 := by exact prefixLift 7450058
  have htrace : WordTrace (prefixWord ++ tailWord_7450058) baseStart_7450058 baseEnd_7450058 := by
    simpa [prefixWord, tailWord_7450058, baseEnd_7450058] using wordTrace_append hprefix tailTrace_7450058
  have hstable : (prefixWord ++ tailWord_7450058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450058).length < 2 ^ (prefixWord ++ tailWord_7450058).sum := by decide
  have hdescent : baseEnd_7450058 < baseStart_7450058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450068 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_7450068 : Nat := 118140960795 + 7450068 * 2 ^ 59
def prefixEnd_7450068 : Nat := 4983230072969 + 3 ^ 40 * 7450068 * 2
def baseEnd_7450068 : Nat := 3825465792680462808387767

theorem tailTrace_7450068 : CollatzResearch.WordTrace tailWord_7450068 prefixEnd_7450068 3825465792680462808387767 := by
  unfold tailWord_7450068
  simp only [CollatzResearch.WordTrace]
  refine ⟨135863151586841740580467429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181150868782455654107289905 135863151586841740580467429)
  ·
    refine ⟨25474340922532826358837643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135863151586841740580467429 25474340922532826358837643)
    ·
      refine ⟨38211511383799239538256465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25474340922532826358837643 38211511383799239538256465)
      ·
        refine ⟨28658633537849429653692349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38211511383799239538256465 28658633537849429653692349)
        ·
          refine ⟨10746987576693536120134631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28658633537849429653692349 10746987576693536120134631)
          ·
            refine ⟨16120481365040304180201947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10746987576693536120134631 16120481365040304180201947)
            ·
              refine ⟨24180722047560456270302921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16120481365040304180201947 24180722047560456270302921)
              ·
                refine ⟨18135541535670342202727191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24180722047560456270302921 18135541535670342202727191)
                ·
                  refine ⟨27203312303505513304090787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18135541535670342202727191 27203312303505513304090787)
                  ·
                    refine ⟨40804968455258269956136181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27203312303505513304090787 40804968455258269956136181)
                    ·
                      refine ⟨3825465792680462808387767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40804968455258269956136181 3825465792680462808387767)
                      ·
                        rfl

theorem cell23_7450068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_7450068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450068 prefixEnd_7450068 := by exact prefixLift 7450068
  have htrace : WordTrace (prefixWord ++ tailWord_7450068) baseStart_7450068 baseEnd_7450068 := by
    simpa [prefixWord, tailWord_7450068, baseEnd_7450068] using wordTrace_append hprefix tailTrace_7450068
  have hstable : (prefixWord ++ tailWord_7450068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450068).length < 2 ^ (prefixWord ++ tailWord_7450068).sum := by decide
  have hdescent : baseEnd_7450068 < baseStart_7450068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450084 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 2, 7]
def baseStart_7450084 : Nat := 118140960795 + 7450084 * 2 ^ 59
def prefixEnd_7450084 : Nat := 4983230072969 + 3 ^ 40 * 7450084 * 2
def baseEnd_7450084 : Nat := 1275158002790311581929231

theorem tailTrace_7450084 : CollatzResearch.WordTrace tailWord_7450084 prefixEnd_7450084 1275158002790311581929231 := by
  unfold tailWord_7450084
  simp only [CollatzResearch.WordTrace]
  refine ⟨135863443370812757946758653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181151257827750343929011537 135863443370812757946758653)
  ·
    refine ⟨50948791264054784230034495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135863443370812757946758653 50948791264054784230034495)
    ·
      refine ⟨76423186896082176345051743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50948791264054784230034495 76423186896082176345051743)
      ·
        refine ⟨114634780344123264517577615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76423186896082176345051743 114634780344123264517577615)
        ·
          refine ⟨171952170516184896776366423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114634780344123264517577615 171952170516184896776366423)
          ·
            refine ⟨257928255774277345164549635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171952170516184896776366423 257928255774277345164549635)
            ·
              refine ⟨386892383661416017746824453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257928255774277345164549635 386892383661416017746824453)
              ·
                refine ⟨72542321936515503327529585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 386892383661416017746824453 72542321936515503327529585)
                ·
                  refine ⟨54406741452386627495647189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72542321936515503327529585 54406741452386627495647189)
                  ·
                    refine ⟨1275158002790311581929231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54406741452386627495647189 1275158002790311581929231)
                    ·
                      rfl

theorem cell23_7450084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_7450084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450084 prefixEnd_7450084 := by exact prefixLift 7450084
  have htrace : WordTrace (prefixWord ++ tailWord_7450084) baseStart_7450084 baseEnd_7450084 := by
    simpa [prefixWord, tailWord_7450084, baseEnd_7450084] using wordTrace_append hprefix tailTrace_7450084
  have hstable : (prefixWord ++ tailWord_7450084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450084).length < 2 ^ (prefixWord ++ tailWord_7450084).sum := by decide
  have hdescent : baseEnd_7450084 < baseStart_7450084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450085 : List Nat := [1, 3, 1, 5, 1, 2, 2, 2, 1, 2, 3]
def baseStart_7450085 : Nat := 118140960795 + 7450085 * 2 ^ 59
def prefixEnd_7450085 : Nat := 4983230072969 + 3 ^ 40 * 7450085 * 2
def baseEnd_7450085 : Nat := 3825474521851589241875189

theorem tailTrace_7450085 : CollatzResearch.WordTrace tailWord_7450085 prefixEnd_7450085 3825474521851589241875189 := by
  unfold tailWord_7450085
  simp only [CollatzResearch.WordTrace]
  refine ⟨271726923214621893064303709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181151282143081262042869139 271726923214621893064303709)
  ·
    refine ⟨101897596205483209899113891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271726923214621893064303709 101897596205483209899113891)
    ·
      refine ⟨152846394308224814848670837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101897596205483209899113891 152846394308224814848670837)
      ·
        refine ⟨14329349466396076392062891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152846394308224814848670837 14329349466396076392062891)
        ·
          refine ⟨21494024199594114588094337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14329349466396076392062891 21494024199594114588094337)
          ·
            refine ⟨16120518149695585941070753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21494024199594114588094337 16120518149695585941070753)
            ·
              refine ⟨12090388612271689455803065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16120518149695585941070753 12090388612271689455803065)
              ·
                refine ⟨9067791459203767091852299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12090388612271689455803065 9067791459203767091852299)
                ·
                  refine ⟨13601687188805650637778449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9067791459203767091852299 13601687188805650637778449)
                  ·
                    refine ⟨10201265391604237978333837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13601687188805650637778449 10201265391604237978333837)
                    ·
                      refine ⟨3825474521851589241875189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10201265391604237978333837 3825474521851589241875189)
                      ·
                        rfl

theorem cell23_7450085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_7450085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450085 prefixEnd_7450085 := by exact prefixLift 7450085
  have htrace : WordTrace (prefixWord ++ tailWord_7450085) baseStart_7450085 baseEnd_7450085 := by
    simpa [prefixWord, tailWord_7450085, baseEnd_7450085] using wordTrace_append hprefix tailTrace_7450085
  have hstable : (prefixWord ++ tailWord_7450085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450085).length < 2 ^ (prefixWord ++ tailWord_7450085).sum := by decide
  have hdescent : baseEnd_7450085 < baseStart_7450085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450116 : List Nat := [2, 3, 2, 3, 2, 1, 3, 2, 1, 2, 2]
def baseStart_7450116 : Nat := 118140960795 + 7450116 * 2 ^ 59
def prefixEnd_7450116 : Nat := 4983230072969 + 3 ^ 40 * 7450116 * 2
def baseEnd_7450116 : Nat := 3825490439751878620587547

theorem tailTrace_7450116 : CollatzResearch.WordTrace tailWord_7450116 prefixEnd_7450116 3825490439751878620587547 := by
  unfold tailWord_7450116
  simp only [CollatzResearch.WordTrace]
  refine ⟨135864026938754792679341101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181152035918339723572454801 135864026938754792679341101)
  ·
    refine ⟨50949010102033047254752913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135864026938754792679341101 50949010102033047254752913)
    ·
      refine ⟨38211757576524785441064685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50949010102033047254752913 38211757576524785441064685)
      ·
        refine ⟨14329409091196794540399257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38211757576524785441064685 14329409091196794540399257)
        ·
          refine ⟨10747056818397595905299443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14329409091196794540399257 10747056818397595905299443)
          ·
            refine ⟨16120585227596393857949165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10747056818397595905299443 16120585227596393857949165)
            ·
              refine ⟨6045219460348647696730937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16120585227596393857949165 6045219460348647696730937)
              ·
                refine ⟨4533914595261485772548203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6045219460348647696730937 4533914595261485772548203)
                ·
                  refine ⟨6800871892892228658822305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4533914595261485772548203 6800871892892228658822305)
                  ·
                    refine ⟨5100653919669171494116729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6800871892892228658822305 5100653919669171494116729)
                    ·
                      refine ⟨3825490439751878620587547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100653919669171494116729 3825490439751878620587547)
                      ·
                        rfl

theorem cell23_7450116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_7450116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450116 prefixEnd_7450116 := by exact prefixLift 7450116
  have htrace : WordTrace (prefixWord ++ tailWord_7450116) baseStart_7450116 baseEnd_7450116 := by
    simpa [prefixWord, tailWord_7450116, baseEnd_7450116] using wordTrace_append hprefix tailTrace_7450116
  have hstable : (prefixWord ++ tailWord_7450116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450116).length < 2 ^ (prefixWord ++ tailWord_7450116).sum := by decide
  have hdescent : baseEnd_7450116 < baseStart_7450116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450138 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2]
def baseStart_7450138 : Nat := 118140960795 + 7450138 * 2 ^ 59
def prefixEnd_7450138 : Nat := 4983230072969 + 3 ^ 40 * 7450138 * 2
def baseEnd_7450138 : Nat := 3825501736326277534512445

theorem tailTrace_7450138 : CollatzResearch.WordTrace tailWord_7450138 prefixEnd_7450138 3825501736326277534512445 := by
  unfold tailWord_7450138
  simp only [CollatzResearch.WordTrace]
  refine ⟨67932214070857470778995767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181152570855619922077322045 67932214070857470778995767)
  ·
    refine ⟨101898321106286206168493651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67932214070857470778995767 101898321106286206168493651)
    ·
      refine ⟨152847481659429309252740477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101898321106286206168493651 152847481659429309252740477)
      ·
        refine ⟨57317805622285990969777679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152847481659429309252740477 57317805622285990969777679)
        ·
          refine ⟨85976708433428986454666519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57317805622285990969777679 85976708433428986454666519)
          ·
            refine ⟨128965062650143479681999779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85976708433428986454666519 128965062650143479681999779)
            ·
              refine ⟨193447593975215219522999669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128965062650143479681999779 193447593975215219522999669)
              ·
                refine ⟨18135711935176426830281219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193447593975215219522999669 18135711935176426830281219)
                ·
                  refine ⟨27203567902764640245421829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18135711935176426830281219 27203567902764640245421829)
                  ·
                    refine ⟨5100668981768370046016593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27203567902764640245421829 5100668981768370046016593)
                    ·
                      refine ⟨3825501736326277534512445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100668981768370046016593 3825501736326277534512445)
                      ·
                        rfl

theorem cell23_7450138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_7450138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450138 prefixEnd_7450138 := by exact prefixLift 7450138
  have htrace : WordTrace (prefixWord ++ tailWord_7450138) baseStart_7450138 baseEnd_7450138 := by
    simpa [prefixWord, tailWord_7450138, baseEnd_7450138] using wordTrace_append hprefix tailTrace_7450138
  have hstable : (prefixWord ++ tailWord_7450138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450138).length < 2 ^ (prefixWord ++ tailWord_7450138).sum := by decide
  have hdescent : baseEnd_7450138 < baseStart_7450138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450141 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_7450141 : Nat := 118140960795 + 7450141 * 2 ^ 59
def prefixEnd_7450141 : Nat := 4983230072969 + 3 ^ 40 * 7450141 * 2
def baseEnd_7450141 : Nat := 3825503276768241022774931

theorem tailTrace_7450141 : CollatzResearch.WordTrace tailWord_7450141 prefixEnd_7450141 3825503276768241022774931 := by
  unfold tailWord_7450141
  simp only [CollatzResearch.WordTrace]
  refine ⟨271728965702419014628342277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181152643801612676418894851 271728965702419014628342277)
  ·
    refine ⟨50949181069203565242814177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271728965702419014628342277 50949181069203565242814177)
    ·
      refine ⟨38211885801902673932110633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50949181069203565242814177 38211885801902673932110633)
      ·
        refine ⟨28658914351427005449082975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38211885801902673932110633 28658914351427005449082975)
        ·
          refine ⟨42988371527140508173624463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28658914351427005449082975 42988371527140508173624463)
          ·
            refine ⟨64482557290710762260436695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42988371527140508173624463 64482557290710762260436695)
            ·
              refine ⟨96723835936066143390655043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64482557290710762260436695 96723835936066143390655043)
              ·
                refine ⟨145085753904099215085982565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96723835936066143390655043 145085753904099215085982565)
                ·
                  refine ⟨27203578857018602828621731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145085753904099215085982565 27203578857018602828621731)
                  ·
                    refine ⟨40805368285527904242932597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27203578857018602828621731 40805368285527904242932597)
                    ·
                      refine ⟨3825503276768241022774931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40805368285527904242932597 3825503276768241022774931)
                      ·
                        rfl

theorem cell23_7450141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_7450141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450141 prefixEnd_7450141 := by exact prefixLift 7450141
  have htrace : WordTrace (prefixWord ++ tailWord_7450141) baseStart_7450141 baseEnd_7450141 := by
    simpa [prefixWord, tailWord_7450141, baseEnd_7450141] using wordTrace_append hprefix tailTrace_7450141
  have hstable : (prefixWord ++ tailWord_7450141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450141).length < 2 ^ (prefixWord ++ tailWord_7450141).sum := by decide
  have hdescent : baseEnd_7450141 < baseStart_7450141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450158 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_7450158 : Nat := 118140960795 + 7450158 * 2 ^ 59
def prefixEnd_7450158 : Nat := 4983230072969 + 3 ^ 40 * 7450158 * 2
def baseEnd_7450158 : Nat := 3825512005939367456262353

theorem tailTrace_7450158 : CollatzResearch.WordTrace tailWord_7450158 prefixEnd_7450158 3825512005939367456262353 := by
  unfold tailWord_7450158
  simp only [CollatzResearch.WordTrace]
  refine ⟨33966198217919678316463891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181153057162238284354474085 33966198217919678316463891)
  ·
    refine ⟨50949297326879517474695837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33966198217919678316463891 50949297326879517474695837)
    ·
      refine ⟨19105986497579819053010939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50949297326879517474695837 19105986497579819053010939)
      ·
        refine ⟨28658979746369728579516409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19105986497579819053010939 28658979746369728579516409)
        ·
          refine ⟨21494234809777296434637307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28658979746369728579516409 21494234809777296434637307)
          ·
            refine ⟨32241352214665944651955961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21494234809777296434637307 32241352214665944651955961)
            ·
              refine ⟨24181014160999458488966971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32241352214665944651955961 24181014160999458488966971)
              ·
                refine ⟨36271521241499187733450457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24181014160999458488966971 36271521241499187733450457)
                ·
                  refine ⟨27203640931124390800087843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36271521241499187733450457 27203640931124390800087843)
                  ·
                    refine ⟨40805461396686586200131765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27203640931124390800087843 40805461396686586200131765)
                    ·
                      refine ⟨3825512005939367456262353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40805461396686586200131765 3825512005939367456262353)
                      ·
                        rfl

theorem cell23_7450158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_7450158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450158 prefixEnd_7450158 := by exact prefixLift 7450158
  have htrace : WordTrace (prefixWord ++ tailWord_7450158) baseStart_7450158 baseEnd_7450158 := by
    simpa [prefixWord, tailWord_7450158, baseEnd_7450158] using wordTrace_append hprefix tailTrace_7450158
  have hstable : (prefixWord ++ tailWord_7450158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450158).length < 2 ^ (prefixWord ++ tailWord_7450158).sum := by decide
  have hdescent : baseEnd_7450158 < baseStart_7450158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450188 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 2, 3, 3]
def baseStart_7450188 : Nat := 118140960795 + 7450188 * 2 ^ 59
def prefixEnd_7450188 : Nat := 4983230072969 + 3 ^ 40 * 7450188 * 2
def baseEnd_7450188 : Nat := 3825527410359002338887215

theorem tailTrace_7450188 : CollatzResearch.WordTrace tailWord_7450188 prefixEnd_7450188 3825527410359002338887215 := by
  unfold tailWord_7450188
  simp only [CollatzResearch.WordTrace]
  refine ⟨135865339966624370827651609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181153786622165827770202145 135865339966624370827651609)
  ·
    refine ⟨101899004974968278120738707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135865339966624370827651609 101899004974968278120738707)
    ·
      refine ⟨152848507462452417181108061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101899004974968278120738707 152848507462452417181108061)
      ·
        refine ⟨57318190298419656442915523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152848507462452417181108061 57318190298419656442915523)
        ·
          refine ⟨85977285447629484664373285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57318190298419656442915523 85977285447629484664373285)
          ·
            refine ⟨16120741021430528374569991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85977285447629484664373285 16120741021430528374569991)
            ·
              refine ⟨24181111532145792561854987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16120741021430528374569991 24181111532145792561854987)
              ·
                refine ⟨36271667298218688842782481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24181111532145792561854987 36271667298218688842782481)
                ·
                  refine ⟨27203750473664016632086861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36271667298218688842782481 27203750473664016632086861)
                  ·
                    refine ⟨10201406427624006237032573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27203750473664016632086861 10201406427624006237032573)
                    ·
                      refine ⟨3825527410359002338887215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10201406427624006237032573 3825527410359002338887215)
                      ·
                        rfl

theorem cell23_7450188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_7450188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450188 prefixEnd_7450188 := by exact prefixLift 7450188
  have htrace : WordTrace (prefixWord ++ tailWord_7450188) baseStart_7450188 baseEnd_7450188 := by
    simpa [prefixWord, tailWord_7450188, baseEnd_7450188] using wordTrace_append hprefix tailTrace_7450188
  have hstable : (prefixWord ++ tailWord_7450188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450188).length < 2 ^ (prefixWord ++ tailWord_7450188).sum := by decide
  have hdescent : baseEnd_7450188 < baseStart_7450188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450272 : List Nat := [2, 1, 1, 4, 3, 1, 3, 3, 1, 4]
def baseStart_7450272 : Nat := 118140960795 + 7450272 * 2 ^ 59
def prefixEnd_7450272 : Nat := 4983230072969 + 3 ^ 40 * 7450272 * 2
def baseEnd_7450272 : Nat := 1275190180911326670078943

theorem tailTrace_7450272 : CollatzResearch.WordTrace tailWord_7450272 prefixEnd_7450272 1275190180911326670078943 := by
  unfold tailWord_7450272
  simp only [CollatzResearch.WordTrace]
  refine ⟨135866871832472212000680535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181155829109962949334240713 135866871832472212000680535)
  ·
    refine ⟨203800307748708318001020803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135866871832472212000680535 203800307748708318001020803)
    ·
      refine ⟨305700461623062477001531205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203800307748708318001020803 305700461623062477001531205)
      ·
        refine ⟨57318836554324214437787101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 305700461623062477001531205 57318836554324214437787101)
        ·
          refine ⟨21494563707871580414170163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57318836554324214437787101 21494563707871580414170163)
          ·
            refine ⟨32241845561807370621255245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21494563707871580414170163 32241845561807370621255245)
            ·
              refine ⟨12090692085677763982970717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32241845561807370621255245 12090692085677763982970717)
              ·
                refine ⟨4534009532129161493614019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12090692085677763982970717 4534009532129161493614019)
                ·
                  refine ⟨6801014298193742240421029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4534009532129161493614019 6801014298193742240421029)
                  ·
                    refine ⟨1275190180911326670078943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6801014298193742240421029 1275190180911326670078943)
                    ·
                      rfl

theorem cell23_7450272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 1, 4].length) (baseStart_7450272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450272 prefixEnd_7450272 := by exact prefixLift 7450272
  have htrace : WordTrace (prefixWord ++ tailWord_7450272) baseStart_7450272 baseEnd_7450272 := by
    simpa [prefixWord, tailWord_7450272, baseEnd_7450272] using wordTrace_append hprefix tailTrace_7450272
  have hstable : (prefixWord ++ tailWord_7450272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450272).length < 2 ^ (prefixWord ++ tailWord_7450272).sum := by decide
  have hdescent : baseEnd_7450272 < baseStart_7450272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450302 : List Nat := [4, 2, 1, 1, 2, 4, 2, 1, 6]
def baseStart_7450302 : Nat := 118140960795 + 7450302 * 2 ^ 59
def prefixEnd_7450302 : Nat := 4983230072969 + 3 ^ 40 * 7450302 * 2
def baseEnd_7450302 : Nat := 425065105239290543651299

theorem tailTrace_7450302 : CollatzResearch.WordTrace tailWord_7450302 prefixEnd_7450302 425065105239290543651299 := by
  unfold tailWord_7450302
  simp only [CollatzResearch.WordTrace]
  refine ⟨33966854731854467390619145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181156558569890492749968773 33966854731854467390619145)
  ·
    refine ⟨25475141048890850542964359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33966854731854467390619145 25475141048890850542964359)
    ·
      refine ⟨38212711573336275814446539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25475141048890850542964359 38212711573336275814446539)
      ·
        refine ⟨57319067360004413721669809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38212711573336275814446539 57319067360004413721669809)
        ·
          refine ⟨42989300520003310291252357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57319067360004413721669809 42989300520003310291252357)
          ·
            refine ⟨8060493847500620679609817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42989300520003310291252357 8060493847500620679609817)
            ·
              refine ⟨6045370385625465509707363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8060493847500620679609817 6045370385625465509707363)
              ·
                refine ⟨9068055578438198264561045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6045370385625465509707363 9068055578438198264561045)
                ·
                  refine ⟨425065105239290543651299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9068055578438198264561045 425065105239290543651299)
                  ·
                    rfl

theorem cell23_7450302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_7450302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450302 prefixEnd_7450302 := by exact prefixLift 7450302
  have htrace : WordTrace (prefixWord ++ tailWord_7450302) baseStart_7450302 baseEnd_7450302 := by
    simpa [prefixWord, tailWord_7450302, baseEnd_7450302] using wordTrace_append hprefix tailTrace_7450302
  have hstable : (prefixWord ++ tailWord_7450302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450302).length < 2 ^ (prefixWord ++ tailWord_7450302).sum := by decide
  have hdescent : baseEnd_7450302 < baseStart_7450302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450322 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 2, 3, 2]
def baseStart_7450322 : Nat := 118140960795 + 7450322 * 2 ^ 59
def prefixEnd_7450322 : Nat := 4983230072969 + 3 ^ 40 * 7450322 * 2
def baseEnd_7450322 : Nat := 3825596216766704814611599

theorem tailTrace_7450322 : CollatzResearch.WordTrace tailWord_7450322 prefixEnd_7450322 3825596216766704814611599 := by
  unfold tailWord_7450322
  simp only [CollatzResearch.WordTrace]
  refine ⟨67933891828690820635170305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181157044876508855027120813 67933891828690820635170305)
  ·
    refine ⟨50950418871518115476377729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67933891828690820635170305 50950418871518115476377729)
    ·
      refine ⟨38212814153638586607283297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50950418871518115476377729 38212814153638586607283297)
      ·
        refine ⟨28659610615228939955462473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38212814153638586607283297 28659610615228939955462473)
        ·
          refine ⟨21494707961421704966596855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28659610615228939955462473 21494707961421704966596855)
          ·
            refine ⟨32242061942132557449895283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21494707961421704966596855 32242061942132557449895283)
            ·
              refine ⟨48363092913198836174842925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32242061942132557449895283 48363092913198836174842925)
              ·
                refine ⟨18136159842449563565566097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48363092913198836174842925 18136159842449563565566097)
                ·
                  refine ⟨13602119881837172674174573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18136159842449563565566097 13602119881837172674174573)
                  ·
                    refine ⟨5100794955688939752815465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13602119881837172674174573 5100794955688939752815465)
                    ·
                      refine ⟨3825596216766704814611599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100794955688939752815465 3825596216766704814611599)
                      ·
                        rfl

theorem cell23_7450322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_7450322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450322 prefixEnd_7450322 := by exact prefixLift 7450322
  have htrace : WordTrace (prefixWord ++ tailWord_7450322) baseStart_7450322 baseEnd_7450322 := by
    simpa [prefixWord, tailWord_7450322, baseEnd_7450322] using wordTrace_append hprefix tailTrace_7450322
  have hstable : (prefixWord ++ tailWord_7450322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450322).length < 2 ^ (prefixWord ++ tailWord_7450322).sum := by decide
  have hdescent : baseEnd_7450322 < baseStart_7450322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450328 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 1, 6]
def baseStart_7450328 : Nat := 118140960795 + 7450328 * 2 ^ 59
def prefixEnd_7450328 : Nat := 4983230072969 + 3 ^ 40 * 7450328 * 2
def baseEnd_7450328 : Nat := 1275199765883543930378857

theorem tailTrace_7450328 : CollatzResearch.WordTrace tailWord_7450328 prefixEnd_7450328 1275199765883543930378857 := by
  unfold tailWord_7450328
  simp only [CollatzResearch.WordTrace]
  refine ⟨135867893076370772782699819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181157190768494363710266425 135867893076370772782699819)
  ·
    refine ⟨203801839614556159174049729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135867893076370772782699819 203801839614556159174049729)
    ·
      refine ⟨152851379710917119380537297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203801839614556159174049729 152851379710917119380537297)
      ·
        refine ⟨114638534783187839535402973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152851379710917119380537297 114638534783187839535402973)
        ·
          refine ⟨42989450543695439825776115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114638534783187839535402973 42989450543695439825776115)
          ·
            refine ⟨64484175815543159738664173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42989450543695439825776115 64484175815543159738664173)
            ·
              refine ⟨24181565930828684901999065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64484175815543159738664173 24181565930828684901999065)
              ·
                refine ⟨18136174448121513676499299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24181565930828684901999065 18136174448121513676499299)
                ·
                  refine ⟨27204261672182270514748949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18136174448121513676499299 27204261672182270514748949)
                  ·
                    refine ⟨1275199765883543930378857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27204261672182270514748949 1275199765883543930378857)
                    ·
                      rfl

theorem cell23_7450328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_7450328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450328 prefixEnd_7450328 := by exact prefixLift 7450328
  have htrace : WordTrace (prefixWord ++ tailWord_7450328) baseStart_7450328 baseEnd_7450328 := by
    simpa [prefixWord, tailWord_7450328, baseEnd_7450328] using wordTrace_append hprefix tailTrace_7450328
  have hstable : (prefixWord ++ tailWord_7450328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450328).length < 2 ^ (prefixWord ++ tailWord_7450328).sum := by decide
  have hdescent : baseEnd_7450328 < baseStart_7450328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450368 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 3]
def baseStart_7450368 : Nat := 118140960795 + 7450368 * 2 ^ 59
def prefixEnd_7450368 : Nat := 4983230072969 + 3 ^ 40 * 7450368 * 2
def baseEnd_7450368 : Nat := 3825619836876811634636387

theorem tailTrace_7450368 : CollatzResearch.WordTrace tailWord_7450368 prefixEnd_7450368 3825619836876811634636387 := by
  unfold tailWord_7450368
  simp only [CollatzResearch.WordTrace]
  refine ⟨135868622536298316198427879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181158163381731088264570505 135868622536298316198427879)
  ·
    refine ⟨203802933804447474297641819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135868622536298316198427879 203802933804447474297641819)
    ·
      refine ⟨305704400706671211446462729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203802933804447474297641819 305704400706671211446462729)
      ·
        refine ⟨229278300530003408584847047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305704400706671211446462729 229278300530003408584847047)
        ·
          refine ⟨343917450795005112877270571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229278300530003408584847047 343917450795005112877270571)
          ·
            refine ⟨515876176192507669315905857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343917450795005112877270571 515876176192507669315905857)
            ·
              refine ⟨386907132144380751986929393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515876176192507669315905857 386907132144380751986929393)
              ·
                refine ⟨290180349108285563990197045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386907132144380751986929393 290180349108285563990197045)
                ·
                  refine ⟨27204407728901771624080973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 290180349108285563990197045 27204407728901771624080973)
                  ·
                    refine ⟨10201652898338164359030365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27204407728901771624080973 10201652898338164359030365)
                    ·
                      refine ⟨3825619836876811634636387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10201652898338164359030365 3825619836876811634636387)
                      ·
                        rfl

theorem cell23_7450368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_7450368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450368 prefixEnd_7450368 := by exact prefixLift 7450368
  have htrace : WordTrace (prefixWord ++ tailWord_7450368) baseStart_7450368 baseEnd_7450368 := by
    simpa [prefixWord, tailWord_7450368, baseEnd_7450368] using wordTrace_append hprefix tailTrace_7450368
  have hstable : (prefixWord ++ tailWord_7450368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450368).length < 2 ^ (prefixWord ++ tailWord_7450368).sum := by decide
  have hdescent : baseEnd_7450368 < baseStart_7450368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450385 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 4, 1, 3]
def baseStart_7450385 : Nat := 118140960795 + 7450385 * 2 ^ 59
def prefixEnd_7450385 : Nat := 4983230072969 + 3 ^ 40 * 7450385 * 2
def baseEnd_7450385 : Nat := 3825628566047938068123809

theorem tailTrace_7450385 : CollatzResearch.WordTrace tailWord_7450385 prefixEnd_7450385 3825628566047938068123809 := by
  unfold tailWord_7450385
  simp only [CollatzResearch.WordTrace]
  refine ⟨271737865113535044300224609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181158576742356696200149739 271737865113535044300224609)
  ·
    refine ⟨203803398835151283225168457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271737865113535044300224609 203803398835151283225168457)
    ·
      refine ⟨152852549126363462418876343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203803398835151283225168457 152852549126363462418876343)
      ·
        refine ⟨229278823689545193628314515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152852549126363462418876343 229278823689545193628314515)
        ·
          refine ⟨343918235534317790442471773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229278823689545193628314515 343918235534317790442471773)
          ·
            refine ⟨128969338325369171415926915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343918235534317790442471773 128969338325369171415926915)
            ·
              refine ⟨193454007488053757123890373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128969338325369171415926915 193454007488053757123890373)
              ·
                refine ⟨36272626404010079460729445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193454007488053757123890373 36272626404010079460729445)
                ·
                  refine ⟨6801117450751889898886771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36272626404010079460729445 6801117450751889898886771)
                  ·
                    refine ⟨10201676176127834848330157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6801117450751889898886771 10201676176127834848330157)
                    ·
                      refine ⟨3825628566047938068123809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10201676176127834848330157 3825628566047938068123809)
                      ·
                        rfl

theorem cell23_7450385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 1, 3].length) (baseStart_7450385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450385 prefixEnd_7450385 := by exact prefixLift 7450385
  have htrace : WordTrace (prefixWord ++ tailWord_7450385) baseStart_7450385 baseEnd_7450385 := by
    simpa [prefixWord, tailWord_7450385, baseEnd_7450385] using wordTrace_append hprefix tailTrace_7450385
  have hstable : (prefixWord ++ tailWord_7450385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450385).length < 2 ^ (prefixWord ++ tailWord_7450385).sum := by decide
  have hdescent : baseEnd_7450385 < baseStart_7450385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450386 : List Nat := [3, 2, 4, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_7450386 : Nat := 118140960795 + 7450386 * 2 ^ 59
def prefixEnd_7450386 : Nat := 4983230072969 + 3 ^ 40 * 7450386 * 2
def baseEnd_7450386 : Nat := 3825629079528592564211305

theorem tailTrace_7450386 : CollatzResearch.WordTrace tailWord_7450386 prefixEnd_7450386 3825629079528592564211305 := by
  unfold tailWord_7450386
  simp only [CollatzResearch.WordTrace]
  refine ⟨67934475396632855367752753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181158601057687614314007341 67934475396632855367752753)
  ·
    refine ⟨50950856547474641525814565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67934475396632855367752753 50950856547474641525814565)
    ·
      refine ⟨9553285602651495286090231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50950856547474641525814565 9553285602651495286090231)
      ·
        refine ⟨14329928403977242929135347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9553285602651495286090231 14329928403977242929135347)
        ·
          refine ⟨21494892605965864393703021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14329928403977242929135347 21494892605965864393703021)
          ·
            refine ⟨8060584727237199147638633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21494892605965864393703021 8060584727237199147638633)
            ·
              refine ⟨6045438545427899360728975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8060584727237199147638633 6045438545427899360728975)
              ·
                refine ⟨9068157818141849041093463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6045438545427899360728975 9068157818141849041093463)
                ·
                  refine ⟨13602236727212773561640195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9068157818141849041093463 13602236727212773561640195)
                  ·
                    refine ⟨20403355090819160342460293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13602236727212773561640195 20403355090819160342460293)
                    ·
                      refine ⟨3825629079528592564211305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20403355090819160342460293 3825629079528592564211305)
                      ·
                        rfl

theorem cell23_7450386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_7450386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450386 prefixEnd_7450386 := by exact prefixLift 7450386
  have htrace : WordTrace (prefixWord ++ tailWord_7450386) baseStart_7450386 baseEnd_7450386 := by
    simpa [prefixWord, tailWord_7450386, baseEnd_7450386] using wordTrace_append hprefix tailTrace_7450386
  have hstable : (prefixWord ++ tailWord_7450386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450386).length < 2 ^ (prefixWord ++ tailWord_7450386).sum := by decide
  have hdescent : baseEnd_7450386 < baseStart_7450386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450389 : List Nat := [1, 3, 2, 1, 2, 5, 2, 1, 1, 2, 3]
def baseStart_7450389 : Nat := 118140960795 + 7450389 * 2 ^ 59
def prefixEnd_7450389 : Nat := 4983230072969 + 3 ^ 40 * 7450389 * 2
def baseEnd_7450389 : Nat := 3825630619970556052473791

theorem tailTrace_7450389 : CollatzResearch.WordTrace tailWord_7450389 prefixEnd_7450389 3825630619970556052473791 := by
  unfold tailWord_7450389
  simp only [CollatzResearch.WordTrace]
  refine ⟨271738011005520552983370221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181158674003680368655580147 271738011005520552983370221)
  ·
    refine ⟨101901754127070207368763833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271738011005520552983370221 101901754127070207368763833)
    ·
      refine ⟨76426315595302655526572875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101901754127070207368763833 76426315595302655526572875)
      ·
        refine ⟨114639473392953983289859313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76426315595302655526572875 114639473392953983289859313)
        ·
          refine ⟨85979605044715487467394485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114639473392953983289859313 85979605044715487467394485)
          ·
            refine ⟨8060587972942076950068233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85979605044715487467394485 8060587972942076950068233)
            ·
              refine ⟨6045440979706557712551175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8060587972942076950068233 6045440979706557712551175)
              ·
                refine ⟨9068161469559836568826763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6045440979706557712551175 9068161469559836568826763)
                ·
                  refine ⟨13602242204339754853240145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9068161469559836568826763 13602242204339754853240145)
                  ·
                    refine ⟨10201681653254816139930109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13602242204339754853240145 10201681653254816139930109)
                    ·
                      refine ⟨3825630619970556052473791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10201681653254816139930109 3825630619970556052473791)
                      ·
                        rfl

theorem cell23_7450389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_7450389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450389 prefixEnd_7450389 := by exact prefixLift 7450389
  have htrace : WordTrace (prefixWord ++ tailWord_7450389) baseStart_7450389 baseEnd_7450389 := by
    simpa [prefixWord, tailWord_7450389, baseEnd_7450389] using wordTrace_append hprefix tailTrace_7450389
  have hstable : (prefixWord ++ tailWord_7450389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450389).length < 2 ^ (prefixWord ++ tailWord_7450389).sum := by decide
  have hdescent : baseEnd_7450389 < baseStart_7450389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450402 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_7450402 : Nat := 118140960795 + 7450402 * 2 ^ 59
def prefixEnd_7450402 : Nat := 4983230072969 + 3 ^ 40 * 7450402 * 2
def baseEnd_7450402 : Nat := 3825637295219064501611231

theorem tailTrace_7450402 : CollatzResearch.WordTrace tailWord_7450402 prefixEnd_7450402 3825637295219064501611231 := by
  unfold tailWord_7450402
  simp only [CollatzResearch.WordTrace]
  refine ⟨67934621288618364050898365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181158990102982304135728973 67934621288618364050898365)
  ·
    refine ⟨25475482983231886519086887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67934621288618364050898365 25475482983231886519086887)
    ·
      refine ⟨38213224474847829778630331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25475482983231886519086887 38213224474847829778630331)
      ·
        refine ⟨57319836712271744667945497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38213224474847829778630331 57319836712271744667945497)
        ·
          refine ⟨42989877534203808500959123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57319836712271744667945497 42989877534203808500959123)
          ·
            refine ⟨64484816301305712751438685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42989877534203808500959123 64484816301305712751438685)
            ·
              refine ⟨24181806112989642281789507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64484816301305712751438685 24181806112989642281789507)
              ·
                refine ⟨36272709169484463422684261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24181806112989642281789507 36272709169484463422684261)
                ·
                  refine ⟨6801132969278336891753299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36272709169484463422684261 6801132969278336891753299)
                  ·
                    refine ⟨10201699453917505337629949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6801132969278336891753299 10201699453917505337629949)
                    ·
                      refine ⟨3825637295219064501611231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10201699453917505337629949 3825637295219064501611231)
                      ·
                        rfl

theorem cell23_7450402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_7450402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450402 prefixEnd_7450402 := by exact prefixLift 7450402
  have htrace : WordTrace (prefixWord ++ tailWord_7450402) baseStart_7450402 baseEnd_7450402 := by
    simpa [prefixWord, tailWord_7450402, baseEnd_7450402] using wordTrace_append hprefix tailTrace_7450402
  have hstable : (prefixWord ++ tailWord_7450402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450402).length < 2 ^ (prefixWord ++ tailWord_7450402).sum := by decide
  have hdescent : baseEnd_7450402 < baseStart_7450402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450419 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 1, 3, 3]
def baseStart_7450419 : Nat := 118140960795 + 7450419 * 2 ^ 59
def prefixEnd_7450419 : Nat := 4983230072969 + 3 ^ 40 * 7450419 * 2
def baseEnd_7450419 : Nat := 3825646024390190935098653

theorem tailTrace_7450419 : CollatzResearch.WordTrace tailWord_7450419 prefixEnd_7450419 3825646024390190935098653 := by
  unfold tailWord_7450419
  simp only [CollatzResearch.WordTrace]
  refine ⟨271739105195411868106962311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181159403463607912071308207 271739105195411868106962311)
  ·
    refine ⟨407608657793117802160443467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271739105195411868106962311 407608657793117802160443467)
    ·
      refine ⟨611412986689676703240665201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407608657793117802160443467 611412986689676703240665201)
      ·
        refine ⟨458559740017257527430498901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 611412986689676703240665201 458559740017257527430498901)
        ·
          refine ⟨5373746953327236649576159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 458559740017257527430498901 5373746953327236649576159)
          ·
            refine ⟨8060620429990854974364239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5373746953327236649576159 8060620429990854974364239)
            ·
              refine ⟨12090930644986282461546359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8060620429990854974364239 12090930644986282461546359)
              ·
                refine ⟨18136395967479423692319539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12090930644986282461546359 18136395967479423692319539)
                ·
                  refine ⟨27204593951219135538479309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18136395967479423692319539 27204593951219135538479309)
                  ·
                    refine ⟨10201722731707175826929741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27204593951219135538479309 10201722731707175826929741)
                    ·
                      refine ⟨3825646024390190935098653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10201722731707175826929741 3825646024390190935098653)
                      ·
                        rfl

theorem cell23_7450419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 1, 3, 3].length) (baseStart_7450419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450419 prefixEnd_7450419 := by exact prefixLift 7450419
  have htrace : WordTrace (prefixWord ++ tailWord_7450419) baseStart_7450419 baseEnd_7450419 := by
    simpa [prefixWord, tailWord_7450419, baseEnd_7450419] using wordTrace_append hprefix tailTrace_7450419
  have hstable : (prefixWord ++ tailWord_7450419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450419).length < 2 ^ (prefixWord ++ tailWord_7450419).sum := by decide
  have hdescent : baseEnd_7450419 < baseStart_7450419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450429 : List Nat := [1, 4, 1, 4, 1, 1, 1, 4, 1, 3, 2]
def baseStart_7450429 : Nat := 118140960795 + 7450429 * 2 ^ 59
def prefixEnd_7450429 : Nat := 4983230072969 + 3 ^ 40 * 7450429 * 2
def baseEnd_7450429 : Nat := 3825651159196735895973607

theorem tailTrace_7450429 : CollatzResearch.WordTrace tailWord_7450429 prefixEnd_7450429 3825651159196735895973607 := by
  unfold tailWord_7450429
  simp only [CollatzResearch.WordTrace]
  refine ⟨271739469925375639814826341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181159646616917093209884227 271739469925375639814826341)
  ·
    refine ⟨50951150611007932465279939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 271739469925375639814826341 50951150611007932465279939)
    ·
      refine ⟨76426725916511898697919909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50951150611007932465279939 76426725916511898697919909)
      ·
        refine ⟨14330011109345981005859983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76426725916511898697919909 14330011109345981005859983)
        ·
          refine ⟨21495016664018971508789975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14330011109345981005859983 21495016664018971508789975)
          ·
            refine ⟨32242524996028457263184963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21495016664018971508789975 32242524996028457263184963)
            ·
              refine ⟨48363787494042685894777445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32242524996028457263184963 48363787494042685894777445)
              ·
                refine ⟨9068210155133003605270771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48363787494042685894777445 9068210155133003605270771)
                ·
                  refine ⟨13602315232699505407906157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9068210155133003605270771 13602315232699505407906157)
                  ·
                    refine ⟨5100868212262314527964809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13602315232699505407906157 5100868212262314527964809)
                    ·
                      refine ⟨3825651159196735895973607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100868212262314527964809 3825651159196735895973607)
                      ·
                        rfl

theorem cell23_7450429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_7450429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450429 prefixEnd_7450429 := by exact prefixLift 7450429
  have htrace : WordTrace (prefixWord ++ tailWord_7450429) baseStart_7450429 baseEnd_7450429 := by
    simpa [prefixWord, tailWord_7450429, baseEnd_7450429] using wordTrace_append hprefix tailTrace_7450429
  have hstable : (prefixWord ++ tailWord_7450429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450429).length < 2 ^ (prefixWord ++ tailWord_7450429).sum := by decide
  have hdescent : baseEnd_7450429 < baseStart_7450429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450442 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 6, 2, 2]
def baseStart_7450442 : Nat := 118140960795 + 7450442 * 2 ^ 59
def prefixEnd_7450442 : Nat := 4983230072969 + 3 ^ 40 * 7450442 * 2
def baseEnd_7450442 : Nat := 3825657834445244345111047

theorem tailTrace_7450442 : CollatzResearch.WordTrace tailWord_7450442 prefixEnd_7450442 3825657834445244345111047 := by
  unfold tailWord_7450442
  simp only [CollatzResearch.WordTrace]
  refine ⟨67934986018582135758762395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181159962716219028690033053 67934986018582135758762395)
  ·
    refine ⟨101902479027873203638143593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67934986018582135758762395 101902479027873203638143593)
    ·
      refine ⟨76426859270904902728607695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101902479027873203638143593 76426859270904902728607695)
      ·
        refine ⟨114640288906357354092911543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76426859270904902728607695 114640288906357354092911543)
        ·
          refine ⟨171960433359536031139367315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114640288906357354092911543 171960433359536031139367315)
          ·
            refine ⟨257940650039304046709050973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171960433359536031139367315 257940650039304046709050973)
            ·
              refine ⟨96727743764739017515894115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257940650039304046709050973 96727743764739017515894115)
              ·
                refine ⟨145091615647108526273841173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96727743764739017515894115 145091615647108526273841173)
                ·
                  refine ⟨6801169483458212169086305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 145091615647108526273841173 6801169483458212169086305)
                  ·
                    refine ⟨5100877112593659126814729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6801169483458212169086305 5100877112593659126814729)
                    ·
                      refine ⟨3825657834445244345111047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100877112593659126814729 3825657834445244345111047)
                      ·
                        rfl

theorem cell23_7450442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_7450442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450442 prefixEnd_7450442 := by exact prefixLift 7450442
  have htrace : WordTrace (prefixWord ++ tailWord_7450442) baseStart_7450442 baseEnd_7450442 := by
    simpa [prefixWord, tailWord_7450442, baseEnd_7450442] using wordTrace_append hprefix tailTrace_7450442
  have hstable : (prefixWord ++ tailWord_7450442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450442).length < 2 ^ (prefixWord ++ tailWord_7450442).sum := by decide
  have hdescent : baseEnd_7450442 < baseStart_7450442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450458 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7]
def baseStart_7450458 : Nat := 118140960795 + 7450458 * 2 ^ 59
def prefixEnd_7450458 : Nat := 4983230072969 + 3 ^ 40 * 7450458 * 2
def baseEnd_7450458 : Nat := 3825666050135716282510973

theorem tailTrace_7450458 : CollatzResearch.WordTrace tailWord_7450458 prefixEnd_7450458 3825666050135716282510973 := by
  unfold tailWord_7450458
  simp only [CollatzResearch.WordTrace]
  refine ⟨67935131910567644441908007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181160351761513718511754685 67935131910567644441908007)
  ·
    refine ⟨101902697865851466662862011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67935131910567644441908007 101902697865851466662862011)
    ·
      refine ⟨152854046798777199994293017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101902697865851466662862011 152854046798777199994293017)
      ·
        refine ⟨114640535099082899995719763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152854046798777199994293017 114640535099082899995719763)
        ·
          refine ⟨171960802648624349993579645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114640535099082899995719763 171960802648624349993579645)
          ·
            refine ⟨64485300993234131247592367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171960802648624349993579645 64485300993234131247592367)
            ·
              refine ⟨96727951489851196871388551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64485300993234131247592367 96727951489851196871388551)
              ·
                refine ⟨145091927234776795307082827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96727951489851196871388551 145091927234776795307082827)
                ·
                  refine ⟨217637890852165192960624241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145091927234776795307082827 217637890852165192960624241)
                  ·
                    refine ⟨163228418139123894720468181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 217637890852165192960624241 163228418139123894720468181)
                    ·
                      refine ⟨3825666050135716282510973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 163228418139123894720468181 3825666050135716282510973)
                      ·
                        rfl

theorem cell23_7450458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_7450458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450458 prefixEnd_7450458 := by exact prefixLift 7450458
  have htrace : WordTrace (prefixWord ++ tailWord_7450458) baseStart_7450458 baseEnd_7450458 := by
    simpa [prefixWord, tailWord_7450458, baseEnd_7450458] using wordTrace_append hprefix tailTrace_7450458
  have hstable : (prefixWord ++ tailWord_7450458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450458).length < 2 ^ (prefixWord ++ tailWord_7450458).sum := by decide
  have hdescent : baseEnd_7450458 < baseStart_7450458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450476 : List Nat := [2, 2, 1, 1, 4, 2, 4, 1, 2, 2, 2]
def baseStart_7450476 : Nat := 118140960795 + 7450476 * 2 ^ 59
def prefixEnd_7450476 : Nat := 4983230072969 + 3 ^ 40 * 7450476 * 2
def baseEnd_7450476 : Nat := 3825675292787497212085891

theorem tailTrace_7450476 : CollatzResearch.WordTrace tailWord_7450476 prefixEnd_7450476 3825675292787497212085891 := by
  unfold tailWord_7450476
  simp only [CollatzResearch.WordTrace]
  refine ⟨135870592078102683420893641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181160789437470244561191521 135870592078102683420893641)
  ·
    refine ⟨101902944058577012565670231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135870592078102683420893641 101902944058577012565670231)
    ·
      refine ⟨152854416087865518848505347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101902944058577012565670231 152854416087865518848505347)
      ·
        refine ⟨229281624131798278272758021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152854416087865518848505347 229281624131798278272758021)
        ·
          refine ⟨42990304524712177176142129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 229281624131798278272758021 42990304524712177176142129)
          ·
            refine ⟨32242728393534132882106597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42990304524712177176142129 32242728393534132882106597)
            ·
              refine ⟨6045511573787649915394987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32242728393534132882106597 6045511573787649915394987)
              ·
                refine ⟨9068267360681474873092481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6045511573787649915394987 9068267360681474873092481)
                ·
                  refine ⟨6801200520511106154819361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9068267360681474873092481 6801200520511106154819361)
                  ·
                    refine ⟨5100900390383329616114521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6801200520511106154819361 5100900390383329616114521)
                    ·
                      refine ⟨3825675292787497212085891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100900390383329616114521 3825675292787497212085891)
                      ·
                        rfl

theorem cell23_7450476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 2, 2].length) (baseStart_7450476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450476 prefixEnd_7450476 := by exact prefixLift 7450476
  have htrace : WordTrace (prefixWord ++ tailWord_7450476) baseStart_7450476 baseEnd_7450476 := by
    simpa [prefixWord, tailWord_7450476, baseEnd_7450476] using wordTrace_append hprefix tailTrace_7450476
  have hstable : (prefixWord ++ tailWord_7450476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450476).length < 2 ^ (prefixWord ++ tailWord_7450476).sum := by decide
  have hdescent : baseEnd_7450476 < baseStart_7450476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450516 : List Nat := [2, 4, 2, 1, 1, 4, 2, 2, 5]
def baseStart_7450516 : Nat := 118140960795 + 7450516 * 2 ^ 59
def prefixEnd_7450516 : Nat := 4983230072969 + 3 ^ 40 * 7450516 * 2
def baseEnd_7450516 : Nat := 425077314668186339509523

theorem tailTrace_7450516 : CollatzResearch.WordTrace tailWord_7450516 prefixEnd_7450516 425077314668186339509523 := by
  unfold tailWord_7450516
  simp only [CollatzResearch.WordTrace]
  refine ⟨135871321538030226836621701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181161762050706969115495601 135871321538030226836621701)
  ·
    refine ⟨25475872788380667531866569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135871321538030226836621701 25475872788380667531866569)
    ·
      refine ⟨19106904591285500648899927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25475872788380667531866569 19106904591285500648899927)
      ·
        refine ⟨28660356886928250973349891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19106904591285500648899927 28660356886928250973349891)
        ·
          refine ⟨42990535330392376460024837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28660356886928250973349891 42990535330392376460024837)
          ·
            refine ⟨8060725374448570586254657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42990535330392376460024837 8060725374448570586254657)
            ·
              refine ⟨6045544030836427939690993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8060725374448570586254657 6045544030836427939690993)
              ·
                refine ⟨4534158023127320954768245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6045544030836427939690993 4534158023127320954768245)
                ·
                  refine ⟨425077314668186339509523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4534158023127320954768245 425077314668186339509523)
                  ·
                    rfl

theorem cell23_7450516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_7450516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450516 prefixEnd_7450516 := by exact prefixLift 7450516
  have htrace : WordTrace (prefixWord ++ tailWord_7450516) baseStart_7450516 baseEnd_7450516 := by
    simpa [prefixWord, tailWord_7450516, baseEnd_7450516] using wordTrace_append hprefix tailTrace_7450516
  have hstable : (prefixWord ++ tailWord_7450516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450516).length < 2 ^ (prefixWord ++ tailWord_7450516).sum := by decide
  have hdescent : baseEnd_7450516 < baseStart_7450516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450526 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_7450526 : Nat := 118140960795 + 7450526 * 2 ^ 59
def prefixEnd_7450526 : Nat := 4983230072969 + 3 ^ 40 * 7450526 * 2
def baseEnd_7450526 : Nat := 3825700966820222016460661

theorem tailTrace_7450526 : CollatzResearch.WordTrace tailWord_7450526 prefixEnd_7450526 3825700966820222016460661 := by
  unfold tailWord_7450526
  simp only [CollatzResearch.WordTrace]
  refine ⟨33967875975753028172638429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181162005204016150254071621 33967875975753028172638429)
  ·
    refine ⟨12737953490907385564739411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33967875975753028172638429 12737953490907385564739411)
    ·
      refine ⟨19106930236361078347109117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12737953490907385564739411 19106930236361078347109117)
      ·
        refine ⟨7165098838635404380165919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19106930236361078347109117 7165098838635404380165919)
        ·
          refine ⟨10747648257953106570248879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7165098838635404380165919 10747648257953106570248879)
          ·
            refine ⟨16121472386929659855373319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10747648257953106570248879 16121472386929659855373319)
            ·
              refine ⟨24182208580394489783059979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16121472386929659855373319 24182208580394489783059979)
              ·
                refine ⟨36273312870591734674589969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24182208580394489783059979 36273312870591734674589969)
                ·
                  refine ⟨27204984652943801005942477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36273312870591734674589969 27204984652943801005942477)
                  ·
                    refine ⟨10201869244853925377228429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27204984652943801005942477 10201869244853925377228429)
                    ·
                      refine ⟨3825700966820222016460661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10201869244853925377228429 3825700966820222016460661)
                      ·
                        rfl

theorem cell23_7450526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_7450526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450526 prefixEnd_7450526 := by exact prefixLift 7450526
  have htrace : WordTrace (prefixWord ++ tailWord_7450526) baseStart_7450526 baseEnd_7450526 := by
    simpa [prefixWord, tailWord_7450526, baseEnd_7450526] using wordTrace_append hprefix tailTrace_7450526
  have hstable : (prefixWord ++ tailWord_7450526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450526).length < 2 ^ (prefixWord ++ tailWord_7450526).sum := by decide
  have hdescent : baseEnd_7450526 < baseStart_7450526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450532 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 1, 6, 2]
def baseStart_7450532 : Nat := 118140960795 + 7450532 * 2 ^ 59
def prefixEnd_7450532 : Nat := 4983230072969 + 3 ^ 40 * 7450532 * 2
def baseEnd_7450532 : Nat := 3825704047704148992985633

theorem tailTrace_7450532 : CollatzResearch.WordTrace tailWord_7450532 prefixEnd_7450532 3825704047704148992985633 := by
  unfold tailWord_7450532
  simp only [CollatzResearch.WordTrace]
  refine ⟨135871613322001244202912925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181162151096001658937217233 135871613322001244202912925)
  ·
    refine ⟨50951854995750466576092347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135871613322001244202912925 50951854995750466576092347)
    ·
      refine ⟨76427782493625699864138521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50951854995750466576092347 76427782493625699864138521)
      ·
        refine ⟨57320836870219274898103891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76427782493625699864138521 57320836870219274898103891)
        ·
          refine ⟨85981255305328912347155837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57320836870219274898103891 85981255305328912347155837)
          ·
            refine ⟨32242970739498342130183439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85981255305328912347155837 32242970739498342130183439)
            ·
              refine ⟨48364456109247513195275159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32242970739498342130183439 48364456109247513195275159)
              ·
                refine ⟨72546684163871269792912739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48364456109247513195275159 72546684163871269792912739)
                ·
                  refine ⟨108820026245806904689369109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72546684163871269792912739 108820026245806904689369109)
                  ·
                    refine ⟨5100938730272198657314177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108820026245806904689369109 5100938730272198657314177)
                    ·
                      refine ⟨3825704047704148992985633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5100938730272198657314177 3825704047704148992985633)
                      ·
                        rfl

theorem cell23_7450532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_7450532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450532 prefixEnd_7450532 := by exact prefixLift 7450532
  have htrace : WordTrace (prefixWord ++ tailWord_7450532) baseStart_7450532 baseEnd_7450532 := by
    simpa [prefixWord, tailWord_7450532, baseEnd_7450532] using wordTrace_append hprefix tailTrace_7450532
  have hstable : (prefixWord ++ tailWord_7450532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450532).length < 2 ^ (prefixWord ++ tailWord_7450532).sum := by decide
  have hdescent : baseEnd_7450532 < baseStart_7450532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450549 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_7450549 : Nat := 118140960795 + 7450549 * 2 ^ 59
def prefixEnd_7450549 : Nat := 4983230072969 + 3 ^ 40 * 7450549 * 2
def baseEnd_7450549 : Nat := 3825712776875275426473055

theorem tailTrace_7450549 : CollatzResearch.WordTrace tailWord_7450549 prefixEnd_7450549 3825712776875275426473055 := by
  unfold tailWord_7450549
  simp only [CollatzResearch.WordTrace]
  refine ⟨271743846684940900309194701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181162564456627266872796467 271743846684940900309194701)
  ·
    refine ⟨101903942506852837615948013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271743846684940900309194701 101903942506852837615948013)
    ·
      refine ⟨38213978440069814105980505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101903942506852837615948013 38213978440069814105980505)
      ·
        refine ⟨28660483830052360579485379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38213978440069814105980505 28660483830052360579485379)
        ·
          refine ⟨42990725745078540869228069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28660483830052360579485379 42990725745078540869228069)
          ·
            refine ⟨8060761077202226412980263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42990725745078540869228069 8060761077202226412980263)
            ·
              refine ⟨12091141615803339619470395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8060761077202226412980263 12091141615803339619470395)
              ·
                refine ⟨18136712423705009429205593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12091141615803339619470395 18136712423705009429205593)
                ·
                  refine ⟨13602534317778757071904195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18136712423705009429205593 13602534317778757071904195)
                  ·
                    refine ⟨20403801476668135607856293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13602534317778757071904195 20403801476668135607856293)
                    ·
                      refine ⟨3825712776875275426473055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20403801476668135607856293 3825712776875275426473055)
                      ·
                        rfl

theorem cell23_7450549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_7450549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450549 prefixEnd_7450549 := by exact prefixLift 7450549
  have htrace : WordTrace (prefixWord ++ tailWord_7450549) baseStart_7450549 baseEnd_7450549 := by
    simpa [prefixWord, tailWord_7450549, baseEnd_7450549] using wordTrace_append hprefix tailTrace_7450549
  have hstable : (prefixWord ++ tailWord_7450549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450549).length < 2 ^ (prefixWord ++ tailWord_7450549).sum := by decide
  have hdescent : baseEnd_7450549 < baseStart_7450549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450559 : List Nat := [1, 1, 2, 2, 2, 1, 6, 3, 1, 4]
def baseStart_7450559 : Nat := 118140960795 + 7450559 * 2 ^ 59
def prefixEnd_7450559 : Nat := 4983230072969 + 3 ^ 40 * 7450559 * 2
def baseEnd_7450559 : Nat := 1275239303893940129116003

theorem tailTrace_7450559 : CollatzResearch.WordTrace tailWord_7450559 prefixEnd_7450559 1275239303893940129116003 := by
  unfold tailWord_7450559
  simp only [CollatzResearch.WordTrace]
  refine ⟨271744211414904672017058731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181162807609936448011372487 271744211414904672017058731)
  ·
    refine ⟨407616317122357008025588097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271744211414904672017058731 407616317122357008025588097)
    ·
      refine ⟨305712237841767756019191073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407616317122357008025588097 305712237841767756019191073)
      ·
        refine ⟨229284178381325817014393305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305712237841767756019191073 229284178381325817014393305)
        ·
          refine ⟨171963133785994362760794979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229284178381325817014393305 171963133785994362760794979)
          ·
            refine ⟨257944700678991544141192469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171963133785994362760794979 257944700678991544141192469)
            ·
              refine ⟨12091157844327728631618397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 257944700678991544141192469 12091157844327728631618397)
              ·
                refine ⟨4534184191622898236856899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12091157844327728631618397 4534184191622898236856899)
                ·
                  refine ⟨6801276287434347355285349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4534184191622898236856899 6801276287434347355285349)
                  ·
                    refine ⟨1275239303893940129116003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6801276287434347355285349 1275239303893940129116003)
                    ·
                      rfl

theorem cell23_7450559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 1, 4].length) (baseStart_7450559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450559 prefixEnd_7450559 := by exact prefixLift 7450559
  have htrace : WordTrace (prefixWord ++ tailWord_7450559) baseStart_7450559 baseEnd_7450559 := by
    simpa [prefixWord, tailWord_7450559, baseEnd_7450559] using wordTrace_append hprefix tailTrace_7450559
  have hstable : (prefixWord ++ tailWord_7450559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450559).length < 2 ^ (prefixWord ++ tailWord_7450559).sum := by decide
  have hdescent : baseEnd_7450559 < baseStart_7450559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450572 : List Nat := [2, 2, 1, 4, 1, 2, 3, 2, 6]
def baseStart_7450572 : Nat := 118140960795 + 7450572 * 2 ^ 59
def prefixEnd_7450572 : Nat := 4983230072969 + 3 ^ 40 * 7450572 * 2
def baseEnd_7450572 : Nat := 425080509658925426276161

theorem tailTrace_7450572 : CollatzResearch.WordTrace tailWord_7450572 prefixEnd_7450572 425080509658925426276161 := by
  unfold tailWord_7450572
  simp only [CollatzResearch.WordTrace]
  refine ⟨135872342781928787618640985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181163123709238383491521313 135872342781928787618640985)
  ·
    refine ⟨101904257086446590713980739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135872342781928787618640985 101904257086446590713980739)
    ·
      refine ⟨152856385629669886070971109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101904257086446590713980739 152856385629669886070971109)
      ·
        refine ⟨28660572305563103638307083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152856385629669886070971109 28660572305563103638307083)
        ·
          refine ⟨42990858458344655457460625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28660572305563103638307083 42990858458344655457460625)
          ·
            refine ⟨32243143843758491593095469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42990858458344655457460625 32243143843758491593095469)
            ·
              refine ⟨12091178941409434347410801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32243143843758491593095469 12091178941409434347410801)
              ·
                refine ⟨9068384206057075760558101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12091178941409434347410801 9068384206057075760558101)
                ·
                  refine ⟨425080509658925426276161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9068384206057075760558101 425080509658925426276161)
                  ·
                    rfl

theorem cell23_7450572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 6].length) (baseStart_7450572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450572 prefixEnd_7450572 := by exact prefixLift 7450572
  have htrace : WordTrace (prefixWord ++ tailWord_7450572) baseStart_7450572 baseEnd_7450572 := by
    simpa [prefixWord, tailWord_7450572, baseEnd_7450572] using wordTrace_append hprefix tailTrace_7450572
  have hstable : (prefixWord ++ tailWord_7450572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450572).length < 2 ^ (prefixWord ++ tailWord_7450572).sum := by decide
  have hdescent : baseEnd_7450572 < baseStart_7450572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450616 : List Nat := [2, 1, 2, 1, 1, 3, 5, 3, 1, 1, 3]
def baseStart_7450616 : Nat := 118140960795 + 7450616 * 2 ^ 59
def prefixEnd_7450616 : Nat := 4983230072969 + 3 ^ 40 * 7450616 * 2
def baseEnd_7450616 : Nat := 3825747180079126664335247

theorem tailTrace_7450616 : CollatzResearch.WordTrace tailWord_7450616 prefixEnd_7450616 3825747180079126664335247 := by
  unfold tailWord_7450616
  simp only [CollatzResearch.WordTrace]
  refine ⟨135873145187849085375941851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181164193583798780501255801 135873145187849085375941851)
  ·
    refine ⟨203809717781773628063912777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135873145187849085375941851 203809717781773628063912777)
    ·
      refine ⟨152857288336330221047934583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203809717781773628063912777 152857288336330221047934583)
      ·
        refine ⟨229285932504495331571901875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152857288336330221047934583 229285932504495331571901875)
        ·
          refine ⟨343928898756742997357852813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229285932504495331571901875 343928898756742997357852813)
          ·
            refine ⟨128973337033778624009194805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343928898756742997357852813 128973337033778624009194805)
            ·
              refine ⟨12091250346916746000862013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128973337033778624009194805 12091250346916746000862013)
              ·
                refine ⟨4534218880093779750323255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12091250346916746000862013 4534218880093779750323255)
                ·
                  refine ⟨6801328320140669625484883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4534218880093779750323255 6801328320140669625484883)
                  ·
                    refine ⟨10201992480211004438227325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6801328320140669625484883 10201992480211004438227325)
                    ·
                      refine ⟨3825747180079126664335247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10201992480211004438227325 3825747180079126664335247)
                      ·
                        rfl

theorem cell23_7450616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 1, 1, 3].length) (baseStart_7450616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450616 prefixEnd_7450616 := by exact prefixLift 7450616
  have htrace : WordTrace (prefixWord ++ tailWord_7450616) baseStart_7450616 baseEnd_7450616 := by
    simpa [prefixWord, tailWord_7450616, baseEnd_7450616] using wordTrace_append hprefix tailTrace_7450616
  have hstable : (prefixWord ++ tailWord_7450616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450616).length < 2 ^ (prefixWord ++ tailWord_7450616).sum := by decide
  have hdescent : baseEnd_7450616 < baseStart_7450616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450632 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 4, 4]
def baseStart_7450632 : Nat := 118140960795 + 7450632 * 2 ^ 59
def prefixEnd_7450632 : Nat := 4983230072969 + 3 ^ 40 * 7450632 * 2
def baseEnd_7450632 : Nat := 1275251798589866200578391

theorem tailTrace_7450632 : CollatzResearch.WordTrace tailWord_7450632 prefixEnd_7450632 1275251798589866200578391 := by
  unfold tailWord_7450632
  simp only [CollatzResearch.WordTrace]
  refine ⟨135873436971820102742233075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181164582629093470322977433 135873436971820102742233075)
  ·
    refine ⟨203810155457730154113349613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135873436971820102742233075 203810155457730154113349613)
    ·
      refine ⟨76428808296648807792506105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203810155457730154113349613 76428808296648807792506105)
      ·
        refine ⟨57321606222486605844379579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76428808296648807792506105 57321606222486605844379579)
        ·
          refine ⟨85982409333729908766569369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57321606222486605844379579 85982409333729908766569369)
          ·
            refine ⟨64486807000297431574927027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85982409333729908766569369 64486807000297431574927027)
            ·
              refine ⟨96730210500446147362390541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64486807000297431574927027 96730210500446147362390541)
              ·
                refine ⟨36273828937667305260896453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96730210500446147362390541 36273828937667305260896453)
                ·
                  refine ⟨6801342925812619736418085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36273828937667305260896453 6801342925812619736418085)
                  ·
                    refine ⟨1275251798589866200578391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6801342925812619736418085 1275251798589866200578391)
                    ·
                      rfl

theorem cell23_7450632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_7450632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450632 prefixEnd_7450632 := by exact prefixLift 7450632
  have htrace : WordTrace (prefixWord ++ tailWord_7450632) baseStart_7450632 baseEnd_7450632 := by
    simpa [prefixWord, tailWord_7450632, baseEnd_7450632] using wordTrace_append hprefix tailTrace_7450632
  have hstable : (prefixWord ++ tailWord_7450632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450632).length < 2 ^ (prefixWord ++ tailWord_7450632).sum := by decide
  have hdescent : baseEnd_7450632 < baseStart_7450632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450635 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 6]
def baseStart_7450635 : Nat := 118140960795 + 7450635 * 2 ^ 59
def prefixEnd_7450635 : Nat := 4983230072969 + 3 ^ 40 * 7450635 * 2
def baseEnd_7450635 : Nat := 3825756936211562089997659

theorem tailTrace_7450635 : CollatzResearch.WordTrace tailWord_7450635 prefixEnd_7450635 3825756936211562089997659 := by
  unfold tailWord_7450635
  simp only [CollatzResearch.WordTrace]
  refine ⟨271746983362629336996825359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181164655575086224664550239 271746983362629336996825359)
  ·
    refine ⟨407620475043944005495238039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271746983362629336996825359 407620475043944005495238039)
    ·
      refine ⟨611430712565916008242857059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407620475043944005495238039 611430712565916008242857059)
      ·
        refine ⟨917146068848874012364285589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611430712565916008242857059 917146068848874012364285589)
        ·
          refine ⟨42991221977290969329575887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 917146068848874012364285589 42991221977290969329575887)
          ·
            refine ⟨64486832965936453994363831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42991221977290969329575887 64486832965936453994363831)
            ·
              refine ⟨96730249448904680991545747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64486832965936453994363831 96730249448904680991545747)
              ·
                refine ⟨145095374173357021487318621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96730249448904680991545747 145095374173357021487318621)
                ·
                  refine ⟨54410765315008883057744483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145095374173357021487318621 54410765315008883057744483)
                  ·
                    refine ⟨81616147972513324586616725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54410765315008883057744483 81616147972513324586616725)
                    ·
                      refine ⟨3825756936211562089997659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81616147972513324586616725 3825756936211562089997659)
                      ·
                        rfl

theorem cell23_7450635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 6].length) (baseStart_7450635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450635 prefixEnd_7450635 := by exact prefixLift 7450635
  have htrace : WordTrace (prefixWord ++ tailWord_7450635) baseStart_7450635 baseEnd_7450635 := by
    simpa [prefixWord, tailWord_7450635, baseEnd_7450635] using wordTrace_append hprefix tailTrace_7450635
  have hstable : (prefixWord ++ tailWord_7450635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450635).length < 2 ^ (prefixWord ++ tailWord_7450635).sum := by decide
  have hdescent : baseEnd_7450635 < baseStart_7450635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450652 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_7450652 : Nat := 118140960795 + 7450652 * 2 ^ 59
def prefixEnd_7450652 : Nat := 4983230072969 + 3 ^ 40 * 7450652 * 2
def baseEnd_7450652 : Nat := 3825765665382688523485081

theorem tailTrace_7450652 : CollatzResearch.WordTrace tailWord_7450652 prefixEnd_7450652 3825765665382688523485081 := by
  unfold tailWord_7450652
  simp only [CollatzResearch.WordTrace]
  refine ⟨135873801701783874450097105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181165068935711832600129473 135873801701783874450097105)
  ·
    refine ⟨101905351276337905837572829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135873801701783874450097105 101905351276337905837572829)
    ·
      refine ⟨38214506728626714689089811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101905351276337905837572829 38214506728626714689089811)
      ·
        refine ⟨57321760092940072033634717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38214506728626714689089811 57321760092940072033634717)
        ·
          refine ⟨21495660034852527012613019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57321760092940072033634717 21495660034852527012613019)
          ·
            refine ⟨32243490052278790518919529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21495660034852527012613019 32243490052278790518919529)
            ·
              refine ⟨24182617539209092889189647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32243490052278790518919529 24182617539209092889189647)
              ·
                refine ⟨36273926308813639333784471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24182617539209092889189647 36273926308813639333784471)
                ·
                  refine ⟨54410889463220459000676707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36273926308813639333784471 54410889463220459000676707)
                  ·
                    refine ⟨81616334194830688501015061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54410889463220459000676707 81616334194830688501015061)
                    ·
                      refine ⟨3825765665382688523485081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81616334194830688501015061 3825765665382688523485081)
                      ·
                        rfl

theorem cell23_7450652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_7450652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450652 prefixEnd_7450652 := by exact prefixLift 7450652
  have htrace : WordTrace (prefixWord ++ tailWord_7450652) baseStart_7450652 baseEnd_7450652 := by
    simpa [prefixWord, tailWord_7450652, baseEnd_7450652] using wordTrace_append hprefix tailTrace_7450652
  have hstable : (prefixWord ++ tailWord_7450652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450652).length < 2 ^ (prefixWord ++ tailWord_7450652).sum := by decide
  have hdescent : baseEnd_7450652 < baseStart_7450652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450672 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 3]
def baseStart_7450672 : Nat := 118140960795 + 7450672 * 2 ^ 59
def prefixEnd_7450672 : Nat := 4983230072969 + 3 ^ 40 * 7450672 * 2
def baseEnd_7450672 : Nat := 3825775934995778445234989

theorem tailTrace_7450672 : CollatzResearch.WordTrace tailWord_7450672 prefixEnd_7450672 3825775934995778445234989 := by
  unfold tailWord_7450672
  simp only [CollatzResearch.WordTrace]
  refine ⟨135874166431747646157961135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181165555242330194877281513 135874166431747646157961135)
  ·
    refine ⟨203811249647621469236941703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135874166431747646157961135 203811249647621469236941703)
    ·
      refine ⟨305716874471432203855412555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203811249647621469236941703 305716874471432203855412555)
      ·
        refine ⟨458575311707148305783118833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305716874471432203855412555 458575311707148305783118833)
        ·
          refine ⟨343931483780361229337339125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458575311707148305783118833 343931483780361229337339125)
          ·
            refine ⟨32243576604408865250375543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 343931483780361229337339125 32243576604408865250375543)
            ·
              refine ⟨48365364906613297875563315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32243576604408865250375543 48365364906613297875563315)
              ·
                refine ⟨72548047359919946813344973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48365364906613297875563315 72548047359919946813344973)
                ·
                  refine ⟨27205517759969980055004365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72548047359919946813344973 27205517759969980055004365)
                  ·
                    refine ⟨10202069159988742520626637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27205517759969980055004365 10202069159988742520626637)
                    ·
                      refine ⟨3825775934995778445234989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10202069159988742520626637 3825775934995778445234989)
                      ·
                        rfl

theorem cell23_7450672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 3].length) (baseStart_7450672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450672 prefixEnd_7450672 := by exact prefixLift 7450672
  have htrace : WordTrace (prefixWord ++ tailWord_7450672) baseStart_7450672 baseEnd_7450672 := by
    simpa [prefixWord, tailWord_7450672, baseEnd_7450672] using wordTrace_append hprefix tailTrace_7450672
  have hstable : (prefixWord ++ tailWord_7450672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450672).length < 2 ^ (prefixWord ++ tailWord_7450672).sum := by decide
  have hdescent : baseEnd_7450672 < baseStart_7450672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450706 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_7450706 : Nat := 118140960795 + 7450706 * 2 ^ 59
def prefixEnd_7450706 : Nat := 4983230072969 + 3 ^ 40 * 7450706 * 2
def baseEnd_7450706 : Nat := 3825793393338031312209833

theorem tailTrace_7450706 : CollatzResearch.WordTrace tailWord_7450706 prefixEnd_7450706 3825793393338031312209833 := by
  unfold tailWord_7450706
  simp only [CollatzResearch.WordTrace]
  refine ⟨67937393236343029030664993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181166381963581410748439981 67937393236343029030664993)
  ·
    refine ⟨50953044927257271772998745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67937393236343029030664993 50953044927257271772998745)
    ·
      refine ⟨38214783695442953829749059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50953044927257271772998745 38214783695442953829749059)
      ·
        refine ⟨57322175543164430744623589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38214783695442953829749059 57322175543164430744623589)
        ·
          refine ⟨10747907914343330764616923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57322175543164430744623589 10747907914343330764616923)
          ·
            refine ⟨16121861871514996146925385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10747907914343330764616923 16121861871514996146925385)
            ·
              refine ⟨12091396403636247110194039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16121861871514996146925385 12091396403636247110194039)
              ·
                refine ⟨18137094605454370665291059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12091396403636247110194039 18137094605454370665291059)
                ·
                  refine ⟨27205641908181555997936589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18137094605454370665291059 27205641908181555997936589)
                  ·
                    refine ⟨10202115715568083499226221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27205641908181555997936589 10202115715568083499226221)
                    ·
                      refine ⟨3825793393338031312209833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10202115715568083499226221 3825793393338031312209833)
                      ·
                        rfl

theorem cell23_7450706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_7450706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450706 prefixEnd_7450706 := by exact prefixLift 7450706
  have htrace : WordTrace (prefixWord ++ tailWord_7450706) baseStart_7450706 baseEnd_7450706 := by
    simpa [prefixWord, tailWord_7450706, baseEnd_7450706] using wordTrace_append hprefix tailTrace_7450706
  have hstable : (prefixWord ++ tailWord_7450706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450706).length < 2 ^ (prefixWord ++ tailWord_7450706).sum := by decide
  have hdescent : baseEnd_7450706 < baseStart_7450706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450716 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_7450716 : Nat := 118140960795 + 7450716 * 2 ^ 59
def prefixEnd_7450716 : Nat := 4983230072969 + 3 ^ 40 * 7450716 * 2
def baseEnd_7450716 : Nat := 3825798528144576273084787

theorem tailTrace_7450716 : CollatzResearch.WordTrace tailWord_7450716 prefixEnd_7450716 3825798528144576273084787 := by
  unfold tailWord_7450716
  simp only [CollatzResearch.WordTrace]
  refine ⟨135874968837667943915262001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181166625116890591887016001 135874968837667943915262001)
  ·
    refine ⟨101906226628250957936446501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135874968837667943915262001 101906226628250957936446501)
    ·
      refine ⟨19107417492797054613083719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101906226628250957936446501 19107417492797054613083719)
      ·
        refine ⟨28661126239195581919625579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19107417492797054613083719 28661126239195581919625579)
        ·
          refine ⟨42991689358793372879438369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28661126239195581919625579 42991689358793372879438369)
          ·
            refine ⟨32243767019095029659578777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42991689358793372879438369 32243767019095029659578777)
            ·
              refine ⟨24182825264321272244684083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32243767019095029659578777 24182825264321272244684083)
              ·
                refine ⟨36274237896481908367026125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24182825264321272244684083 36274237896481908367026125)
                ·
                  refine ⟨13602839211180715637634797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36274237896481908367026125 13602839211180715637634797)
                  ·
                    refine ⟨5101064704192768364113049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13602839211180715637634797 5101064704192768364113049)
                    ·
                      refine ⟨3825798528144576273084787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5101064704192768364113049 3825798528144576273084787)
                      ·
                        rfl

theorem cell23_7450716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_7450716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450716 prefixEnd_7450716 := by exact prefixLift 7450716
  have htrace : WordTrace (prefixWord ++ tailWord_7450716) baseStart_7450716 baseEnd_7450716 := by
    simpa [prefixWord, tailWord_7450716, baseEnd_7450716] using wordTrace_append hprefix tailTrace_7450716
  have hstable : (prefixWord ++ tailWord_7450716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450716).length < 2 ^ (prefixWord ++ tailWord_7450716).sum := by decide
  have hdescent : baseEnd_7450716 < baseStart_7450716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450729 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 1, 4, 2]
def baseStart_7450729 : Nat := 118140960795 + 7450729 * 2 ^ 59
def prefixEnd_7450729 : Nat := 4983230072969 + 3 ^ 40 * 7450729 * 2
def baseEnd_7450729 : Nat := 3825805203393084722222227

theorem tailTrace_7450729 : CollatzResearch.WordTrace tailWord_7450729 prefixEnd_7450729 3825805203393084722222227 := by
  unfold tailWord_7450729
  simp only [CollatzResearch.WordTrace]
  refine ⟨271750411824288791050747241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181166941216192527367164827 271750411824288791050747241)
  ·
    refine ⟨203812808868216593288060431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271750411824288791050747241 203812808868216593288060431)
    ·
      refine ⟨305719213302324889932090647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203812808868216593288060431 305719213302324889932090647)
      ·
        refine ⟨458578819953487334898135971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305719213302324889932090647 458578819953487334898135971)
        ·
          refine ⟨687868229930231002347203957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458578819953487334898135971 687868229930231002347203957)
          ·
            refine ⟨64487646555959156470050371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 687868229930231002347203957 64487646555959156470050371)
            ·
              refine ⟨96731469833938734705075557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64487646555959156470050371 96731469833938734705075557)
              ·
                refine ⟨18137150593863512757201667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96731469833938734705075557 18137150593863512757201667)
                ·
                  refine ⟨27205725890795269135802501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18137150593863512757201667 27205725890795269135802501)
                  ·
                    refine ⟨5101073604524112962962969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27205725890795269135802501 5101073604524112962962969)
                    ·
                      refine ⟨3825805203393084722222227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5101073604524112962962969 3825805203393084722222227)
                      ·
                        rfl

theorem cell23_7450729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 4, 2].length) (baseStart_7450729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450729 prefixEnd_7450729 := by exact prefixLift 7450729
  have htrace : WordTrace (prefixWord ++ tailWord_7450729) baseStart_7450729 baseEnd_7450729 := by
    simpa [prefixWord, tailWord_7450729, baseEnd_7450729] using wordTrace_append hprefix tailTrace_7450729
  have hstable : (prefixWord ++ tailWord_7450729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450729).length < 2 ^ (prefixWord ++ tailWord_7450729).sum := by decide
  have hdescent : baseEnd_7450729 < baseStart_7450729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450814 : List Nat := [4, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2]
def baseStart_7450814 : Nat := 118140960795 + 7450814 * 2 ^ 59
def prefixEnd_7450814 : Nat := 4983230072969 + 3 ^ 40 * 7450814 * 2
def baseEnd_7450814 : Nat := 3825848849248716889659337

theorem tailTrace_7450814 : CollatzResearch.WordTrace tailWord_7450814 prefixEnd_7450814 3825848849248716889659337 := by
  unfold tailWord_7450814
  simp only [CollatzResearch.WordTrace]
  refine ⟨33969189003622606320948937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181169008019320567045060997 33969189003622606320948937)
  ·
    refine ⟨25476891752716954740711703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33969189003622606320948937 25476891752716954740711703)
    ·
      refine ⟨38215337629075432111067555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25476891752716954740711703 38215337629075432111067555)
      ·
        refine ⟨57323006443613148166601333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38215337629075432111067555 57323006443613148166601333)
        ·
          refine ⟨5374031854088732640618875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57323006443613148166601333 5374031854088732640618875)
          ·
            refine ⟨8061047781133098960928313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5374031854088732640618875 8061047781133098960928313)
            ·
              refine ⟨6045785835849824220696235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8061047781133098960928313 6045785835849824220696235)
              ·
                refine ⟨9068678753774736331044353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6045785835849824220696235 9068678753774736331044353)
                ·
                  refine ⟨6801509065331052248283265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9068678753774736331044353 6801509065331052248283265)
                  ·
                    refine ⟨5101131798998289186212449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6801509065331052248283265 5101131798998289186212449)
                    ·
                      refine ⟨3825848849248716889659337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5101131798998289186212449 3825848849248716889659337)
                      ·
                        rfl

theorem cell23_7450814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_7450814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450814 prefixEnd_7450814 := by exact prefixLift 7450814
  have htrace : WordTrace (prefixWord ++ tailWord_7450814) baseStart_7450814 baseEnd_7450814 := by
    simpa [prefixWord, tailWord_7450814, baseEnd_7450814] using wordTrace_append hprefix tailTrace_7450814
  have hstable : (prefixWord ++ tailWord_7450814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450814).length < 2 ^ (prefixWord ++ tailWord_7450814).sum := by decide
  have hdescent : baseEnd_7450814 < baseStart_7450814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450819 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 6, 4, 2]
def baseStart_7450819 : Nat := 118140960795 + 7450819 * 2 ^ 59
def prefixEnd_7450819 : Nat := 4983230072969 + 3 ^ 40 * 7450819 * 2
def baseEnd_7450819 : Nat := 3825851416651989370096813

theorem tailTrace_7450819 : CollatzResearch.WordTrace tailWord_7450819 prefixEnd_7450819 3825851416651989370096813 := by
  unfold tailWord_7450819
  simp only [CollatzResearch.WordTrace]
  refine ⟨271753694393962736421523511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181169129595975157614349007 271753694393962736421523511)
  ·
    refine ⟨407630541590944104632285267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271753694393962736421523511 407630541590944104632285267)
    ·
      refine ⟨611445812386416156948427901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407630541590944104632285267 611445812386416156948427901)
      ·
        refine ⟨229292179644906058855660463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 611445812386416156948427901 229292179644906058855660463)
        ·
          refine ⟨343938269467359088283490695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229292179644906058855660463 343938269467359088283490695)
          ·
            refine ⟨515907404201038632425236043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343938269467359088283490695 515907404201038632425236043)
            ·
              refine ⟨773861106301557948637854065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515907404201038632425236043 773861106301557948637854065)
              ·
                refine ⟨580395829726168461478390549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 773861106301557948637854065 580395829726168461478390549)
                ·
                  refine ⟨27206054518414146631799557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 580395829726168461478390549 27206054518414146631799557)
                  ·
                    refine ⟨5101135222202652493462417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27206054518414146631799557 5101135222202652493462417)
                    ·
                      refine ⟨3825851416651989370096813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5101135222202652493462417 3825851416651989370096813)
                      ·
                        rfl

theorem cell23_7450819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 4, 2].length) (baseStart_7450819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450819 prefixEnd_7450819 := by exact prefixLift 7450819
  have htrace : WordTrace (prefixWord ++ tailWord_7450819) baseStart_7450819 baseEnd_7450819 := by
    simpa [prefixWord, tailWord_7450819, baseEnd_7450819] using wordTrace_append hprefix tailTrace_7450819
  have hstable : (prefixWord ++ tailWord_7450819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450819).length < 2 ^ (prefixWord ++ tailWord_7450819).sum := by decide
  have hdescent : baseEnd_7450819 < baseStart_7450819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450842 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 10]
def baseStart_7450842 : Nat := 118140960795 + 7450842 * 2 ^ 59
def prefixEnd_7450842 : Nat := 4983230072969 + 3 ^ 40 * 7450842 * 2
def baseEnd_7450842 : Nat := 425095914078560308901023

theorem tailTrace_7450842 : CollatzResearch.WordTrace tailWord_7450842 prefixEnd_7450842 425095914078560308901023 := by
  unfold tailWord_7450842
  simp only [CollatzResearch.WordTrace]
  refine ⟨67938633318219852837402695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 181169688848586274233073853 67938633318219852837402695)
  ·
    refine ⟨101907949977329779256104043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67938633318219852837402695 101907949977329779256104043)
    ·
      refine ⟨152861924965994668884156065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101907949977329779256104043 152861924965994668884156065)
      ·
        refine ⟨114646443724496001663117049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152861924965994668884156065 114646443724496001663117049)
        ·
          refine ⟨85984832793372001247337787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114646443724496001663117049 85984832793372001247337787)
          ·
            refine ⟨128977249190058001871006681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85984832793372001247337787 128977249190058001871006681)
            ·
              refine ⟨96732936892543501403255011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128977249190058001871006681 96732936892543501403255011)
              ·
                refine ⟨145099405338815252104882517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96732936892543501403255011 145099405338815252104882517)
                ·
                  refine ⟨425095914078560308901023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 145099405338815252104882517 425095914078560308901023)
                  ·
                    rfl

theorem cell23_7450842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 10].length) (baseStart_7450842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450842 prefixEnd_7450842 := by exact prefixLift 7450842
  have htrace : WordTrace (prefixWord ++ tailWord_7450842) baseStart_7450842 baseEnd_7450842 := by
    simpa [prefixWord, tailWord_7450842, baseEnd_7450842] using wordTrace_append hprefix tailTrace_7450842
  have hstable : (prefixWord ++ tailWord_7450842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450842).length < 2 ^ (prefixWord ++ tailWord_7450842).sum := by decide
  have hdescent : baseEnd_7450842 < baseStart_7450842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450856 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_7450856 : Nat := 118140960795 + 7450856 * 2 ^ 59
def prefixEnd_7450856 : Nat := 4983230072969 + 3 ^ 40 * 7450856 * 2
def baseEnd_7450856 : Nat := 3825870415436205725334143

theorem tailTrace_7450856 : CollatzResearch.WordTrace tailWord_7450856 prefixEnd_7450856 3825870415436205725334143 := by
  unfold tailWord_7450856
  simp only [CollatzResearch.WordTrace]
  refine ⟨135877521947414345870310211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181170029263219127827080281 135877521947414345870310211)
  ·
    refine ⟨203816282921121518805465317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135877521947414345870310211 203816282921121518805465317)
    ·
      refine ⟨38215553047710284776024747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203816282921121518805465317 38215553047710284776024747)
      ·
        refine ⟨57323329571565427164037121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38215553047710284776024747 57323329571565427164037121)
        ·
          refine ⟨42992497178674070373027841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57323329571565427164037121 42992497178674070373027841)
          ·
            refine ⟨32244372884005552779770881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42992497178674070373027841 32244372884005552779770881)
            ·
              refine ⟨24183279663004164584828161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32244372884005552779770881 24183279663004164584828161)
              ·
                refine ⟨18137459747253123438621121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24183279663004164584828161 18137459747253123438621121)
                ·
                  refine ⟨13603094810439842578965841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18137459747253123438621121 13603094810439842578965841)
                  ·
                    refine ⟨10202321107829881934224381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13603094810439842578965841 10202321107829881934224381)
                    ·
                      refine ⟨3825870415436205725334143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10202321107829881934224381 3825870415436205725334143)
                      ·
                        rfl

theorem cell23_7450856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_7450856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450856 prefixEnd_7450856 := by exact prefixLift 7450856
  have htrace : WordTrace (prefixWord ++ tailWord_7450856) baseStart_7450856 baseEnd_7450856 := by
    simpa [prefixWord, tailWord_7450856, baseEnd_7450856] using wordTrace_append hprefix tailTrace_7450856
  have hstable : (prefixWord ++ tailWord_7450856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450856).length < 2 ^ (prefixWord ++ tailWord_7450856).sum := by decide
  have hdescent : baseEnd_7450856 < baseStart_7450856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450859 : List Nat := [1, 1, 1, 1, 2, 5, 4, 2, 6]
def baseStart_7450859 : Nat := 118140960795 + 7450859 * 2 ^ 59
def prefixEnd_7450859 : Nat := 4983230072969 + 3 ^ 40 * 7450859 * 2
def baseEnd_7450859 : Nat := 425096883986463245955181

theorem tailTrace_7450859 : CollatzResearch.WordTrace tailWord_7450859 prefixEnd_7450859 425096883986463245955181 := by
  unfold tailWord_7450859
  simp only [CollatzResearch.WordTrace]
  refine ⟨271755153313817823252979631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181170102209211882168653087 271755153313817823252979631)
  ·
    refine ⟨407632729970726734879469447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271755153313817823252979631 407632729970726734879469447)
    ·
      refine ⟨611449094956090102319204171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407632729970726734879469447 611449094956090102319204171)
      ·
        refine ⟨917173642434135153478806257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611449094956090102319204171 917173642434135153478806257)
        ·
          refine ⟨687880231825601365109104693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 917173642434135153478806257 687880231825601365109104693)
          ·
            refine ⟨64488771733650127978978565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 687880231825601365109104693 64488771733650127978978565)
            ·
              refine ⟨12091644700059398996058481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64488771733650127978978565 12091644700059398996058481)
              ·
                refine ⟨9068733525044549247043861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12091644700059398996058481 9068733525044549247043861)
                ·
                  refine ⟨425096883986463245955181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9068733525044549247043861 425096883986463245955181)
                  ·
                    rfl

theorem cell23_7450859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 6].length) (baseStart_7450859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450859 prefixEnd_7450859 := by exact prefixLift 7450859
  have htrace : WordTrace (prefixWord ++ tailWord_7450859) baseStart_7450859 baseEnd_7450859 := by
    simpa [prefixWord, tailWord_7450859, baseEnd_7450859] using wordTrace_append hprefix tailTrace_7450859
  have hstable : (prefixWord ++ tailWord_7450859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450859).length < 2 ^ (prefixWord ++ tailWord_7450859).sum := by decide
  have hdescent : baseEnd_7450859 < baseStart_7450859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450863 : List Nat := [1, 1, 2, 1, 6, 2, 1, 4, 1, 4]
def baseStart_7450863 : Nat := 118140960795 + 7450863 * 2 ^ 59
def prefixEnd_7450863 : Nat := 4983230072969 + 3 ^ 40 * 7450863 * 2
def baseEnd_7450863 : Nat := 1275291336600262399315537

theorem tailTrace_7450863 : CollatzResearch.WordTrace tailWord_7450863 prefixEnd_7450863 1275291336600262399315537 := by
  unfold tailWord_7450863
  simp only [CollatzResearch.WordTrace]
  refine ⟨271755299205803331936125243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181170199470535554624083495 271755299205803331936125243)
  ·
    refine ⟨407632948808704997904187865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 271755299205803331936125243 407632948808704997904187865)
    ·
      refine ⟨305724711606528748428140899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407632948808704997904187865 305724711606528748428140899)
      ·
        refine ⟨458587067409793122642211349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305724711606528748428140899 458587067409793122642211349)
        ·
          refine ⟨21496268784834052623853657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 458587067409793122642211349 21496268784834052623853657)
          ·
            refine ⟨16122201588625539467890243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21496268784834052623853657 16122201588625539467890243)
            ·
              refine ⟨24183302382938309201835365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16122201588625539467890243 24183302382938309201835365)
              ·
                refine ⟨4534369196800932975344131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24183302382938309201835365 4534369196800932975344131)
                ·
                  refine ⟨6801553795201399463016197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4534369196800932975344131 6801553795201399463016197)
                  ·
                    refine ⟨1275291336600262399315537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6801553795201399463016197 1275291336600262399315537)
                    ·
                      rfl

theorem cell23_7450863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 1, 4].length) (baseStart_7450863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450863 prefixEnd_7450863 := by exact prefixLift 7450863
  have htrace : WordTrace (prefixWord ++ tailWord_7450863) baseStart_7450863 baseEnd_7450863 := by
    simpa [prefixWord, tailWord_7450863, baseEnd_7450863] using wordTrace_append hprefix tailTrace_7450863
  have hstable : (prefixWord ++ tailWord_7450863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450863).length < 2 ^ (prefixWord ++ tailWord_7450863).sum := by decide
  have hdescent : baseEnd_7450863 < baseStart_7450863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450889 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 3, 5]
def baseStart_7450889 : Nat := 118140960795 + 7450889 * 2 ^ 59
def prefixEnd_7450889 : Nat := 4983230072969 + 3 ^ 40 * 7450889 * 2
def baseEnd_7450889 : Nat := 1275295786765934698740497

theorem tailTrace_7450889 : CollatzResearch.WordTrace tailWord_7450889 prefixEnd_7450889 1275295786765934698740497 := by
  unfold tailWord_7450889
  simp only [CollatzResearch.WordTrace]
  refine ⟨271756247503709138376571721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 181170831669139425584381147 271756247503709138376571721)
  ·
    refine ⟨203817185627781853782428791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 271756247503709138376571721 203817185627781853782428791)
    ·
      refine ⟨305725778441672780673643187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203817185627781853782428791 305725778441672780673643187)
      ·
        refine ⟨458588667662509171010464781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305725778441672780673643187 458588667662509171010464781)
        ·
          refine ⟨171970750373440939128924293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 458588667662509171010464781 171970750373440939128924293)
          ·
            refine ⟨32244515695020176086673305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171970750373440939128924293 32244515695020176086673305)
            ·
              refine ⟨24183386771265132065004979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32244515695020176086673305 24183386771265132065004979)
              ·
                refine ⟨36275080156897698097507469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24183386771265132065004979 36275080156897698097507469)
                ·
                  refine ⟨13603155058836636786565301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36275080156897698097507469 13603155058836636786565301)
                  ·
                    refine ⟨1275295786765934698740497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13603155058836636786565301 1275295786765934698740497)
                    ·
                      rfl

theorem cell23_7450889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 5].length) (baseStart_7450889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450889 prefixEnd_7450889 := by exact prefixLift 7450889
  have htrace : WordTrace (prefixWord ++ tailWord_7450889) baseStart_7450889 baseEnd_7450889 := by
    simpa [prefixWord, tailWord_7450889, baseEnd_7450889] using wordTrace_append hprefix tailTrace_7450889
  have hstable : (prefixWord ++ tailWord_7450889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450889).length < 2 ^ (prefixWord ++ tailWord_7450889).sum := by decide
  have hdescent : baseEnd_7450889 < baseStart_7450889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450910 : List Nat := [4, 3, 2, 1, 1, 3, 1, 2, 6]
def baseStart_7450910 : Nat := 118140960795 + 7450910 * 2 ^ 59
def prefixEnd_7450910 : Nat := 4983230072969 + 3 ^ 40 * 7450910 * 2
def baseEnd_7450910 : Nat := 425099793710172057117655

theorem tailTrace_7450910 : CollatzResearch.WordTrace tailWord_7450910 prefixEnd_7450910 425099793710172057117655 := by
  unfold tailWord_7450910
  simp only [CollatzResearch.WordTrace]
  refine ⟨33969626679579132370385773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 181171342291088705975390789 33969626679579132370385773)
  ·
    refine ⟨12738610004842174638894665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33969626679579132370385773 12738610004842174638894665)
    ·
      refine ⟨9553957503631630979170999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12738610004842174638894665 9553957503631630979170999)
      ·
        refine ⟨14330936255447446468756499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9553957503631630979170999 14330936255447446468756499)
        ·
          refine ⟨21496404383171169703134749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14330936255447446468756499 21496404383171169703134749)
          ·
            refine ⟨8061151643689188638675531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21496404383171169703134749 8061151643689188638675531)
            ·
              refine ⟨12091727465533782958013297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8061151643689188638675531 12091727465533782958013297)
              ·
                refine ⟨9068795599150337218509973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12091727465533782958013297 9068795599150337218509973)
                ·
                  refine ⟨425099793710172057117655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9068795599150337218509973 425099793710172057117655)
                  ·
                    rfl

theorem cell23_7450910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_7450910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450910 prefixEnd_7450910 := by exact prefixLift 7450910
  have htrace : WordTrace (prefixWord ++ tailWord_7450910) baseStart_7450910 baseEnd_7450910 := by
    simpa [prefixWord, tailWord_7450910, baseEnd_7450910] using wordTrace_append hprefix tailTrace_7450910
  have hstable : (prefixWord ++ tailWord_7450910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450910).length < 2 ^ (prefixWord ++ tailWord_7450910).sum := by decide
  have hdescent : baseEnd_7450910 < baseStart_7450910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450920 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_7450920 : Nat := 118140960795 + 7450920 * 2 ^ 59
def prefixEnd_7450920 : Nat := 4983230072969 + 3 ^ 40 * 7450920 * 2
def baseEnd_7450920 : Nat := 3825903278198093474933849

theorem tailTrace_7450920 : CollatzResearch.WordTrace tailWord_7450920 prefixEnd_7450920 3825903278198093474933849 := by
  unfold tailWord_7450920
  simp only [CollatzResearch.WordTrace]
  refine ⟨135878689083298415335475107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181171585444397887113966809 135878689083298415335475107)
  ·
    refine ⟨203818033624947623003212661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135878689083298415335475107 203818033624947623003212661)
    ·
      refine ⟨19107940652338839656551187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203818033624947623003212661 19107940652338839656551187)
      ·
        refine ⟨28661910978508259484826781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19107940652338839656551187 28661910978508259484826781)
        ·
          refine ⟨10748216616940597306810043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28661910978508259484826781 10748216616940597306810043)
          ·
            refine ⟨16122324925410895960215065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10748216616940597306810043 16122324925410895960215065)
            ·
              refine ⟨12091743694058171970161299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16122324925410895960215065 12091743694058171970161299)
              ·
                refine ⟨18137615541087257955241949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12091743694058171970161299 18137615541087257955241949)
                ·
                  refine ⟨6801605827907721733215731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18137615541087257955241949 6801605827907721733215731)
                  ·
                    refine ⟨10202408741861582599823597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6801605827907721733215731 10202408741861582599823597)
                    ·
                      refine ⟨3825903278198093474933849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10202408741861582599823597 3825903278198093474933849)
                      ·
                        rfl

theorem cell23_7450920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_7450920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450920 prefixEnd_7450920 := by exact prefixLift 7450920
  have htrace : WordTrace (prefixWord ++ tailWord_7450920) baseStart_7450920 baseEnd_7450920 := by
    simpa [prefixWord, tailWord_7450920, baseEnd_7450920] using wordTrace_append hprefix tailTrace_7450920
  have hstable : (prefixWord ++ tailWord_7450920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450920).length < 2 ^ (prefixWord ++ tailWord_7450920).sum := by decide
  have hdescent : baseEnd_7450920 < baseStart_7450920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7450936 : List Nat := [2, 1, 2, 1, 3, 1, 2, 5, 2, 4]
def baseStart_7450936 : Nat := 118140960795 + 7450936 * 2 ^ 59
def prefixEnd_7450936 : Nat := 4983230072969 + 3 ^ 40 * 7450936 * 2
def baseEnd_7450936 : Nat := 1275303831296188470777925

theorem tailTrace_7450936 : CollatzResearch.WordTrace tailWord_7450936 prefixEnd_7450936 1275303831296188470777925 := by
  unfold tailWord_7450936
  simp only [CollatzResearch.WordTrace]
  refine ⟨135878980867269432701766331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 181171974489692576935688441 135878980867269432701766331)
  ·
    refine ⟨203818471300904149052649497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135878980867269432701766331 203818471300904149052649497)
    ·
      refine ⟨152863853475678111789487123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203818471300904149052649497 152863853475678111789487123)
      ·
        refine ⟨229295780213517167684230685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152863853475678111789487123 229295780213517167684230685)
        ·
          refine ⟨85985917580068937881586507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229295780213517167684230685 85985917580068937881586507)
          ·
            refine ⟨128978876370103406822379761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85985917580068937881586507 128978876370103406822379761)
            ·
              refine ⟨96734157277577555116784821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128978876370103406822379761 96734157277577555116784821)
              ·
                refine ⟨9068827244772895792198577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96734157277577555116784821 9068827244772895792198577)
                ·
                  refine ⟨6801620433579671844148933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9068827244772895792198577 6801620433579671844148933)
                  ·
                    refine ⟨1275303831296188470777925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6801620433579671844148933 1275303831296188470777925)
                    ·
                      rfl

theorem cell23_7450936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_7450936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7450936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7450936 prefixEnd_7450936 := by exact prefixLift 7450936
  have htrace : WordTrace (prefixWord ++ tailWord_7450936) baseStart_7450936 baseEnd_7450936 := by
    simpa [prefixWord, tailWord_7450936, baseEnd_7450936] using wordTrace_append hprefix tailTrace_7450936
  have hstable : (prefixWord ++ tailWord_7450936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7450936).length < 2 ^ (prefixWord ++ tailWord_7450936).sum := by decide
  have hdescent : baseEnd_7450936 < baseStart_7450936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7450936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
