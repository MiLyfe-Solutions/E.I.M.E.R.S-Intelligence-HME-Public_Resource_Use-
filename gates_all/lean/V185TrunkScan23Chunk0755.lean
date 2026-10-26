import V185TrunkScan23Chunk0754

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4464289 : List Nat := [1, 2, 3, 3, 2, 3, 1, 2, 2, 1, 3]
def baseStart_4464289 : Nat := 118140960795 + 4464289 * 2 ^ 59
def prefixEnd_4464289 : Nat := 4983230072969 + 3 ^ 40 * 4464289 * 2
def baseEnd_4464289 : Nat := 2292326037579789182456615

theorem tailTrace_4464289 : CollatzResearch.WordTrace tailWord_4464289 prefixEnd_4464289 2292326037579789182456615 := by
  unfold tailWord_4464289
  simp only [CollatzResearch.WordTrace]
  refine ⟨162825996523650867705371921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108550664349100578470247947 162825996523650867705371921)
  ·
    refine ⟨122119497392738150779028941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162825996523650867705371921 122119497392738150779028941)
    ·
      refine ⟨45794811522276806542135853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122119497392738150779028941 45794811522276806542135853)
      ·
        refine ⟨17173054320853802453300945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45794811522276806542135853 17173054320853802453300945)
        ·
          refine ⟨12879790740640351839975709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17173054320853802453300945 12879790740640351839975709)
          ·
            refine ⟨4829921527740131939990891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12879790740640351839975709 4829921527740131939990891)
            ·
              refine ⟨7244882291610197909986337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4829921527740131939990891 7244882291610197909986337)
              ·
                refine ⟨5433661718707648432489753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7244882291610197909986337 5433661718707648432489753)
                ·
                  refine ⟨4075246289030736324367315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5433661718707648432489753 4075246289030736324367315)
                  ·
                    refine ⟨6112869433546104486550973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4075246289030736324367315 6112869433546104486550973)
                    ·
                      refine ⟨2292326037579789182456615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6112869433546104486550973 2292326037579789182456615)
                      ·
                        rfl

theorem cell23_4464289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_4464289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464289 prefixEnd_4464289 := by exact prefixLift 4464289
  have htrace : WordTrace (prefixWord ++ tailWord_4464289) baseStart_4464289 baseEnd_4464289 := by
    simpa [prefixWord, tailWord_4464289, baseEnd_4464289] using wordTrace_append hprefix tailTrace_4464289
  have hstable : (prefixWord ++ tailWord_4464289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464289).length < 2 ^ (prefixWord ++ tailWord_4464289).sum := by decide
  have hdescent : baseEnd_4464289 < baseStart_4464289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464312 : List Nat := [2, 1, 2, 1, 2, 1, 1, 7, 2, 2, 2]
def baseStart_4464312 : Nat := 118140960795 + 4464312 * 2 ^ 59
def prefixEnd_4464312 : Nat := 4983230072969 + 3 ^ 40 * 4464312 * 2
def baseEnd_4464312 : Nat := 2292337847634842592469009

theorem tailTrace_4464312 : CollatzResearch.WordTrace tailWord_4464312 prefixEnd_4464312 2292337847634842592469009 := by
  unfold tailWord_4464312
  simp only [CollatzResearch.WordTrace]
  refine ⟨81413417701283771316729595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108551223601711695088972793 81413417701283771316729595)
  ·
    refine ⟨122120126551925656975094393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81413417701283771316729595 122120126551925656975094393)
    ·
      refine ⟨91590094913944242731320795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122120126551925656975094393 91590094913944242731320795)
      ·
        refine ⟨137385142370916364096981193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91590094913944242731320795 137385142370916364096981193)
        ·
          refine ⟨103038856778187273072735895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137385142370916364096981193 103038856778187273072735895)
          ·
            refine ⟨154558285167280909609103843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103038856778187273072735895 154558285167280909609103843)
            ·
              refine ⟨231837427750921364413655765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154558285167280909609103843 231837427750921364413655765)
              ·
                refine ⟨5433689712912219478445057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 231837427750921364413655765 5433689712912219478445057)
                ·
                  refine ⟨4075267284684164608833793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5433689712912219478445057 4075267284684164608833793)
                  ·
                    refine ⟨3056450463513123456625345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4075267284684164608833793 3056450463513123456625345)
                    ·
                      refine ⟨2292337847634842592469009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3056450463513123456625345 2292337847634842592469009)
                      ·
                        rfl

theorem cell23_4464312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 2, 2, 2].length) (baseStart_4464312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464312 prefixEnd_4464312 := by exact prefixLift 4464312
  have htrace : WordTrace (prefixWord ++ tailWord_4464312) baseStart_4464312 baseEnd_4464312 := by
    simpa [prefixWord, tailWord_4464312, baseEnd_4464312] using wordTrace_append hprefix tailTrace_4464312
  have hstable : (prefixWord ++ tailWord_4464312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464312).length < 2 ^ (prefixWord ++ tailWord_4464312).sum := by decide
  have hdescent : baseEnd_4464312 < baseStart_4464312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464368 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 4]
def baseStart_4464368 : Nat := 118140960795 + 4464368 * 2 ^ 59
def prefixEnd_4464368 : Nat := 4983230072969 + 3 ^ 40 * 4464368 * 2
def baseEnd_4464368 : Nat := 2292366602551494373368751

theorem tailTrace_4464368 : CollatzResearch.WordTrace tailWord_4464368 prefixEnd_4464368 2292366602551494373368751 := by
  unfold tailWord_4464368
  simp only [CollatzResearch.WordTrace]
  refine ⟨81414438945182332098748879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108552585260243109464998505 81414438945182332098748879)
  ·
    refine ⟨122121658417773498148123319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81414438945182332098748879 122121658417773498148123319)
    ·
      refine ⟨183182487626660247222184979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122121658417773498148123319 183182487626660247222184979)
      ·
        refine ⟨274773731439990370833277469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183182487626660247222184979 274773731439990370833277469)
        ·
          refine ⟨103040149289996389062479051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274773731439990370833277469 103040149289996389062479051)
          ·
            refine ⟨154560223934994583593718577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103040149289996389062479051 154560223934994583593718577)
            ·
              refine ⟨115920167951245937695288933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154560223934994583593718577 115920167951245937695288933)
              ·
                refine ⟨21735031490858613317866675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115920167951245937695288933 21735031490858613317866675)
                ·
                  refine ⟨32602547236287919976800013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21735031490858613317866675 32602547236287919976800013)
                  ·
                    refine ⟨12225955213607969991300005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32602547236287919976800013 12225955213607969991300005)
                    ·
                      refine ⟨2292366602551494373368751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12225955213607969991300005 2292366602551494373368751)
                      ·
                        rfl

theorem cell23_4464368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_4464368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464368 prefixEnd_4464368 := by exact prefixLift 4464368
  have htrace : WordTrace (prefixWord ++ tailWord_4464368) baseStart_4464368 baseEnd_4464368 := by
    simpa [prefixWord, tailWord_4464368, baseEnd_4464368] using wordTrace_append hprefix tailTrace_4464368
  have hstable : (prefixWord ++ tailWord_4464368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464368).length < 2 ^ (prefixWord ++ tailWord_4464368).sum := by decide
  have hdescent : baseEnd_4464368 < baseStart_4464368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464385 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_4464385 : Nat := 118140960795 + 4464385 * 2 ^ 59
def prefixEnd_4464385 : Nat := 4983230072969 + 3 ^ 40 * 4464385 * 2
def baseEnd_4464385 : Nat := 2292375331722620806856173

theorem tailTrace_4464385 : CollatzResearch.WordTrace tailWord_4464385 prefixEnd_4464385 2292375331722620806856173 := by
  unfold tailWord_4464385
  simp only [CollatzResearch.WordTrace]
  refine ⟨162829497931303076100866609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108552998620868717400577739 162829497931303076100866609)
  ·
    refine ⟨122122123448477307075649957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162829497931303076100866609 122122123448477307075649957)
    ·
      refine ⟨22897898146589495076684367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122122123448477307075649957 22897898146589495076684367)
      ·
        refine ⟨34346847219884242615026551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22897898146589495076684367 34346847219884242615026551)
        ·
          refine ⟨51520270829826363922539827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34346847219884242615026551 51520270829826363922539827)
          ·
            refine ⟨77280406244739545883809741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51520270829826363922539827 77280406244739545883809741)
            ·
              refine ⟨28980152341777329706428653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77280406244739545883809741 28980152341777329706428653)
              ·
                refine ⟨10867557128166498639910745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28980152341777329706428653 10867557128166498639910745)
                ·
                  refine ⟨8150667846124873979933059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10867557128166498639910745 8150667846124873979933059)
                  ·
                    refine ⟨12226001769187310969899589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8150667846124873979933059 12226001769187310969899589)
                    ·
                      refine ⟨2292375331722620806856173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12226001769187310969899589 2292375331722620806856173)
                      ·
                        rfl

theorem cell23_4464385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_4464385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464385 prefixEnd_4464385 := by exact prefixLift 4464385
  have htrace : WordTrace (prefixWord ++ tailWord_4464385) baseStart_4464385 baseEnd_4464385 := by
    simpa [prefixWord, tailWord_4464385, baseEnd_4464385] using wordTrace_append hprefix tailTrace_4464385
  have hstable : (prefixWord ++ tailWord_4464385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464385).length < 2 ^ (prefixWord ++ tailWord_4464385).sum := by decide
  have hdescent : baseEnd_4464385 < baseStart_4464385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464397 : List Nat := [1, 7, 2, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_4464397 : Nat := 118140960795 + 4464397 * 2 ^ 59
def prefixEnd_4464397 : Nat := 4983230072969 + 3 ^ 40 * 4464397 * 2
def baseEnd_4464397 : Nat := 2292381493490474759906119

theorem tailTrace_4464397 : CollatzResearch.WordTrace tailWord_4464397 prefixEnd_4464397 2292381493490474759906119 := by
  unfold tailWord_4464397
  simp only [CollatzResearch.WordTrace]
  refine ⟨162829935607259602150303445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108553290404839734766868963 162829935607259602150303445)
  ·
    refine ⟨3816326615795146925397737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 162829935607259602150303445 3816326615795146925397737)
    ·
      refine ⟨2862244961846360194048303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3816326615795146925397737 2862244961846360194048303)
      ·
        refine ⟨4293367442769540291072455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2862244961846360194048303 4293367442769540291072455)
        ·
          refine ⟨6440051164154310436608683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4293367442769540291072455 6440051164154310436608683)
          ·
            refine ⟨9660076746231465654913025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6440051164154310436608683 9660076746231465654913025)
            ·
              refine ⟨7245057559673599241184769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9660076746231465654913025 7245057559673599241184769)
              ·
                refine ⟨5433793169755199430888577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7245057559673599241184769 5433793169755199430888577)
                ·
                  refine ⟨4075344877316399573166433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5433793169755199430888577 4075344877316399573166433)
                  ·
                    refine ⟨3056508657987299679874825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4075344877316399573166433 3056508657987299679874825)
                    ·
                      refine ⟨2292381493490474759906119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3056508657987299679874825 2292381493490474759906119)
                      ·
                        rfl

theorem cell23_4464397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_4464397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464397 prefixEnd_4464397 := by exact prefixLift 4464397
  have htrace : WordTrace (prefixWord ++ tailWord_4464397) baseStart_4464397 baseEnd_4464397 := by
    simpa [prefixWord, tailWord_4464397, baseEnd_4464397] using wordTrace_append hprefix tailTrace_4464397
  have hstable : (prefixWord ++ tailWord_4464397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464397).length < 2 ^ (prefixWord ++ tailWord_4464397).sum := by decide
  have hdescent : baseEnd_4464397 < baseStart_4464397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464408 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 8]
def baseStart_4464408 : Nat := 118140960795 + 4464408 * 2 ^ 59
def prefixEnd_4464408 : Nat := 4983230072969 + 3 ^ 40 * 4464408 * 2
def baseEnd_4464408 : Nat := 254709682419741579652063

theorem tailTrace_4464408 : CollatzResearch.WordTrace tailWord_4464408 prefixEnd_4464408 254709682419741579652063 := by
  unfold tailWord_4464408
  simp only [CollatzResearch.WordTrace]
  refine ⟨81415168405109875514476939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108553557873479834019302585 81415168405109875514476939)
  ·
    refine ⟨122122752607664813271715409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81415168405109875514476939 122122752607664813271715409)
    ·
      refine ⟨91592064455748609953786557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122122752607664813271715409 91592064455748609953786557)
      ·
        refine ⟨34347024170905728732669959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91592064455748609953786557 34347024170905728732669959)
        ·
          refine ⟨51520536256358593099004939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34347024170905728732669959 51520536256358593099004939)
          ·
            refine ⟨77280804384537889648507409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51520536256358593099004939 77280804384537889648507409)
            ·
              refine ⟨57960603288403417236380557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77280804384537889648507409 57960603288403417236380557)
              ·
                refine ⟨21735226233151281463642709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57960603288403417236380557 21735226233151281463642709)
                ·
                  refine ⟨254709682419741579652063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21735226233151281463642709 254709682419741579652063)
                  ·
                    rfl

theorem cell23_4464408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 8].length) (baseStart_4464408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464408 prefixEnd_4464408 := by exact prefixLift 4464408
  have htrace : WordTrace (prefixWord ++ tailWord_4464408) baseStart_4464408 baseEnd_4464408 := by
    simpa [prefixWord, tailWord_4464408, baseEnd_4464408] using wordTrace_append hprefix tailTrace_4464408
  have hstable : (prefixWord ++ tailWord_4464408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464408).length < 2 ^ (prefixWord ++ tailWord_4464408).sum := by decide
  have hdescent : baseEnd_4464408 < baseStart_4464408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464446 : List Nat := [4, 2, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_4464446 : Nat := 118140960795 + 4464446 * 2 ^ 59
def prefixEnd_4464446 : Nat := 4983230072969 + 3 ^ 40 * 4464446 * 2
def baseEnd_4464446 : Nat := 764135551347515022731131

theorem tailTrace_4464446 : CollatzResearch.WordTrace tailWord_4464446 prefixEnd_4464446 764135551347515022731131 := by
  unfold tailWord_4464446
  simp only [CollatzResearch.WordTrace]
  refine ⟨20353965348010260439854649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108554481856054722345891461 20353965348010260439854649)
  ·
    refine ⟨15265474011007695329890987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20353965348010260439854649 15265474011007695329890987)
    ·
      refine ⟨22898211016511542994836481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15265474011007695329890987 22898211016511542994836481)
      ·
        refine ⟨17173658262383657246127361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22898211016511542994836481 17173658262383657246127361)
        ·
          refine ⟨12880243696787742934595521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17173658262383657246127361 12880243696787742934595521)
          ·
            refine ⟨9660182772590807200946641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12880243696787742934595521 9660182772590807200946641)
            ·
              refine ⟨7245137079443105400709981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9660182772590807200946641 7245137079443105400709981)
              ·
                refine ⟨2716926404791164525266243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7245137079443105400709981 2716926404791164525266243)
                ·
                  refine ⟨4075389607186746787899365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2716926404791164525266243 4075389607186746787899365)
                  ·
                    refine ⟨764135551347515022731131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4075389607186746787899365 764135551347515022731131)
                    ·
                      rfl

theorem cell23_4464446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_4464446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464446 prefixEnd_4464446 := by exact prefixLift 4464446
  have htrace : WordTrace (prefixWord ++ tailWord_4464446) baseStart_4464446 baseEnd_4464446 := by
    simpa [prefixWord, tailWord_4464446, baseEnd_4464446] using wordTrace_append hprefix tailTrace_4464446
  have hstable : (prefixWord ++ tailWord_4464446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464446).length < 2 ^ (prefixWord ++ tailWord_4464446).sum := by decide
  have hdescent : baseEnd_4464446 < baseStart_4464446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464448 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 5]
def baseStart_4464448 : Nat := 118140960795 + 4464448 * 2 ^ 59
def prefixEnd_4464448 : Nat := 4983230072969 + 3 ^ 40 * 4464448 * 2
def baseEnd_4464448 : Nat := 2292407681003854060368383

theorem tailTrace_4464448 : CollatzResearch.WordTrace tailWord_4464448 prefixEnd_4464448 2292407681003854060368383 := by
  unfold tailWord_4464448
  simp only [CollatzResearch.WordTrace]
  refine ⟨81415897865037418930204999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108554530486716558573606665 81415897865037418930204999)
  ·
    refine ⟨122123846797556128395307499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81415897865037418930204999 122123846797556128395307499)
    ·
      refine ⟨183185770196334192592961249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122123846797556128395307499 183185770196334192592961249)
      ·
        refine ⟨137389327647250644444720937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183185770196334192592961249 137389327647250644444720937)
        ·
          refine ⟨103041995735437983333540703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137389327647250644444720937 103041995735437983333540703)
          ·
            refine ⟨154562993603156975000311055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103041995735437983333540703 154562993603156975000311055)
            ·
              refine ⟨231844490404735462500466583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154562993603156975000311055 231844490404735462500466583)
              ·
                refine ⟨347766735607103193750699875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231844490404735462500466583 347766735607103193750699875)
                ·
                  refine ⟨521650103410654790626049813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 347766735607103193750699875 521650103410654790626049813)
                  ·
                    refine ⟨24452348597374443310596085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 521650103410654790626049813 24452348597374443310596085)
                    ·
                      refine ⟨2292407681003854060368383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24452348597374443310596085 2292407681003854060368383)
                      ·
                        rfl

theorem cell23_4464448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_4464448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464448 prefixEnd_4464448 := by exact prefixLift 4464448
  have htrace : WordTrace (prefixWord ++ tailWord_4464448) baseStart_4464448 baseEnd_4464448 := by
    simpa [prefixWord, tailWord_4464448, baseEnd_4464448] using wordTrace_append hprefix tailTrace_4464448
  have hstable : (prefixWord ++ tailWord_4464448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464448).length < 2 ^ (prefixWord ++ tailWord_4464448).sum := by decide
  have hdescent : baseEnd_4464448 < baseStart_4464448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464469 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 3, 1, 3]
def baseStart_4464469 : Nat := 118140960795 + 4464469 * 2 ^ 59
def prefixEnd_4464469 : Nat := 4983230072969 + 3 ^ 40 * 4464469 * 2
def baseEnd_4464469 : Nat := 2292418464097598478205787

theorem tailTrace_4464469 : CollatzResearch.WordTrace tailWord_4464469 prefixEnd_4464469 2292418464097598478205787 := by
  unfold tailWord_4464469
  simp only [CollatzResearch.WordTrace]
  refine ⟨162832561662998758446924461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108555041108665838964616307 162832561662998758446924461)
  ·
    refine ⟨61062210623624534417596673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162832561662998758446924461 61062210623624534417596673)
    ·
      refine ⟨45796657967718400813197505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61062210623624534417596673 45796657967718400813197505)
      ·
        refine ⟨34347493475788800609898129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45796657967718400813197505 34347493475788800609898129)
        ·
          refine ⟨25760620106841600457423597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34347493475788800609898129 25760620106841600457423597)
          ·
            refine ⟨9660232540065600171533849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25760620106841600457423597 9660232540065600171533849)
            ·
              refine ⟨7245174405049200128650387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9660232540065600171533849 7245174405049200128650387)
              ·
                refine ⟨10867761607573800192975581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7245174405049200128650387 10867761607573800192975581)
                ·
                  refine ⟨4075410602840175072365843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10867761607573800192975581 4075410602840175072365843)
                  ·
                    refine ⟨6113115904260262608548765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4075410602840175072365843 6113115904260262608548765)
                    ·
                      refine ⟨2292418464097598478205787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6113115904260262608548765 2292418464097598478205787)
                      ·
                        rfl

theorem cell23_4464469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_4464469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464469 prefixEnd_4464469 := by exact prefixLift 4464469
  have htrace : WordTrace (prefixWord ++ tailWord_4464469) baseStart_4464469 baseEnd_4464469 := by
    simpa [prefixWord, tailWord_4464469, baseEnd_4464469] using wordTrace_append hprefix tailTrace_4464469
  have hstable : (prefixWord ++ tailWord_4464469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464469).length < 2 ^ (prefixWord ++ tailWord_4464469).sum := by decide
  have hdescent : baseEnd_4464469 < baseStart_4464469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464492 : List Nat := [2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 4]
def baseStart_4464492 : Nat := 118140960795 + 4464492 * 2 ^ 59
def prefixEnd_4464492 : Nat := 4983230072969 + 3 ^ 40 * 4464492 * 2
def baseEnd_4464492 : Nat := 2292430274152651888218181

theorem tailTrace_4464492 : CollatzResearch.WordTrace tailWord_4464492 prefixEnd_4464492 2292430274152651888218181 := by
  unfold tailWord_4464492
  simp only [CollatzResearch.WordTrace]
  refine ⟨81416700270957716687505865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108555600361276955583341153 81416700270957716687505865)
  ·
    refine ⟨61062525203218287515629399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81416700270957716687505865 61062525203218287515629399)
    ·
      refine ⟨91593787804827431273444099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61062525203218287515629399 91593787804827431273444099)
      ·
        refine ⟨137390681707241146910166149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91593787804827431273444099 137390681707241146910166149)
        ·
          refine ⟨25760752820107715045656153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137390681707241146910166149 25760752820107715045656153)
          ·
            refine ⟨19320564615080786284242115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25760752820107715045656153 19320564615080786284242115)
            ·
              refine ⟨28980846922621179426363173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19320564615080786284242115 28980846922621179426363173)
              ·
                refine ⟨5433908797991471142443095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28980846922621179426363173 5433908797991471142443095)
                ·
                  refine ⟨8150863196987206713664643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5433908797991471142443095 8150863196987206713664643)
                  ·
                    refine ⟨12226294795480810070496965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8150863196987206713664643 12226294795480810070496965)
                    ·
                      refine ⟨2292430274152651888218181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12226294795480810070496965 2292430274152651888218181)
                      ·
                        rfl

theorem cell23_4464492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_4464492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464492 prefixEnd_4464492 := by exact prefixLift 4464492
  have htrace : WordTrace (prefixWord ++ tailWord_4464492) baseStart_4464492 baseEnd_4464492 := by
    simpa [prefixWord, tailWord_4464492, baseEnd_4464492] using wordTrace_append hprefix tailTrace_4464492
  have hstable : (prefixWord ++ tailWord_4464492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464492).length < 2 ^ (prefixWord ++ tailWord_4464492).sum := by decide
  have hdescent : baseEnd_4464492 < baseStart_4464492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464505 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 3, 2, 4]
def baseStart_4464505 : Nat := 118140960795 + 4464505 * 2 ^ 59
def prefixEnd_4464505 : Nat := 4983230072969 + 3 ^ 40 * 4464505 * 2
def baseEnd_4464505 : Nat := 2292436949401160337355621

theorem tailTrace_4464505 : CollatzResearch.WordTrace tailWord_4464505 prefixEnd_4464505 2292436949401160337355621 := by
  unfold tailWord_4464505
  simp only [CollatzResearch.WordTrace]
  refine ⟨162833874690868336595234969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108555916460578891063489979 162833874690868336595234969)
  ·
    refine ⟨122125406018151252446426227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162833874690868336595234969 122125406018151252446426227)
    ·
      refine ⟨183188109027226878669639341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122125406018151252446426227 183188109027226878669639341)
      ·
        refine ⟨68695540885210079501114753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183188109027226878669639341 68695540885210079501114753)
        ·
          refine ⟨51521655663907559625836065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68695540885210079501114753 51521655663907559625836065)
          ·
            refine ⟨38641241747930669719377049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51521655663907559625836065 38641241747930669719377049)
            ·
              refine ⟨28980931310948002289532787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38641241747930669719377049 28980931310948002289532787)
              ·
                refine ⟨43471396966422003434299181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28980931310948002289532787 43471396966422003434299181)
                ·
                  refine ⟨16301773862408251287862193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43471396966422003434299181 16301773862408251287862193)
                  ·
                    refine ⟨12226330396806188465896645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16301773862408251287862193 12226330396806188465896645)
                    ·
                      refine ⟨2292436949401160337355621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12226330396806188465896645 2292436949401160337355621)
                      ·
                        rfl

theorem cell23_4464505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_4464505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464505 prefixEnd_4464505 := by exact prefixLift 4464505
  have htrace : WordTrace (prefixWord ++ tailWord_4464505) baseStart_4464505 baseEnd_4464505 := by
    simpa [prefixWord, tailWord_4464505, baseEnd_4464505] using wordTrace_append hprefix tailTrace_4464505
  have hstable : (prefixWord ++ tailWord_4464505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464505).length < 2 ^ (prefixWord ++ tailWord_4464505).sum := by decide
  have hdescent : baseEnd_4464505 < baseStart_4464505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464512 : List Nat := [2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 3]
def baseStart_4464512 : Nat := 118140960795 + 4464512 * 2 ^ 59
def prefixEnd_4464512 : Nat := 4983230072969 + 3 ^ 40 * 4464512 * 2
def baseEnd_4464512 : Nat := 2292440543765741809968089

theorem tailTrace_4464512 : CollatzResearch.WordTrace tailWord_4464512 prefixEnd_4464512 2292440543765741809968089 := by
  unfold tailWord_4464512
  simp only [CollatzResearch.WordTrace]
  refine ⟨81417065000921488395369895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108556086667895317860493193 81417065000921488395369895)
  ·
    refine ⟨122125597501382232593054843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81417065000921488395369895 122125597501382232593054843)
    ·
      refine ⟨183188396252073348889582265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122125597501382232593054843 183188396252073348889582265)
      ·
        refine ⟨137391297189055011667186699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183188396252073348889582265 137391297189055011667186699)
        ·
          refine ⟨206086945783582517500780049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137391297189055011667186699 206086945783582517500780049)
          ·
            refine ⟨154565209337686888125585037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206086945783582517500780049 154565209337686888125585037)
            ·
              refine ⟨57961953501632583047094389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154565209337686888125585037 57961953501632583047094389)
              ·
                refine ⟨5433933140778054660665099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57961953501632583047094389 5433933140778054660665099)
                ·
                  refine ⟨8150899711167081990997649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5433933140778054660665099 8150899711167081990997649)
                  ·
                    refine ⟨6113174783375311493248237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8150899711167081990997649 6113174783375311493248237)
                    ·
                      refine ⟨2292440543765741809968089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6113174783375311493248237 2292440543765741809968089)
                      ·
                        rfl

theorem cell23_4464512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_4464512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464512 prefixEnd_4464512 := by exact prefixLift 4464512
  have htrace : WordTrace (prefixWord ++ tailWord_4464512) baseStart_4464512 baseEnd_4464512 := by
    simpa [prefixWord, tailWord_4464512, baseEnd_4464512] using wordTrace_append hprefix tailTrace_4464512
  have hstable : (prefixWord ++ tailWord_4464512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464512).length < 2 ^ (prefixWord ++ tailWord_4464512).sum := by decide
  have hdescent : baseEnd_4464512 < baseStart_4464512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464515 : List Nat := [1, 1, 1, 3, 4, 4, 9]
def baseStart_4464515 : Nat := 118140960795 + 4464515 * 2 ^ 59
def prefixEnd_4464515 : Nat := 4983230072969 + 3 ^ 40 * 4464515 * 2
def baseEnd_4464515 : Nat := 28301754126021053064575

theorem tailTrace_4464515 : CollatzResearch.WordTrace tailWord_4464515 prefixEnd_4464515 28301754126021053064575 := by
  unfold tailWord_4464515
  simp only [CollatzResearch.WordTrace]
  refine ⟨162834239420832108303098999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108556159613888072202065999 162834239420832108303098999)
  ·
    refine ⟨244251359131248162454648499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162834239420832108303098999 244251359131248162454648499)
    ·
      refine ⟨366377038696872243681972749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244251359131248162454648499 366377038696872243681972749)
      ·
        refine ⟨137391389511327091380739781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 366377038696872243681972749 137391389511327091380739781)
        ·
          refine ⟨25760885533373829633888709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137391389511327091380739781 25760885533373829633888709)
          ·
            refine ⟨4830166037507593056354133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25760885533373829633888709 4830166037507593056354133)
            ·
              refine ⟨28301754126021053064575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4830166037507593056354133 28301754126021053064575)
              ·
                rfl

theorem cell23_4464515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 9].length) (baseStart_4464515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464515 prefixEnd_4464515 := by exact prefixLift 4464515
  have htrace : WordTrace (prefixWord ++ tailWord_4464515) baseStart_4464515 baseEnd_4464515 := by
    simpa [prefixWord, tailWord_4464515, baseEnd_4464515] using wordTrace_append hprefix tailTrace_4464515
  have hstable : (prefixWord ++ tailWord_4464515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464515).length < 2 ^ (prefixWord ++ tailWord_4464515).sum := by decide
  have hdescent : baseEnd_4464515 < baseStart_4464515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464532 : List Nat := [2, 4, 2, 1, 1, 3, 2, 8]
def baseStart_4464532 : Nat := 118140960795 + 4464532 * 2 ^ 59
def prefixEnd_4464532 : Nat := 4983230072969 + 3 ^ 40 * 4464532 * 2
def baseEnd_4464532 : Nat := 84905585680697471545111

theorem tailTrace_4464532 : CollatzResearch.WordTrace tailWord_4464532 prefixEnd_4464532 84905585680697471545111 := by
  unfold tailWord_4464532
  simp only [CollatzResearch.WordTrace]
  refine ⟨81417429730885260103233925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108556572974513680137645233 81417429730885260103233925)
  ·
    refine ⟨15265768074540986269356361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81417429730885260103233925 15265768074540986269356361)
    ·
      refine ⟨11449326055905739702017271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15265768074540986269356361 11449326055905739702017271)
      ·
        refine ⟨17173989083858609553025907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11449326055905739702017271 17173989083858609553025907)
        ·
          refine ⟨25760983625787914329538861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17173989083858609553025907 25760983625787914329538861)
          ·
            refine ⟨9660368859670467873577073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25760983625787914329538861 9660368859670467873577073)
            ·
              refine ⟨7245276644752850905182805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9660368859670467873577073 7245276644752850905182805)
              ·
                refine ⟨84905585680697471545111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7245276644752850905182805 84905585680697471545111)
                ·
                  rfl

theorem cell23_4464532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 8].length) (baseStart_4464532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464532 prefixEnd_4464532 := by exact prefixLift 4464532
  have htrace : WordTrace (prefixWord ++ tailWord_4464532) baseStart_4464532 baseEnd_4464532 := by
    simpa [prefixWord, tailWord_4464532, baseEnd_4464532] using wordTrace_append hprefix tailTrace_4464532
  have hstable : (prefixWord ++ tailWord_4464532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464532).length < 2 ^ (prefixWord ++ tailWord_4464532).sum := by decide
  have hdescent : baseEnd_4464532 < baseStart_4464532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464536 : List Nat := [2, 1, 2, 6, 1, 1, 1, 3, 2, 4]
def baseStart_4464536 : Nat := 118140960795 + 4464536 * 2 ^ 59
def prefixEnd_4464536 : Nat := 4983230072969 + 3 ^ 40 * 4464536 * 2
def baseEnd_4464536 : Nat := 764150955767149905355993

theorem tailTrace_4464536 : CollatzResearch.WordTrace tailWord_4464536 prefixEnd_4464536 764150955767149905355993 := by
  unfold tailWord_4464536
  simp only [CollatzResearch.WordTrace]
  refine ⟨81417502676878014444806731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108556670235837352593075641 81417502676878014444806731)
  ·
    refine ⟨122126254015317021667210097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81417502676878014444806731 122126254015317021667210097)
    ·
      refine ⟨91594690511487766250407573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122126254015317021667210097 91594690511487766250407573)
      ·
        refine ⟨4293501117725989042987855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 91594690511487766250407573 4293501117725989042987855)
        ·
          refine ⟨6440251676588983564481783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4293501117725989042987855 6440251676588983564481783)
          ·
            refine ⟨9660377514883475346722675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6440251676588983564481783 9660377514883475346722675)
            ·
              refine ⟨14490566272325213020084013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9660377514883475346722675 14490566272325213020084013)
              ·
                refine ⟨5433962352121954882531505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14490566272325213020084013 5433962352121954882531505)
                ·
                  refine ⟨4075471764091466161898629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5433962352121954882531505 4075471764091466161898629)
                  ·
                    refine ⟨764150955767149905355993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4075471764091466161898629 764150955767149905355993)
                    ·
                      rfl

theorem cell23_4464536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_4464536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464536 prefixEnd_4464536 := by exact prefixLift 4464536
  have htrace : WordTrace (prefixWord ++ tailWord_4464536) baseStart_4464536 baseEnd_4464536 := by
    simpa [prefixWord, tailWord_4464536, baseEnd_4464536] using wordTrace_append hprefix tailTrace_4464536
  have hstable : (prefixWord ++ tailWord_4464536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464536).length < 2 ^ (prefixWord ++ tailWord_4464536).sum := by decide
  have hdescent : baseEnd_4464536 < baseStart_4464536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464575 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 2, 6]
def baseStart_4464575 : Nat := 118140960795 + 4464575 * 2 ^ 59
def prefixEnd_4464575 : Nat := 4983230072969 + 3 ^ 40 * 4464575 * 2
def baseEnd_4464575 : Nat := 764157631015658354493433

theorem tailTrace_4464575 : CollatzResearch.WordTrace tailWord_4464575 prefixEnd_4464575 764157631015658354493433 := by
  unfold tailWord_4464575
  simp only [CollatzResearch.WordTrace]
  refine ⟨162836427800614738550283179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108557618533743159033522119 162836427800614738550283179)
  ·
    refine ⟨244254641700922107825424769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162836427800614738550283179 244254641700922107825424769)
    ·
      refine ⟨183190981275691580869068577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244254641700922107825424769 183190981275691580869068577)
      ·
        refine ⟨137393235956768685651801433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183190981275691580869068577 137393235956768685651801433)
        ·
          refine ⟨103044926967576514238851075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137393235956768685651801433 103044926967576514238851075)
          ·
            refine ⟨154567390451364771358276613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103044926967576514238851075 154567390451364771358276613)
            ·
              refine ⟨28981385709630894629676865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154567390451364771358276613 28981385709630894629676865)
              ·
                refine ⟨21736039282223170972257649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28981385709630894629676865 21736039282223170972257649)
                ·
                  refine ⟨16302029461667378229193237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21736039282223170972257649 16302029461667378229193237)
                  ·
                    refine ⟨764157631015658354493433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16302029461667378229193237 764157631015658354493433)
                    ·
                      rfl

theorem cell23_4464575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 6].length) (baseStart_4464575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464575 prefixEnd_4464575 := by exact prefixLift 4464575
  have htrace : WordTrace (prefixWord ++ tailWord_4464575) baseStart_4464575 baseEnd_4464575 := by
    simpa [prefixWord, tailWord_4464575, baseEnd_4464575] using wordTrace_append hprefix tailTrace_4464575
  have hstable : (prefixWord ++ tailWord_4464575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464575).length < 2 ^ (prefixWord ++ tailWord_4464575).sum := by decide
  have hdescent : baseEnd_4464575 < baseStart_4464575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464599 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 1, 4, 2]
def baseStart_4464599 : Nat := 118140960795 + 4464599 * 2 ^ 59
def prefixEnd_4464599 : Nat := 4983230072969 + 3 ^ 40 * 4464599 * 2
def baseEnd_4464599 : Nat := 2292485216582682969580189

theorem tailTrace_4464599 : CollatzResearch.WordTrace tailWord_4464599 prefixEnd_4464599 2292485216582682969580189 := by
  unfold tailWord_4464599
  simp only [CollatzResearch.WordTrace]
  refine ⟨162837303152527790649156851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108558202101685193766104567 162837303152527790649156851)
  ·
    refine ⟨244255954728791685973735277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162837303152527790649156851 244255954728791685973735277)
    ·
      refine ⟨91595983023296882240150729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244255954728791685973735277 91595983023296882240150729)
      ·
        refine ⟨68696987267472661680113047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91595983023296882240150729 68696987267472661680113047)
        ·
          refine ⟨103045480901208992520169571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68696987267472661680113047 103045480901208992520169571)
          ·
            refine ⟨154568221351813488780254357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103045480901208992520169571 154568221351813488780254357)
            ·
              refine ⟨7245385375866257286574423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 154568221351813488780254357 7245385375866257286574423)
              ·
                refine ⟨10868078063799385929861635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7245385375866257286574423 10868078063799385929861635)
                ·
                  refine ⟨16302117095699078894792453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10868078063799385929861635 16302117095699078894792453)
                  ·
                    refine ⟨3056646955443577292773585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16302117095699078894792453 3056646955443577292773585)
                    ·
                      refine ⟨2292485216582682969580189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3056646955443577292773585 2292485216582682969580189)
                      ·
                        rfl

theorem cell23_4464599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_4464599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464599 prefixEnd_4464599 := by exact prefixLift 4464599
  have htrace : WordTrace (prefixWord ++ tailWord_4464599) baseStart_4464599 baseEnd_4464599 := by
    simpa [prefixWord, tailWord_4464599, baseEnd_4464599] using wordTrace_append hprefix tailTrace_4464599
  have hstable : (prefixWord ++ tailWord_4464599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464599).length < 2 ^ (prefixWord ++ tailWord_4464599).sum := by decide
  have hdescent : baseEnd_4464599 < baseStart_4464599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464632 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 2, 3, 3]
def baseStart_4464632 : Nat := 118140960795 + 4464632 * 2 ^ 59
def prefixEnd_4464632 : Nat := 4983230072969 + 3 ^ 40 * 4464632 * 2
def baseEnd_4464632 : Nat := 2292502161444281340467537

theorem tailTrace_4464632 : CollatzResearch.WordTrace tailWord_4464632 prefixEnd_4464632 2292502161444281340467537 := by
  unfold tailWord_4464632
  simp only [CollatzResearch.WordTrace]
  refine ⟨81419253380704118642554075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108559004507605491523405433 81419253380704118642554075)
  ·
    refine ⟨122128880071056177963831113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81419253380704118642554075 122128880071056177963831113)
    ·
      refine ⟨91596660053292133472873335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122128880071056177963831113 91596660053292133472873335)
      ·
        refine ⟨137394990079938200209310003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91596660053292133472873335 137394990079938200209310003)
        ·
          refine ⟨206092485119907300313965005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137394990079938200209310003 206092485119907300313965005)
          ·
            refine ⟨77284681919965237617736877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206092485119907300313965005 77284681919965237617736877)
            ·
              refine ⟨28981755719986964106651329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77284681919965237617736877 28981755719986964106651329)
              ·
                refine ⟨21736316789990223079988497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28981755719986964106651329 21736316789990223079988497)
                ·
                  refine ⟨16302237592492667309991373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21736316789990223079988497 16302237592492667309991373)
                  ·
                    refine ⟨6113339097184750241246765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16302237592492667309991373 6113339097184750241246765)
                    ·
                      refine ⟨2292502161444281340467537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6113339097184750241246765 2292502161444281340467537)
                      ·
                        rfl

theorem cell23_4464632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_4464632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464632 prefixEnd_4464632 := by exact prefixLift 4464632
  have htrace : WordTrace (prefixWord ++ tailWord_4464632) baseStart_4464632 baseEnd_4464632 := by
    simpa [prefixWord, tailWord_4464632, baseEnd_4464632] using wordTrace_append hprefix tailTrace_4464632
  have hstable : (prefixWord ++ tailWord_4464632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464632).length < 2 ^ (prefixWord ++ tailWord_4464632).sum := by decide
  have hdescent : baseEnd_4464632 < baseStart_4464632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464633 : List Nat := [1, 2, 1, 3, 1, 6, 1, 2, 2, 2, 2]
def baseStart_4464633 : Nat := 118140960795 + 4464633 * 2 ^ 59
def prefixEnd_4464633 : Nat := 4983230072969 + 3 ^ 40 * 4464633 * 2
def baseEnd_4464633 : Nat := 2292502674924935836555033

theorem tailTrace_4464633 : CollatzResearch.WordTrace tailWord_4464633 prefixEnd_4464633 2292502674924935836555033 := by
  unfold tailWord_4464633
  simp only [CollatzResearch.WordTrace]
  refine ⟨162838543234404614455894553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108559028822936409637263035 162838543234404614455894553)
  ·
    refine ⟨122128907425803460841920915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162838543234404614455894553 122128907425803460841920915)
    ·
      refine ⟨183193361138705191262881373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122128907425803460841920915 183193361138705191262881373)
      ·
        refine ⟨68697510427014446723580515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183193361138705191262881373 68697510427014446723580515)
        ·
          refine ⟨103046265640521670085370773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68697510427014446723580515 103046265640521670085370773)
          ·
            refine ⟨4830293701899453285251755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103046265640521670085370773 4830293701899453285251755)
            ·
              refine ⟨7245440552849179927877633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4830293701899453285251755 7245440552849179927877633)
              ·
                refine ⟨5434080414636884945908225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7245440552849179927877633 5434080414636884945908225)
                ·
                  refine ⟨4075560310977663709431169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5434080414636884945908225 4075560310977663709431169)
                  ·
                    refine ⟨3056670233233247782073377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4075560310977663709431169 3056670233233247782073377)
                    ·
                      refine ⟨2292502674924935836555033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3056670233233247782073377 2292502674924935836555033)
                      ·
                        rfl

theorem cell23_4464633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_4464633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464633 prefixEnd_4464633 := by exact prefixLift 4464633
  have htrace : WordTrace (prefixWord ++ tailWord_4464633) baseStart_4464633 baseEnd_4464633 := by
    simpa [prefixWord, tailWord_4464633, baseEnd_4464633] using wordTrace_append hprefix tailTrace_4464633
  have hstable : (prefixWord ++ tailWord_4464633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464633).length < 2 ^ (prefixWord ++ tailWord_4464633).sum := by decide
  have hdescent : baseEnd_4464633 < baseStart_4464633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464650 : List Nat := [3, 1, 2, 2, 4, 1, 3, 1, 2, 2, 2]
def baseStart_4464650 : Nat := 118140960795 + 4464650 * 2 ^ 59
def prefixEnd_4464650 : Nat := 4983230072969 + 3 ^ 40 * 4464650 * 2
def baseEnd_4464650 : Nat := 2292511404096062270042455

theorem tailTrace_4464650 : CollatzResearch.WordTrace tailWord_4464650 prefixEnd_4464650 2292511404096062270042455 := by
  unfold tailWord_4464650
  simp only [CollatzResearch.WordTrace]
  refine ⟨40709790818835756589815851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108559442183562017572842269 40709790818835756589815851)
  ·
    refine ⟨61064686228253634884723777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40709790818835756589815851 61064686228253634884723777)
    ·
      refine ⟨45798514671190226163542833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61064686228253634884723777 45798514671190226163542833)
      ·
        refine ⟨34348886003392669622657125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45798514671190226163542833 34348886003392669622657125)
        ·
          refine ⟨6440416125636125554248211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34348886003392669622657125 6440416125636125554248211)
          ·
            refine ⟨9660624188454188331372317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6440416125636125554248211 9660624188454188331372317)
            ·
              refine ⟨3622734070670320624264619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9660624188454188331372317 3622734070670320624264619)
              ·
                refine ⟨5434101106005480936396929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3622734070670320624264619 5434101106005480936396929)
                ·
                  refine ⟨4075575829504110702297697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5434101106005480936396929 4075575829504110702297697)
                  ·
                    refine ⟨3056681872128083026723273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4075575829504110702297697 3056681872128083026723273)
                    ·
                      refine ⟨2292511404096062270042455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3056681872128083026723273 2292511404096062270042455)
                      ·
                        rfl

theorem cell23_4464650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_4464650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464650 prefixEnd_4464650 := by exact prefixLift 4464650
  have htrace : WordTrace (prefixWord ++ tailWord_4464650) baseStart_4464650 baseEnd_4464650 := by
    simpa [prefixWord, tailWord_4464650, baseEnd_4464650] using wordTrace_append hprefix tailTrace_4464650
  have hstable : (prefixWord ++ tailWord_4464650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464650).length < 2 ^ (prefixWord ++ tailWord_4464650).sum := by decide
  have hdescent : baseEnd_4464650 < baseStart_4464650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464665 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 1, 10]
def baseStart_4464665 : Nat := 118140960795 + 4464665 * 2 ^ 59
def prefixEnd_4464665 : Nat := 4983230072969 + 3 ^ 40 * 4464665 * 2
def baseEnd_4464665 : Nat := 764173035435293237118295

theorem tailTrace_4464665 : CollatzResearch.WordTrace tailWord_4464665 prefixEnd_4464665 764173035435293237118295 := by
  unfold tailWord_4464665
  simp only [CollatzResearch.WordTrace]
  refine ⟨162839710370288683921059449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108559806913525789280706299 162839710370288683921059449)
  ·
    refine ⟨122129782777716512940794587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162839710370288683921059449 122129782777716512940794587)
    ·
      refine ⟨183194674166574769411191881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122129782777716512940794587 183194674166574769411191881)
      ·
        refine ⟨137396005624931077058393911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183194674166574769411191881 137396005624931077058393911)
        ·
          refine ⟨206094008437396615587590867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137396005624931077058393911 206094008437396615587590867)
          ·
            refine ⟨309141012656094923381386301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206094008437396615587590867 309141012656094923381386301)
            ·
              refine ⟨115927879746035596268019863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 309141012656094923381386301 115927879746035596268019863)
              ·
                refine ⟨173891819619053394402029795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115927879746035596268019863 173891819619053394402029795)
                ·
                  refine ⟨260837729428580091603044693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173891819619053394402029795 260837729428580091603044693)
                  ·
                    refine ⟨764173035435293237118295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 260837729428580091603044693 764173035435293237118295)
                    ·
                      rfl

theorem cell23_4464665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 10].length) (baseStart_4464665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464665 prefixEnd_4464665 := by exact prefixLift 4464665
  have htrace : WordTrace (prefixWord ++ tailWord_4464665) baseStart_4464665 baseEnd_4464665 := by
    simpa [prefixWord, tailWord_4464665, baseEnd_4464665] using wordTrace_append hprefix tailTrace_4464665
  have hstable : (prefixWord ++ tailWord_4464665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464665).length < 2 ^ (prefixWord ++ tailWord_4464665).sum := by decide
  have hdescent : baseEnd_4464665 < baseStart_4464665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464673 : List Nat := [1, 2, 3, 2, 5, 1, 1, 3, 5]
def baseStart_4464673 : Nat := 118140960795 + 4464673 * 2 ^ 59
def prefixEnd_4464673 : Nat := 4983230072969 + 3 ^ 40 * 4464673 * 2
def baseEnd_4464673 : Nat := 254724801572346186672761

theorem tailTrace_4464673 : CollatzResearch.WordTrace tailWord_4464673 prefixEnd_4464673 254724801572346186672761 := by
  unfold tailWord_4464673
  simp only [CollatzResearch.WordTrace]
  refine ⟨162840002154259701287350673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108560001436173134191567115 162840002154259701287350673)
  ·
    refine ⟨122130001615694775965513005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162840002154259701287350673 122130001615694775965513005)
    ·
      refine ⟨45798750605885540987067377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122130001615694775965513005 45798750605885540987067377)
      ·
        refine ⟨34349062954414155740300533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45798750605885540987067377 34349062954414155740300533)
        ·
          refine ⟨3220224651976327100653175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34349062954414155740300533 3220224651976327100653175)
          ·
            refine ⟨4830336977964490650979763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3220224651976327100653175 4830336977964490650979763)
            ·
              refine ⟨7245505466946735976469645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4830336977964490650979763 7245505466946735976469645)
              ·
                refine ⟨2717064550105025991176117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7245505466946735976469645 2717064550105025991176117)
                ·
                  refine ⟨254724801572346186672761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2717064550105025991176117 254724801572346186672761)
                  ·
                    rfl

theorem cell23_4464673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 5].length) (baseStart_4464673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464673 prefixEnd_4464673 := by exact prefixLift 4464673
  have htrace : WordTrace (prefixWord ++ tailWord_4464673) baseStart_4464673 baseEnd_4464673 := by
    simpa [prefixWord, tailWord_4464673, baseEnd_4464673] using wordTrace_append hprefix tailTrace_4464673
  have hstable : (prefixWord ++ tailWord_4464673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464673).length < 2 ^ (prefixWord ++ tailWord_4464673).sum := by decide
  have hdescent : baseEnd_4464673 < baseStart_4464673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464689 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 2, 1, 4]
def baseStart_4464689 : Nat := 118140960795 + 4464689 * 2 ^ 59
def prefixEnd_4464689 : Nat := 4983230072969 + 3 ^ 40 * 4464689 * 2
def baseEnd_4464689 : Nat := 2292531429841587617454775

theorem tailTrace_4464689 : CollatzResearch.WordTrace tailWord_4464689 prefixEnd_4464689 2292531429841587617454775 := by
  unfold tailWord_4464689
  simp only [CollatzResearch.WordTrace]
  refine ⟨162840585722201736019933121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108560390481467824013288747 162840585722201736019933121)
  ·
    refine ⟨122130439291651302014949841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162840585722201736019933121 122130439291651302014949841)
    ·
      refine ⟨91597829468738476511212381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122130439291651302014949841 91597829468738476511212381)
      ·
        refine ⟨34349186050776928691704643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91597829468738476511212381 34349186050776928691704643)
        ·
          refine ⟨51523779076165393037556965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34349186050776928691704643 51523779076165393037556965)
          ·
            refine ⟨9660708576781011194541931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51523779076165393037556965 9660708576781011194541931)
            ·
              refine ⟨14491062865171516791812897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9660708576781011194541931 14491062865171516791812897)
              ·
                refine ⟨10868297148878637593859673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14491062865171516791812897 10868297148878637593859673)
                ·
                  refine ⟨8151222861658978195394755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10868297148878637593859673 8151222861658978195394755)
                  ·
                    refine ⟨12226834292488467293092133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8151222861658978195394755 12226834292488467293092133)
                    ·
                      refine ⟨2292531429841587617454775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12226834292488467293092133 2292531429841587617454775)
                      ·
                        rfl

theorem cell23_4464689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_4464689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464689 prefixEnd_4464689 := by exact prefixLift 4464689
  have htrace : WordTrace (prefixWord ++ tailWord_4464689) baseStart_4464689 baseEnd_4464689 := by
    simpa [prefixWord, tailWord_4464689, baseEnd_4464689] using wordTrace_append hprefix tailTrace_4464689
  have hstable : (prefixWord ++ tailWord_4464689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464689).length < 2 ^ (prefixWord ++ tailWord_4464689).sum := by decide
  have hdescent : baseEnd_4464689 < baseStart_4464689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464746 : List Nat := [3, 1, 3, 2, 3, 1, 2, 2, 6]
def baseStart_4464746 : Nat := 118140960795 + 4464746 * 2 ^ 59
def prefixEnd_4464746 : Nat := 4983230072969 + 3 ^ 40 * 4464746 * 2
def baseEnd_4464746 : Nat := 254728966470988210493557

theorem tailTrace_4464746 : CollatzResearch.WordTrace tailWord_4464746 prefixEnd_4464746 254728966470988210493557 := by
  unfold tailWord_4464746
  simp only [CollatzResearch.WordTrace]
  refine ⟨40710666170748808688689523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108561776455330156503172061 40710666170748808688689523)
  ·
    refine ⟨61065999256123213033034285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40710666170748808688689523 61065999256123213033034285)
    ·
      refine ⟨22899749721046204887387857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61065999256123213033034285 22899749721046204887387857)
      ·
        refine ⟨17174812290784653665540893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22899749721046204887387857 17174812290784653665540893)
        ·
          refine ⟨6440554609044245124577835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17174812290784653665540893 6440554609044245124577835)
          ·
            refine ⟨9660831913566367686866753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6440554609044245124577835 9660831913566367686866753)
            ·
              refine ⟨7245623935174775765150065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9660831913566367686866753 7245623935174775765150065)
              ·
                refine ⟨5434217951381081823862549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7245623935174775765150065 5434217951381081823862549)
                ·
                  refine ⟨254728966470988210493557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5434217951381081823862549 254728966470988210493557)
                  ·
                    rfl

theorem cell23_4464746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 6].length) (baseStart_4464746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464746 prefixEnd_4464746 := by exact prefixLift 4464746
  have htrace : WordTrace (prefixWord ++ tailWord_4464746) baseStart_4464746 baseEnd_4464746 := by
    simpa [prefixWord, tailWord_4464746, baseEnd_4464746] using wordTrace_append hprefix tailTrace_4464746
  have hstable : (prefixWord ++ tailWord_4464746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464746).length < 2 ^ (prefixWord ++ tailWord_4464746).sum := by decide
  have hdescent : baseEnd_4464746 < baseStart_4464746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464789 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 4, 4]
def baseStart_4464789 : Nat := 118140960795 + 4464789 * 2 ^ 59
def prefixEnd_4464789 : Nat := 4983230072969 + 3 ^ 40 * 4464789 * 2
def baseEnd_4464789 : Nat := 764194259302345742068105

theorem tailTrace_4464789 : CollatzResearch.WordTrace tailWord_4464789 prefixEnd_4464789 764194259302345742068105 := by
  unfold tailWord_4464789
  simp only [CollatzResearch.WordTrace]
  refine ⟨162844233021839453098573421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108562822014559635399048947 162844233021839453098573421)
  ·
    refine ⟨61066587383189794911965033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162844233021839453098573421 61066587383189794911965033)
    ·
      refine ⟨45799940537392346183973775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61066587383189794911965033 45799940537392346183973775)
      ·
        refine ⟨68699910806088519275960663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45799940537392346183973775 68699910806088519275960663)
        ·
          refine ⟨103049866209132778913940995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68699910806088519275960663 103049866209132778913940995)
          ·
            refine ⟨154574799313699168370911493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103049866209132778913940995 154574799313699168370911493)
            ·
              refine ⟨28982774871318594069545905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154574799313699168370911493 28982774871318594069545905)
              ·
                refine ⟨21737081153488945552159429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28982774871318594069545905 21737081153488945552159429)
                ·
                  refine ⟨4075702716279177291029893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21737081153488945552159429 4075702716279177291029893)
                  ·
                    refine ⟨764194259302345742068105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4075702716279177291029893 764194259302345742068105)
                    ·
                      rfl

theorem cell23_4464789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_4464789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464789 prefixEnd_4464789 := by exact prefixLift 4464789
  have htrace : WordTrace (prefixWord ++ tailWord_4464789) baseStart_4464789 baseEnd_4464789 := by
    simpa [prefixWord, tailWord_4464789, baseEnd_4464789] using wordTrace_append hprefix tailTrace_4464789
  have hstable : (prefixWord ++ tailWord_4464789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464789).length < 2 ^ (prefixWord ++ tailWord_4464789).sum := by decide
  have hdescent : baseEnd_4464789 < baseStart_4464789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464796 : List Nat := [2, 2, 3, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_4464796 : Nat := 118140960795 + 4464796 * 2 ^ 59
def prefixEnd_4464796 : Nat := 4983230072969 + 3 ^ 40 * 4464796 * 2
def baseEnd_4464796 : Nat := 2292586372271618698816783

theorem tailTrace_4464796 : CollatzResearch.WordTrace tailWord_4464796 prefixEnd_4464796 2292586372271618698816783 := by
  unfold tailWord_4464796
  simp only [CollatzResearch.WordTrace]
  refine ⟨81422244166407046647039121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108562992221876062196052161 81422244166407046647039121)
  ·
    refine ⟨61066683124805284985279341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81422244166407046647039121 61066683124805284985279341)
    ·
      refine ⟨22900006171801981869479753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61066683124805284985279341 22900006171801981869479753)
      ·
        refine ⟨17175004628851486402109815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22900006171801981869479753 17175004628851486402109815)
        ·
          refine ⟨25762506943277229603164723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17175004628851486402109815 25762506943277229603164723)
          ·
            refine ⟨38643760414915844404747085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25762506943277229603164723 38643760414915844404747085)
            ·
              refine ⟨14491410155593441651780157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38643760414915844404747085 14491410155593441651780157)
              ·
                refine ⟨5434278808347540619417559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14491410155593441651780157 5434278808347540619417559)
                ·
                  refine ⟨8151418212521310929126339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5434278808347540619417559 8151418212521310929126339)
                  ·
                    refine ⟨12227127318781966393689509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8151418212521310929126339 12227127318781966393689509)
                    ·
                      refine ⟨2292586372271618698816783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12227127318781966393689509 2292586372271618698816783)
                      ·
                        rfl

theorem cell23_4464796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_4464796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464796 prefixEnd_4464796 := by exact prefixLift 4464796
  have htrace : WordTrace (prefixWord ++ tailWord_4464796) baseStart_4464796 baseEnd_4464796 := by
    simpa [prefixWord, tailWord_4464796, baseEnd_4464796] using wordTrace_append hprefix tailTrace_4464796
  have hstable : (prefixWord ++ tailWord_4464796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464796).length < 2 ^ (prefixWord ++ tailWord_4464796).sum := by decide
  have hdescent : baseEnd_4464796 < baseStart_4464796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464823 : List Nat := [1, 1, 3, 1, 4, 3, 3, 1, 2, 4]
def baseStart_4464823 : Nat := 118140960795 + 4464823 * 2 ^ 59
def prefixEnd_4464823 : Nat := 4983230072969 + 3 ^ 40 * 4464823 * 2
def baseEnd_4464823 : Nat := 764200078749763364393053

theorem tailTrace_4464823 : CollatzResearch.WordTrace tailWord_4464823 prefixEnd_4464823 764200078749763364393053 := by
  unfold tailWord_4464823
  simp only [CollatzResearch.WordTrace]
  refine ⟨162845473103716276905311123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108563648735810851270207415 162845473103716276905311123)
  ·
    refine ⟨244268209655574415357966685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162845473103716276905311123 244268209655574415357966685)
    ·
      refine ⟨91600578620840405759237507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244268209655574415357966685 91600578620840405759237507)
      ·
        refine ⟨137400867931260608638856261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91600578620840405759237507 137400867931260608638856261)
        ·
          refine ⟨25762662737111364119785549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137400867931260608638856261 25762662737111364119785549)
          ·
            refine ⟨9660998526416761544919581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25762662737111364119785549 9660998526416761544919581)
            ·
              refine ⟨3622874447406285579344843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9660998526416761544919581 3622874447406285579344843)
              ·
                refine ⟨5434311671109428369017265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3622874447406285579344843 5434311671109428369017265)
                ·
                  refine ⟨4075733753332071276762949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5434311671109428369017265 4075733753332071276762949)
                  ·
                    refine ⟨764200078749763364393053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4075733753332071276762949 764200078749763364393053)
                    ·
                      rfl

theorem cell23_4464823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 2, 4].length) (baseStart_4464823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464823 prefixEnd_4464823 := by exact prefixLift 4464823
  have htrace : WordTrace (prefixWord ++ tailWord_4464823) baseStart_4464823 baseEnd_4464823 := by
    simpa [prefixWord, tailWord_4464823, baseEnd_4464823] using wordTrace_append hprefix tailTrace_4464823
  have hstable : (prefixWord ++ tailWord_4464823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464823).length < 2 ^ (prefixWord ++ tailWord_4464823).sum := by decide
  have hdescent : baseEnd_4464823 < baseStart_4464823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464836 : List Nat := [2, 3, 3, 1, 2, 1, 4, 7]
def baseStart_4464836 : Nat := 118140960795 + 4464836 * 2 ^ 59
def prefixEnd_4464836 : Nat := 4983230072969 + 3 ^ 40 * 4464836 * 2
def baseEnd_4464836 : Nat := 84911367092511057122837

theorem tailTrace_4464836 : CollatzResearch.WordTrace tailWord_4464836 prefixEnd_4464836 84911367092511057122837 := by
  unfold tailWord_4464836
  simp only [CollatzResearch.WordTrace]
  refine ⟨81422973626334590062767181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108563964835112786750356241 81422973626334590062767181)
  ·
    refine ⟨30533615109875471273537693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81422973626334590062767181 30533615109875471273537693)
    ·
      refine ⟨11450105666203301727576635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30533615109875471273537693 11450105666203301727576635)
      ·
        refine ⟨17175158499304952591364953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11450105666203301727576635 17175158499304952591364953)
        ·
          refine ⟨12881368874478714443523715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17175158499304952591364953 12881368874478714443523715)
          ·
            refine ⟨19322053311718071665285573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12881368874478714443523715 19322053311718071665285573)
            ·
              refine ⟨3622884995947138437241045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19322053311718071665285573 3622884995947138437241045)
              ·
                refine ⟨84911367092511057122837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3622884995947138437241045 84911367092511057122837)
                ·
                  rfl

theorem cell23_4464836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 7].length) (baseStart_4464836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464836 prefixEnd_4464836 := by exact prefixLift 4464836
  have htrace : WordTrace (prefixWord ++ tailWord_4464836) baseStart_4464836 baseEnd_4464836 := by
    simpa [prefixWord, tailWord_4464836, baseEnd_4464836] using wordTrace_append hprefix tailTrace_4464836
  have hstable : (prefixWord ++ tailWord_4464836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464836).length < 2 ^ (prefixWord ++ tailWord_4464836).sum := by decide
  have hdescent : baseEnd_4464836 < baseStart_4464836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464889 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 4, 4, 3]
def baseStart_4464889 : Nat := 118140960795 + 4464889 * 2 ^ 59
def prefixEnd_4464889 : Nat := 4983230072969 + 3 ^ 40 * 4464889 * 2
def baseEnd_4464889 : Nat := 2292634125972486834953855

theorem tailTrace_4464889 : CollatzResearch.WordTrace tailWord_4464889 prefixEnd_4464889 2292634125972486834953855 := by
  unfold tailWord_4464889
  simp only [CollatzResearch.WordTrace]
  refine ⟨162847880321477170177213721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108565253547651446784809147 162847880321477170177213721)
  ·
    refine ⟨122135910241107877632910291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162847880321477170177213721 122135910241107877632910291)
    ·
      refine ⟨183203865361661816449365437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122135910241107877632910291 183203865361661816449365437)
      ·
        refine ⟨68701449510623181168512039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183203865361661816449365437 68701449510623181168512039)
        ·
          refine ⟨103052174265934771752768059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68701449510623181168512039 103052174265934771752768059)
          ·
            refine ⟨154578261398902157629152089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103052174265934771752768059 154578261398902157629152089)
            ·
              refine ⟨115933696049176618221864067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154578261398902157629152089 115933696049176618221864067)
              ·
                refine ⟨173900544073764927332796101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115933696049176618221864067 173900544073764927332796101)
                ·
                  refine ⟨32606352013830923874899269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 173900544073764927332796101 32606352013830923874899269)
                  ·
                    refine ⟨6113691002593298226543613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32606352013830923874899269 6113691002593298226543613)
                    ·
                      refine ⟨2292634125972486834953855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6113691002593298226543613 2292634125972486834953855)
                      ·
                        rfl

theorem cell23_4464889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_4464889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464889 prefixEnd_4464889 := by exact prefixLift 4464889
  have htrace : WordTrace (prefixWord ++ tailWord_4464889) baseStart_4464889 baseEnd_4464889 := by
    simpa [prefixWord, tailWord_4464889, baseEnd_4464889] using wordTrace_append hprefix tailTrace_4464889
  have hstable : (prefixWord ++ tailWord_4464889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464889).length < 2 ^ (prefixWord ++ tailWord_4464889).sum := by decide
  have hdescent : baseEnd_4464889 < baseStart_4464889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464890 : List Nat := [3, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2]
def baseStart_4464890 : Nat := 118140960795 + 4464890 * 2 ^ 59
def prefixEnd_4464890 : Nat := 4983230072969 + 3 ^ 40 * 4464890 * 2
def baseEnd_4464890 : Nat := 2292634639453141331041351

theorem tailTrace_4464890 : CollatzResearch.WordTrace tailWord_4464890 prefixEnd_4464890 2292634639453141331041351 := by
  unfold tailWord_4464890
  simp only [CollatzResearch.WordTrace]
  refine ⟨40711979198618386837000031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108565277862982364898666749 40711979198618386837000031)
  ·
    refine ⟨61067968797927580255500047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40711979198618386837000031 61067968797927580255500047)
    ·
      refine ⟨91601953196891370383250071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61067968797927580255500047 91601953196891370383250071)
      ·
        refine ⟨137402929795337055574875107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91601953196891370383250071 137402929795337055574875107)
        ·
          refine ⟨206104394693005583362312661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137402929795337055574875107 206104394693005583362312661)
          ·
            refine ⟨4830571750617318360054203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 206104394693005583362312661 4830571750617318360054203)
            ·
              refine ⟨7245857625925977540081305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4830571750617318360054203 7245857625925977540081305)
              ·
                refine ⟨5434393219444483155060979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7245857625925977540081305 5434393219444483155060979)
                ·
                  refine ⟨8151589829166724732591469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5434393219444483155060979 8151589829166724732591469)
                  ·
                    refine ⟨3056846185937521774721801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8151589829166724732591469 3056846185937521774721801)
                    ·
                      refine ⟨2292634639453141331041351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3056846185937521774721801 2292634639453141331041351)
                      ·
                        rfl

theorem cell23_4464890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2].length) (baseStart_4464890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464890 prefixEnd_4464890 := by exact prefixLift 4464890
  have htrace : WordTrace (prefixWord ++ tailWord_4464890) baseStart_4464890 baseEnd_4464890 := by
    simpa [prefixWord, tailWord_4464890, baseEnd_4464890] using wordTrace_append hprefix tailTrace_4464890
  have hstable : (prefixWord ++ tailWord_4464890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464890).length < 2 ^ (prefixWord ++ tailWord_4464890).sum := by decide
  have hdescent : baseEnd_4464890 < baseStart_4464890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464920 : List Nat := [2, 1, 2, 3, 1, 2, 4, 2, 2, 2, 2]
def baseStart_4464920 : Nat := 118140960795 + 4464920 * 2 ^ 59
def prefixEnd_4464920 : Nat := 4983230072969 + 3 ^ 40 * 4464920 * 2
def baseEnd_4464920 : Nat := 2292650043872776213666213

theorem tailTrace_4464920 : CollatzResearch.WordTrace tailWord_4464920 prefixEnd_4464920 2292650043872776213666213 := by
  unfold tailWord_4464920
  simp only [CollatzResearch.WordTrace]
  refine ⟨81424505492182431235796107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108566007322909908314394809 81424505492182431235796107)
  ·
    refine ⟨122136758238273646853694161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81424505492182431235796107 122136758238273646853694161)
    ·
      refine ⟨91602568678705235140270621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122136758238273646853694161 91602568678705235140270621)
      ·
        refine ⟨34350963254514463177601483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91602568678705235140270621 34350963254514463177601483)
        ·
          refine ⟨51526444881771694766402225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34350963254514463177601483 51526444881771694766402225)
          ·
            refine ⟨38644833661328771074801669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51526444881771694766402225 38644833661328771074801669)
            ·
              refine ⟨7245906311499144576525313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38644833661328771074801669 7245906311499144576525313)
              ·
                refine ⟨5434429733624358432393985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7245906311499144576525313 5434429733624358432393985)
                ·
                  refine ⟨4075822300218268824295489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5434429733624358432393985 4075822300218268824295489)
                  ·
                    refine ⟨3056866725163701618221617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4075822300218268824295489 3056866725163701618221617)
                    ·
                      refine ⟨2292650043872776213666213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3056866725163701618221617 2292650043872776213666213)
                      ·
                        rfl

theorem cell23_4464920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_4464920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464920 prefixEnd_4464920 := by exact prefixLift 4464920
  have htrace : WordTrace (prefixWord ++ tailWord_4464920) baseStart_4464920 baseEnd_4464920 := by
    simpa [prefixWord, tailWord_4464920, baseEnd_4464920] using wordTrace_append hprefix tailTrace_4464920
  have hstable : (prefixWord ++ tailWord_4464920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464920).length < 2 ^ (prefixWord ++ tailWord_4464920).sum := by decide
  have hdescent : baseEnd_4464920 < baseStart_4464920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4464996 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 3, 4, 3]
def baseStart_4464996 : Nat := 118140960795 + 4464996 * 2 ^ 59
def prefixEnd_4464996 : Nat := 4983230072969 + 3 ^ 40 * 4464996 * 2
def baseEnd_4464996 : Nat := 2292689068402517916315863

theorem tailTrace_4464996 : CollatzResearch.WordTrace tailWord_4464996 prefixEnd_4464996 2292689068402517916315863 := by
  unfold tailWord_4464996
  simp only [CollatzResearch.WordTrace]
  refine ⟨81425891466044763725679421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108567855288059684967572561 81425891466044763725679421)
  ·
    refine ⟨30534709299766786397129783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81425891466044763725679421 30534709299766786397129783)
    ·
      refine ⟨45802063949650179595694675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30534709299766786397129783 45802063949650179595694675)
      ·
        refine ⟨68703095924475269393542013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45802063949650179595694675 68703095924475269393542013)
        ·
          refine ⟨25763660971678226022578255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68703095924475269393542013 25763660971678226022578255)
          ·
            refine ⟨38645491457517339033867383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25763660971678226022578255 38645491457517339033867383)
            ·
              refine ⟨57968237186276008550801075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38645491457517339033867383 57968237186276008550801075)
              ·
                refine ⟨86952355779414012826201613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57968237186276008550801075 86952355779414012826201613)
                ·
                  refine ⟨32607133417280254809825605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86952355779414012826201613 32607133417280254809825605)
                  ·
                    refine ⟨6113837515740047776842301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32607133417280254809825605 6113837515740047776842301)
                    ·
                      refine ⟨2292689068402517916315863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6113837515740047776842301 2292689068402517916315863)
                      ·
                        rfl

theorem cell23_4464996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_4464996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4464996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4464996 prefixEnd_4464996 := by exact prefixLift 4464996
  have htrace : WordTrace (prefixWord ++ tailWord_4464996) baseStart_4464996 baseEnd_4464996 := by
    simpa [prefixWord, tailWord_4464996, baseEnd_4464996] using wordTrace_append hprefix tailTrace_4464996
  have hstable : (prefixWord ++ tailWord_4464996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4464996).length < 2 ^ (prefixWord ++ tailWord_4464996).sum := by decide
  have hdescent : baseEnd_4464996 < baseStart_4464996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4464996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465013 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_4465013 : Nat := 118140960795 + 4465013 * 2 ^ 59
def prefixEnd_4465013 : Nat := 4983230072969 + 3 ^ 40 * 4465013 * 2
def baseEnd_4465013 : Nat := 2292697797573644349803285

theorem tailTrace_4465013 : CollatzResearch.WordTrace tailWord_4465013 prefixEnd_4465013 2292697797573644349803285 := by
  unfold tailWord_4465013
  simp only [CollatzResearch.WordTrace]
  refine ⟨162852402973027939354727693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108568268648685292903151795 162852402973027939354727693)
  ·
    refine ⟨61069651114885477258022885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162852402973027939354727693 61069651114885477258022885)
    ·
      refine ⟨11450559584041026985879291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61069651114885477258022885 11450559584041026985879291)
      ·
        refine ⟨17175839376061540478818937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11450559584041026985879291 17175839376061540478818937)
        ·
          refine ⟨12881879532046155359114203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17175839376061540478818937 12881879532046155359114203)
          ·
            refine ⟨19322819298069233038671305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12881879532046155359114203 19322819298069233038671305)
            ·
              refine ⟨14492114473551924779003479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19322819298069233038671305 14492114473551924779003479)
              ·
                refine ⟨21738171710327887168505219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14492114473551924779003479 21738171710327887168505219)
                ·
                  refine ⟨32607257565491830752757829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21738171710327887168505219 32607257565491830752757829)
                  ·
                    refine ⟨6113860793529718266142093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32607257565491830752757829 6113860793529718266142093)
                    ·
                      refine ⟨2292697797573644349803285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6113860793529718266142093 2292697797573644349803285)
                      ·
                        rfl

theorem cell23_4465013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_4465013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465013 prefixEnd_4465013 := by exact prefixLift 4465013
  have htrace : WordTrace (prefixWord ++ tailWord_4465013) baseStart_4465013 baseEnd_4465013 := by
    simpa [prefixWord, tailWord_4465013, baseEnd_4465013] using wordTrace_append hprefix tailTrace_4465013
  have hstable : (prefixWord ++ tailWord_4465013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465013).length < 2 ^ (prefixWord ++ tailWord_4465013).sum := by decide
  have hdescent : baseEnd_4465013 < baseStart_4465013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465050 : List Nat := [3, 1, 1, 4, 1, 4, 2, 1, 6]
def baseStart_4465050 : Nat := 118140960795 + 4465050 * 2 ^ 59
def prefixEnd_4465050 : Nat := 4983230072969 + 3 ^ 40 * 4465050 * 2
def baseEnd_4465050 : Nat := 254746310706428967226735

theorem tailTrace_4465050 : CollatzResearch.WordTrace tailWord_4465050 prefixEnd_4465050 254746310706428967226735 := by
  unfold tailWord_4465050
  simp only [CollatzResearch.WordTrace]
  refine ⟨40713438118473473668456151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108569168315929263115883069 40713438118473473668456151)
  ·
    refine ⟨61070157177710210502684227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40713438118473473668456151 61070157177710210502684227)
    ·
      refine ⟨91605235766565315754026341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61070157177710210502684227 91605235766565315754026341)
      ·
        refine ⟨17175981706230996703879939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91605235766565315754026341 17175981706230996703879939)
        ·
          refine ⟨25763972559346495055819909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17175981706230996703879939 25763972559346495055819909)
          ·
            refine ⟨4830744854877467822966233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25763972559346495055819909 4830744854877467822966233)
            ·
              refine ⟨3623058641158100867224675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4830744854877467822966233 3623058641158100867224675)
              ·
                refine ⟨5434587961737151300837013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3623058641158100867224675 5434587961737151300837013)
                ·
                  refine ⟨254746310706428967226735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5434587961737151300837013 254746310706428967226735)
                  ·
                    rfl

theorem cell23_4465050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 6].length) (baseStart_4465050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465050 prefixEnd_4465050 := by exact prefixLift 4465050
  have htrace : WordTrace (prefixWord ++ tailWord_4465050) baseStart_4465050 baseEnd_4465050 := by
    simpa [prefixWord, tailWord_4465050, baseEnd_4465050] using wordTrace_append hprefix tailTrace_4465050
  have hstable : (prefixWord ++ tailWord_4465050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465050).length < 2 ^ (prefixWord ++ tailWord_4465050).sum := by decide
  have hdescent : baseEnd_4465050 < baseStart_4465050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465063 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 3, 5]
def baseStart_4465063 : Nat := 118140960795 + 4465063 * 2 ^ 59
def prefixEnd_4465063 : Nat := 4983230072969 + 3 ^ 40 * 4465063 * 2
def baseEnd_4465063 : Nat := 764241157202123051392685

theorem tailTrace_4465063 : CollatzResearch.WordTrace tailWord_4465063 prefixEnd_4465063 764241157202123051392685 := by
  unfold tailWord_4465063
  simp only [CollatzResearch.WordTrace]
  refine ⟨162854226622846797894047843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108569484415231198596031895 162854226622846797894047843)
  ·
    refine ⟨244281339934270196841071765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162854226622846797894047843 244281339934270196841071765)
    ·
      refine ⟨11450687809418915476925239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 244281339934270196841071765 11450687809418915476925239)
      ·
        refine ⟨17176031714128373215387859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11450687809418915476925239 17176031714128373215387859)
        ·
          refine ⟨25764047571192559823081789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17176031714128373215387859 25764047571192559823081789)
          ·
            refine ⟨9661517839197209933655671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25764047571192559823081789 9661517839197209933655671)
            ·
              refine ⟨14492276758795814900483507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9661517839197209933655671 14492276758795814900483507)
              ·
                refine ⟨21738415138193722350725261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14492276758795814900483507 21738415138193722350725261)
                ·
                  refine ⟨8151905676822645881521973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21738415138193722350725261 8151905676822645881521973)
                  ·
                    refine ⟨764241157202123051392685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8151905676822645881521973 764241157202123051392685)
                    ·
                      rfl

theorem cell23_4465063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_4465063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465063 prefixEnd_4465063 := by exact prefixLift 4465063
  have htrace : WordTrace (prefixWord ++ tailWord_4465063) baseStart_4465063 baseEnd_4465063 := by
    simpa [prefixWord, tailWord_4465063, baseEnd_4465063] using wordTrace_append hprefix tailTrace_4465063
  have hstable : (prefixWord ++ tailWord_4465063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465063).length < 2 ^ (prefixWord ++ tailWord_4465063).sum := by decide
  have hdescent : baseEnd_4465063 < baseStart_4465063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465110 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_4465110 : Nat := 118140960795 + 4465110 * 2 ^ 59
def prefixEnd_4465110 : Nat := 4983230072969 + 3 ^ 40 * 4465110 * 2
def baseEnd_4465110 : Nat := 764249201732376823430113

theorem tailTrace_4465110 : CollatzResearch.WordTrace tailWord_4465110 prefixEnd_4465110 764249201732376823430113 := by
  unfold tailWord_4465110
  simp only [CollatzResearch.WordTrace]
  refine ⟨10178496303354782807563049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108570627235784349947339189 10178496303354782807563049)
  ·
    refine ⟨7633872227516087105672287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10178496303354782807563049 7633872227516087105672287)
    ·
      refine ⟨11450808341274130658508431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7633872227516087105672287 11450808341274130658508431)
      ·
        refine ⟨17176212511911195987762647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11450808341274130658508431 17176212511911195987762647)
        ·
          refine ⟨25764318767866793981643971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17176212511911195987762647 25764318767866793981643971)
          ·
            refine ⟨38646478151800190972465957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25764318767866793981643971 38646478151800190972465957)
            ·
              refine ⟨7246214653462535807337367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38646478151800190972465957 7246214653462535807337367)
              ·
                refine ⟨10869321980193803711006051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7246214653462535807337367 10869321980193803711006051)
                ·
                  refine ⟨16303982970290705566509077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10869321980193803711006051 16303982970290705566509077)
                  ·
                    refine ⟨764249201732376823430113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16303982970290705566509077 764249201732376823430113)
                    ·
                      rfl

theorem cell23_4465110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_4465110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465110 prefixEnd_4465110 := by exact prefixLift 4465110
  have htrace : WordTrace (prefixWord ++ tailWord_4465110) baseStart_4465110 baseEnd_4465110 := by
    simpa [prefixWord, tailWord_4465110, baseEnd_4465110] using wordTrace_append hprefix tailTrace_4465110
  have hstable : (prefixWord ++ tailWord_4465110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465110).length < 2 ^ (prefixWord ++ tailWord_4465110).sum := by decide
  have hdescent : baseEnd_4465110 < baseStart_4465110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465113 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 1, 2, 4]
def baseStart_4465113 : Nat := 118140960795 + 4465113 * 2 ^ 59
def prefixEnd_4465113 : Nat := 4983230072969 + 3 ^ 40 * 4465113 * 2
def baseEnd_4465113 : Nat := 2292749145639093958552825

theorem tailTrace_4465113 : CollatzResearch.WordTrace tailWord_4465113 prefixEnd_4465113 2292749145639093958552825 := by
  unfold tailWord_4465113
  simp only [CollatzResearch.WordTrace]
  refine ⟨162856050272665656433367993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108570700181777104288911995 162856050272665656433367993)
  ·
    refine ⟨122142037704499242325025995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162856050272665656433367993 122142037704499242325025995)
    ·
      refine ⟨183213056556748863487538993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122142037704499242325025995 183213056556748863487538993)
      ·
        refine ⟨137409792417561647615654245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183213056556748863487538993 137409792417561647615654245)
        ·
          refine ⟨25764336078292808927935171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137409792417561647615654245 25764336078292808927935171)
          ·
            refine ⟨38646504117439213391902757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25764336078292808927935171 38646504117439213391902757)
            ·
              refine ⟨7246219522019852510981767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38646504117439213391902757 7246219522019852510981767)
              ·
                refine ⟨10869329283029778766472651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7246219522019852510981767 10869329283029778766472651)
                ·
                  refine ⟨16303993924544668149708977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10869329283029778766472651 16303993924544668149708977)
                  ·
                    refine ⟨12227995443408501112281733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16303993924544668149708977 12227995443408501112281733)
                    ·
                      refine ⟨2292749145639093958552825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12227995443408501112281733 2292749145639093958552825)
                      ·
                        rfl

theorem cell23_4465113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_4465113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465113 prefixEnd_4465113 := by exact prefixLift 4465113
  have htrace : WordTrace (prefixWord ++ tailWord_4465113) baseStart_4465113 baseEnd_4465113 := by
    simpa [prefixWord, tailWord_4465113, baseEnd_4465113] using wordTrace_append hprefix tailTrace_4465113
  have hstable : (prefixWord ++ tailWord_4465113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465113).length < 2 ^ (prefixWord ++ tailWord_4465113).sum := by decide
  have hdescent : baseEnd_4465113 < baseStart_4465113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465117 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_4465117 : Nat := 118140960795 + 4465117 * 2 ^ 59
def prefixEnd_4465117 : Nat := 4983230072969 + 3 ^ 40 * 4465117 * 2
def baseEnd_4465117 : Nat := 2292751199561711942902807

theorem tailTrace_4465117 : CollatzResearch.WordTrace tailWord_4465117 prefixEnd_4465117 2292751199561711942902807 := by
  unfold tailWord_4465117
  simp only [CollatzResearch.WordTrace]
  refine ⟨162856196164651165116513605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108570797443100776744342403 162856196164651165116513605)
  ·
    refine ⟨30535536780872093459346301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162856196164651165116513605 30535536780872093459346301)
    ·
      refine ⟨11450826292827035047254863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30535536780872093459346301 11450826292827035047254863)
      ·
        refine ⟨17176239439240552570882295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11450826292827035047254863 17176239439240552570882295)
        ·
          refine ⟨25764359158860828856323443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17176239439240552570882295 25764359158860828856323443)
          ·
            refine ⟨38646538738291243284485165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25764359158860828856323443 38646538738291243284485165)
            ·
              refine ⟨14492452026859216231681937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38646538738291243284485165 14492452026859216231681937)
              ·
                refine ⟨10869339020144412173761453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14492452026859216231681937 10869339020144412173761453)
                ·
                  refine ⟨4076002132554154565160545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10869339020144412173761453 4076002132554154565160545)
                  ·
                    refine ⟨3057001599415615923870409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4076002132554154565160545 3057001599415615923870409)
                    ·
                      refine ⟨2292751199561711942902807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3057001599415615923870409 2292751199561711942902807)
                      ·
                        rfl

theorem cell23_4465117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_4465117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465117 prefixEnd_4465117 := by exact prefixLift 4465117
  have htrace : WordTrace (prefixWord ++ tailWord_4465117) baseStart_4465117 baseEnd_4465117 := by
    simpa [prefixWord, tailWord_4465117, baseEnd_4465117] using wordTrace_append hprefix tailTrace_4465117
  have hstable : (prefixWord ++ tailWord_4465117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465117).length < 2 ^ (prefixWord ++ tailWord_4465117).sum := by decide
  have hdescent : baseEnd_4465117 < baseStart_4465117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465134 : List Nat := [4, 1, 2, 1, 2, 2, 1, 5, 1, 2, 2]
def baseStart_4465134 : Nat := 118140960795 + 4465134 * 2 ^ 59
def prefixEnd_4465134 : Nat := 4983230072969 + 3 ^ 40 * 4465134 * 2
def baseEnd_4465134 : Nat := 2292759928732838376390229

theorem tailTrace_4465134 : CollatzResearch.WordTrace tailWord_4465134 prefixEnd_4465134 2292759928732838376390229 := by
  unfold tailWord_4465134
  simp only [CollatzResearch.WordTrace]
  refine ⟨20357102025698697127485307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108571210803726384679921637 20357102025698697127485307)
  ·
    refine ⟨30535653038548045691227961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20357102025698697127485307 30535653038548045691227961)
    ·
      refine ⟨22901739778911034268420971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30535653038548045691227961 22901739778911034268420971)
      ·
        refine ⟨34352609668366551402631457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22901739778911034268420971 34352609668366551402631457)
        ·
          refine ⟨25764457251274913551973593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34352609668366551402631457 25764457251274913551973593)
          ·
            refine ⟨19323342938456185163980195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25764457251274913551973593 19323342938456185163980195)
            ·
              refine ⟨28985014407684277745970293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19323342938456185163980195 28985014407684277745970293)
              ·
                refine ⟨2717345100720401038684715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28985014407684277745970293 2717345100720401038684715)
                ·
                  refine ⟨4076017651080601558027073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2717345100720401038684715 4076017651080601558027073)
                  ·
                    refine ⟨3057013238310451168520305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4076017651080601558027073 3057013238310451168520305)
                    ·
                      refine ⟨2292759928732838376390229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3057013238310451168520305 2292759928732838376390229)
                      ·
                        rfl

theorem cell23_4465134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_4465134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465134 prefixEnd_4465134 := by exact prefixLift 4465134
  have htrace : WordTrace (prefixWord ++ tailWord_4465134) baseStart_4465134 baseEnd_4465134 := by
    simpa [prefixWord, tailWord_4465134, baseEnd_4465134] using wordTrace_append hprefix tailTrace_4465134
  have hstable : (prefixWord ++ tailWord_4465134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465134).length < 2 ^ (prefixWord ++ tailWord_4465134).sum := by decide
  have hdescent : baseEnd_4465134 < baseStart_4465134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465146 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5]
def baseStart_4465146 : Nat := 118140960795 + 4465146 * 2 ^ 59
def prefixEnd_4465146 : Nat := 4983230072969 + 3 ^ 40 * 4465146 * 2
def baseEnd_4465146 : Nat := 2292766090500692329440173

theorem tailTrace_4465146 : CollatzResearch.WordTrace tailWord_4465146 prefixEnd_4465146 2292766090500692329440173 := by
  unfold tailWord_4465146
  simp only [CollatzResearch.WordTrace]
  refine ⟨40714313470386525767329823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108571502587697402046212861 40714313470386525767329823)
  ·
    refine ⟨61071470205579788650994735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40714313470386525767329823 61071470205579788650994735)
    ·
      refine ⟨91607205308369682976492103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61071470205579788650994735 91607205308369682976492103)
      ·
        refine ⟨137410807962554524464738155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91607205308369682976492103 137410807962554524464738155)
        ·
          refine ⟨206116211943831786697107233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137410807962554524464738155 206116211943831786697107233)
          ·
            refine ⟨154587158957873840022830425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206116211943831786697107233 154587158957873840022830425)
            ·
              refine ⟨115940369218405380017122819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154587158957873840022830425 115940369218405380017122819)
              ·
                refine ⟨173910553827608070025684229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115940369218405380017122819 173910553827608070025684229)
                ·
                  refine ⟨32608228842676513129815793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 173910553827608070025684229 32608228842676513129815793)
                  ·
                    refine ⟨24456171632007384847361845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32608228842676513129815793 24456171632007384847361845)
                    ·
                      refine ⟨2292766090500692329440173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24456171632007384847361845 2292766090500692329440173)
                      ·
                        rfl

theorem cell23_4465146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_4465146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465146 prefixEnd_4465146 := by exact prefixLift 4465146
  have htrace : WordTrace (prefixWord ++ tailWord_4465146) baseStart_4465146 baseEnd_4465146 := by
    simpa [prefixWord, tailWord_4465146, baseEnd_4465146] using wordTrace_append hprefix tailTrace_4465146
  have hstable : (prefixWord ++ tailWord_4465146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465146).length < 2 ^ (prefixWord ++ tailWord_4465146).sum := by decide
  have hdescent : baseEnd_4465146 < baseStart_4465146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465196 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 9]
def baseStart_4465196 : Nat := 118140960795 + 4465196 * 2 ^ 59
def prefixEnd_4465196 : Nat := 4983230072969 + 3 ^ 40 * 4465196 * 2
def baseEnd_4465196 : Nat := 254754640503713014868327

theorem tailTrace_4465196 : CollatzResearch.WordTrace tailWord_4465196 prefixEnd_4465196 254754640503713014868327 := by
  unfold tailWord_4465196
  simp only [CollatzResearch.WordTrace]
  refine ⟨81429538765682480804319721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108572718354243307739092961 81429538765682480804319721)
  ·
    refine ⟨61072154074261860603239791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81429538765682480804319721 61072154074261860603239791)
    ·
      refine ⟨91608231111392790904859687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61072154074261860603239791 91608231111392790904859687)
      ·
        refine ⟨137412346667089186357289531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91608231111392790904859687 137412346667089186357289531)
        ·
          refine ⟨206118520000633779535934297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137412346667089186357289531 206118520000633779535934297)
          ·
            refine ⟨154588890000475334651950723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206118520000633779535934297 154588890000475334651950723)
            ·
              refine ⟨231883335000713001977926085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154588890000475334651950723 231883335000713001977926085)
              ·
                refine ⟨43478125312633687870861141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231883335000713001977926085 43478125312633687870861141)
                ·
                  refine ⟨254754640503713014868327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43478125312633687870861141 254754640503713014868327)
                  ·
                    rfl

theorem cell23_4465196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 9].length) (baseStart_4465196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465196 prefixEnd_4465196 := by exact prefixLift 4465196
  have htrace : WordTrace (prefixWord ++ tailWord_4465196) baseStart_4465196 baseEnd_4465196 := by
    simpa [prefixWord, tailWord_4465196, baseEnd_4465196] using wordTrace_append hprefix tailTrace_4465196
  have hstable : (prefixWord ++ tailWord_4465196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465196).length < 2 ^ (prefixWord ++ tailWord_4465196).sum := by decide
  have hdescent : baseEnd_4465196 < baseStart_4465196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465207 : List Nat := [1, 1, 3, 1, 2, 3, 2, 4, 2, 2, 2]
def baseStart_4465207 : Nat := 118140960795 + 4465207 * 2 ^ 59
def prefixEnd_4465207 : Nat := 4983230072969 + 3 ^ 40 * 4465207 * 2
def baseEnd_4465207 : Nat := 2292797412820616590777393

theorem tailTrace_4465207 : CollatzResearch.WordTrace tailWord_4465207 prefixEnd_4465207 2292797412820616590777393 := by
  unfold tailWord_4465207
  simp only [CollatzResearch.WordTrace]
  refine ⟨162859478734325110487289875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108572985822883406991526583 162859478734325110487289875)
  ·
    refine ⟨244289218101487665730934813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162859478734325110487289875 244289218101487665730934813)
    ·
      refine ⟨91608456788057874649100555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244289218101487665730934813 91608456788057874649100555)
      ·
        refine ⟨137412685182086811973650833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91608456788057874649100555 137412685182086811973650833)
        ·
          refine ⟨103059513886565108980238125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137412685182086811973650833 103059513886565108980238125)
          ·
            refine ⟨38647317707461915867589297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103059513886565108980238125 38647317707461915867589297)
            ·
              refine ⟨28985488280596436900691973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38647317707461915867589297 28985488280596436900691973)
              ·
                refine ⟨5434779052611831918879745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28985488280596436900691973 5434779052611831918879745)
                ·
                  refine ⟨4076084289458873939159809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5434779052611831918879745 4076084289458873939159809)
                  ·
                    refine ⟨3057063217094155454369857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4076084289458873939159809 3057063217094155454369857)
                    ·
                      refine ⟨2292797412820616590777393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3057063217094155454369857 2292797412820616590777393)
                      ·
                        rfl

theorem cell23_4465207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 2, 2].length) (baseStart_4465207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465207 prefixEnd_4465207 := by exact prefixLift 4465207
  have htrace : WordTrace (prefixWord ++ tailWord_4465207) baseStart_4465207 baseEnd_4465207 := by
    simpa [prefixWord, tailWord_4465207, baseEnd_4465207] using wordTrace_append hprefix tailTrace_4465207
  have hstable : (prefixWord ++ tailWord_4465207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465207).length < 2 ^ (prefixWord ++ tailWord_4465207).sum := by decide
  have hdescent : baseEnd_4465207 < baseStart_4465207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465264 : List Nat := [2, 1, 1, 1, 7, 2, 2, 2, 5]
def baseStart_4465264 : Nat := 118140960795 + 4465264 * 2 ^ 59
def prefixEnd_4465264 : Nat := 4983230072969 + 3 ^ 40 * 4465264 * 2
def baseEnd_4465264 : Nat := 254758520135324763084959

theorem tailTrace_4465264 : CollatzResearch.WordTrace tailWord_4465264 prefixEnd_4465264 254758520135324763084959 := by
  unfold tailWord_4465264
  simp only [CollatzResearch.WordTrace]
  refine ⟨81430778847559304611057423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108574371796745739481409897 81430778847559304611057423)
  ·
    refine ⟨122146168271338956916586135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81430778847559304611057423 122146168271338956916586135)
    ·
      refine ⟨183219252407008435374879203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122146168271338956916586135 183219252407008435374879203)
      ·
        refine ⟨274828878610512653062318805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183219252407008435374879203 274828878610512653062318805)
        ·
          refine ⟨6441301842433890306148097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 274828878610512653062318805 6441301842433890306148097)
          ·
            refine ⟨4830976381825417729611073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6441301842433890306148097 4830976381825417729611073)
            ·
              refine ⟨3623232286369063297208305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4830976381825417729611073 3623232286369063297208305)
              ·
                refine ⟨2717424214776797472906229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3623232286369063297208305 2717424214776797472906229)
                ·
                  refine ⟨254758520135324763084959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2717424214776797472906229 254758520135324763084959)
                  ·
                    rfl

theorem cell23_4465264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 5].length) (baseStart_4465264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465264 prefixEnd_4465264 := by exact prefixLift 4465264
  have htrace : WordTrace (prefixWord ++ tailWord_4465264) baseStart_4465264 baseEnd_4465264 := by
    simpa [prefixWord, tailWord_4465264, baseEnd_4465264] using wordTrace_append hprefix tailTrace_4465264
  have hstable : (prefixWord ++ tailWord_4465264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465264).length < 2 ^ (prefixWord ++ tailWord_4465264).sum := by decide
  have hdescent : baseEnd_4465264 < baseStart_4465264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465280 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 1, 6, 2]
def baseStart_4465280 : Nat := 118140960795 + 4465280 * 2 ^ 59
def prefixEnd_4465280 : Nat := 4983230072969 + 3 ^ 40 * 4465280 * 2
def baseEnd_4465280 : Nat := 2292834896908394805164557

theorem tailTrace_4465280 : CollatzResearch.WordTrace tailWord_4465280 prefixEnd_4465280 2292834896908394805164557 := by
  unfold tailWord_4465280
  simp only [CollatzResearch.WordTrace]
  refine ⟨81431070631530321977348647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108574760842040429303131529 81431070631530321977348647)
  ·
    refine ⟨122146605947295482966022971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81431070631530321977348647 122146605947295482966022971)
    ·
      refine ⟨183219908920943224449034457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122146605947295482966022971 183219908920943224449034457)
      ·
        refine ⟨137414931690707418336775843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183219908920943224449034457 137414931690707418336775843)
        ·
          refine ⟨206122397536061127505163765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137414931690707418336775843 206122397536061127505163765)
          ·
            refine ⟨19323974769005730703609103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 206122397536061127505163765 19323974769005730703609103)
            ·
              refine ⟨28985962153508596055413655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19323974769005730703609103 28985962153508596055413655)
              ·
                refine ⟨43478943230262894083120483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28985962153508596055413655 43478943230262894083120483)
                ·
                  refine ⟨65218414845394341124680725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43478943230262894083120483 65218414845394341124680725)
                  ·
                    refine ⟨3057113195877859740219409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65218414845394341124680725 3057113195877859740219409)
                    ·
                      refine ⟨2292834896908394805164557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3057113195877859740219409 2292834896908394805164557)
                      ·
                        rfl

theorem cell23_4465280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 1, 6, 2].length) (baseStart_4465280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465280 prefixEnd_4465280 := by exact prefixLift 4465280
  have htrace : WordTrace (prefixWord ++ tailWord_4465280) baseStart_4465280 baseEnd_4465280 := by
    simpa [prefixWord, tailWord_4465280, baseEnd_4465280] using wordTrace_append hprefix tailTrace_4465280
  have hstable : (prefixWord ++ tailWord_4465280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465280).length < 2 ^ (prefixWord ++ tailWord_4465280).sum := by decide
  have hdescent : baseEnd_4465280 < baseStart_4465280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465303 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 8]
def baseStart_4465303 : Nat := 118140960795 + 4465303 * 2 ^ 59
def prefixEnd_4465303 : Nat := 4983230072969 + 3 ^ 40 * 4465303 * 2
def baseEnd_4465303 : Nat := 254760745218160912797439

theorem tailTrace_4465303 : CollatzResearch.WordTrace tailWord_4465303 prefixEnd_4465303 254760745218160912797439 := by
  unfold tailWord_4465303
  simp only [CollatzResearch.WordTrace]
  refine ⟨162862980141977318882784563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108575320094651545921856375 162862980141977318882784563)
  ·
    refine ⟨244294470212965978324176845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162862980141977318882784563 244294470212965978324176845)
    ·
      refine ⟨91610426329862241871566317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244294470212965978324176845 91610426329862241871566317)
      ·
        refine ⟨34353909873698340701837369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91610426329862241871566317 34353909873698340701837369)
        ·
          refine ⟨25765432405273755526378027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34353909873698340701837369 25765432405273755526378027)
          ·
            refine ⟨38648148607910633289567041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25765432405273755526378027 38648148607910633289567041)
            ·
              refine ⟨28986111455932974967175281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38648148607910633289567041 28986111455932974967175281)
              ·
                refine ⟨21739583591949731225381461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28986111455932974967175281 21739583591949731225381461)
                ·
                  refine ⟨254760745218160912797439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21739583591949731225381461 254760745218160912797439)
                  ·
                    rfl

theorem cell23_4465303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 8].length) (baseStart_4465303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465303 prefixEnd_4465303 := by exact prefixLift 4465303
  have htrace : WordTrace (prefixWord ++ tailWord_4465303) baseStart_4465303 baseEnd_4465303 := by
    simpa [prefixWord, tailWord_4465303, baseEnd_4465303] using wordTrace_append hprefix tailTrace_4465303
  have hstable : (prefixWord ++ tailWord_4465303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465303).length < 2 ^ (prefixWord ++ tailWord_4465303).sum := by decide
  have hdescent : baseEnd_4465303 < baseStart_4465303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465310 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_4465310 : Nat := 118140960795 + 4465310 * 2 ^ 59
def prefixEnd_4465310 : Nat := 4983230072969 + 3 ^ 40 * 4465310 * 2
def baseEnd_4465310 : Nat := 2292850301328029687789419

theorem tailTrace_4465310 : CollatzResearch.WordTrace tailWord_4465310 prefixEnd_4465310 2292850301328029687789419 := by
  unfold tailWord_4465310
  simp only [CollatzResearch.WordTrace]
  refine ⟨20357904431618994884786173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108575490301967972718859589 20357904431618994884786173)
  ·
    refine ⟨7634214161857123081794815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20357904431618994884786173 7634214161857123081794815)
    ·
      refine ⟨11451321242785684622692223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7634214161857123081794815 11451321242785684622692223)
      ·
        refine ⟨17176981864178526934038335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11451321242785684622692223 17176981864178526934038335)
        ·
          refine ⟨25765472796267790401057503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17176981864178526934038335 25765472796267790401057503)
          ·
            refine ⟨38648209194401685601586255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25765472796267790401057503 38648209194401685601586255)
            ·
              refine ⟨57972313791602528402379383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38648209194401685601586255 57972313791602528402379383)
              ·
                refine ⟨86958470687403792603569075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57972313791602528402379383 86958470687403792603569075)
                ·
                  refine ⟨130437706031105688905353613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86958470687403792603569075 130437706031105688905353613)
                  ·
                    refine ⟨48914139761664633339507605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 130437706031105688905353613 48914139761664633339507605)
                    ·
                      refine ⟨2292850301328029687789419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48914139761664633339507605 2292850301328029687789419)
                      ·
                        rfl

theorem cell23_4465310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_4465310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465310 prefixEnd_4465310 := by exact prefixLift 4465310
  have htrace : WordTrace (prefixWord ++ tailWord_4465310) baseStart_4465310 baseEnd_4465310 := by
    simpa [prefixWord, tailWord_4465310, baseEnd_4465310] using wordTrace_append hprefix tailTrace_4465310
  have hstable : (prefixWord ++ tailWord_4465310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465310).length < 2 ^ (prefixWord ++ tailWord_4465310).sum := by decide
  have hdescent : baseEnd_4465310 < baseStart_4465310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465353 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 4, 5, 4]
def baseStart_4465353 : Nat := 118140960795 + 4465353 * 2 ^ 59
def prefixEnd_4465353 : Nat := 4983230072969 + 3 ^ 40 * 4465353 * 2
def baseEnd_4465353 : Nat := 2292872380996173019551721

theorem tailTrace_4465353 : CollatzResearch.WordTrace tailWord_4465353 prefixEnd_4465353 2292872380996173019551721 := by
  unfold tailWord_4465353
  simp only [CollatzResearch.WordTrace]
  refine ⟨162864803791796177422104713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108576535861197451614736475 162864803791796177422104713)
  ·
    refine ⟨122148602843847133066578535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162864803791796177422104713 122148602843847133066578535)
    ·
      refine ⟨183222904265770699599867803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122148602843847133066578535 183222904265770699599867803)
      ·
        refine ⟨274834356398656049399801705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183222904265770699599867803 274834356398656049399801705)
        ·
          refine ⟨206125767298992037049851279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274834356398656049399801705 206125767298992037049851279)
          ·
            refine ⟨309188650948488055574776919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206125767298992037049851279 309188650948488055574776919)
            ·
              refine ⟨463782976422732083362165379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309188650948488055574776919 463782976422732083362165379)
              ·
                refine ⟨695674464634098125043248069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463782976422732083362165379 695674464634098125043248069)
                ·
                  refine ⟨130438962118893398445609013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 695674464634098125043248069 130438962118893398445609013)
                  ·
                    refine ⟨12228652698646256104275845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 130438962118893398445609013 12228652698646256104275845)
                    ·
                      refine ⟨2292872380996173019551721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12228652698646256104275845 2292872380996173019551721)
                      ·
                        rfl

theorem cell23_4465353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_4465353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465353 prefixEnd_4465353 := by exact prefixLift 4465353
  have htrace : WordTrace (prefixWord ++ tailWord_4465353) baseStart_4465353 baseEnd_4465353 := by
    simpa [prefixWord, tailWord_4465353, baseEnd_4465353] using wordTrace_append hprefix tailTrace_4465353
  have hstable : (prefixWord ++ tailWord_4465353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465353).length < 2 ^ (prefixWord ++ tailWord_4465353).sum := by decide
  have hdescent : baseEnd_4465353 < baseStart_4465353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465400 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 1, 2, 4]
def baseStart_4465400 : Nat := 118140960795 + 4465400 * 2 ^ 59
def prefixEnd_4465400 : Nat := 4983230072969 + 3 ^ 40 * 4465400 * 2
def baseEnd_4465400 : Nat := 2292896514586934335664005

theorem tailTrace_4465400 : CollatzResearch.WordTrace tailWord_4465400 prefixEnd_4465400 2292896514586934335664005 := by
  unfold tailWord_4465400
  simp only [CollatzResearch.WordTrace]
  refine ⟨81433259011312952224532827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108577678681750602966043769 81433259011312952224532827)
  ·
    refine ⟨122149888516969428336799241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81433259011312952224532827 122149888516969428336799241)
    ·
      refine ⟨91612416387727071252599431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122149888516969428336799241 91612416387727071252599431)
      ·
        refine ⟨137418624581590606878899147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91612416387727071252599431 137418624581590606878899147)
        ·
          refine ⟨206127936872385910318348721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137418624581590606878899147 206127936872385910318348721)
          ·
            refine ⟨154595952654289432738761541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206127936872385910318348721 154595952654289432738761541)
            ·
              refine ⟨28986741122679268638517789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154595952654289432738761541 28986741122679268638517789)
              ·
                refine ⟨10870027921004725739444171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28986741122679268638517789 10870027921004725739444171)
                ·
                  refine ⟨16305041881507088609166257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10870027921004725739444171 16305041881507088609166257)
                  ·
                    refine ⟨12228781411130316456874693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16305041881507088609166257 12228781411130316456874693)
                    ·
                      refine ⟨2292896514586934335664005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12228781411130316456874693 2292896514586934335664005)
                      ·
                        rfl

theorem cell23_4465400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_4465400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465400 prefixEnd_4465400 := by exact prefixLift 4465400
  have htrace : WordTrace (prefixWord ++ tailWord_4465400) baseStart_4465400 baseEnd_4465400 := by
    simpa [prefixWord, tailWord_4465400, baseEnd_4465400] using wordTrace_append hprefix tailTrace_4465400
  have hstable : (prefixWord ++ tailWord_4465400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465400).length < 2 ^ (prefixWord ++ tailWord_4465400).sum := by decide
  have hdescent : baseEnd_4465400 < baseStart_4465400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465404 : List Nat := [2, 2, 2, 1, 3, 4, 1, 2, 1, 1, 4]
def baseStart_4465404 : Nat := 118140960795 + 4465404 * 2 ^ 59
def prefixEnd_4465404 : Nat := 4983230072969 + 3 ^ 40 * 4465404 * 2
def baseEnd_4465404 : Nat := 2292898568509552320013987

theorem tailTrace_4465404 : CollatzResearch.WordTrace tailWord_4465404 prefixEnd_4465404 2292898568509552320013987 := by
  unfold tailWord_4465404
  simp only [CollatzResearch.WordTrace]
  refine ⟨81433331957305706566105633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108577775943074275421474177 81433331957305706566105633)
  ·
    refine ⟨61074998967979279924579225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81433331957305706566105633 61074998967979279924579225)
    ·
      refine ⟨45806249225984459943434419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61074998967979279924579225 45806249225984459943434419)
      ·
        refine ⟨68709373838976689915151629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45806249225984459943434419 68709373838976689915151629)
        ·
          refine ⟨25766015189616258718181861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68709373838976689915151629 25766015189616258718181861)
          ·
            refine ⟨4831127848053048509659099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25766015189616258718181861 4831127848053048509659099)
            ·
              refine ⟨7246691772079572764488649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4831127848053048509659099 7246691772079572764488649)
              ·
                refine ⟨5435018829059679573366487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7246691772079572764488649 5435018829059679573366487)
                ·
                  refine ⟨8152528243589519360049731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5435018829059679573366487 8152528243589519360049731)
                  ·
                    refine ⟨12228792365384279040074597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8152528243589519360049731 12228792365384279040074597)
                    ·
                      refine ⟨2292898568509552320013987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12228792365384279040074597 2292898568509552320013987)
                      ·
                        rfl

theorem cell23_4465404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_4465404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465404 prefixEnd_4465404 := by exact prefixLift 4465404
  have htrace : WordTrace (prefixWord ++ tailWord_4465404) baseStart_4465404 baseEnd_4465404 := by
    simpa [prefixWord, tailWord_4465404, baseEnd_4465404] using wordTrace_append hprefix tailTrace_4465404
  have hstable : (prefixWord ++ tailWord_4465404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465404).length < 2 ^ (prefixWord ++ tailWord_4465404).sum := by decide
  have hdescent : baseEnd_4465404 < baseStart_4465404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465440 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 2, 7]
def baseStart_4465440 : Nat := 118140960795 + 4465440 * 2 ^ 59
def prefixEnd_4465440 : Nat := 4983230072969 + 3 ^ 40 * 4465440 * 2
def baseEnd_4465440 : Nat := 764305684604371393054607

theorem tailTrace_4465440 : CollatzResearch.WordTrace tailWord_4465440 prefixEnd_4465440 764305684604371393054607 := by
  unfold tailWord_4465440
  simp only [CollatzResearch.WordTrace]
  refine ⟨81433988471240495640260887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108578651294987327520347849 81433988471240495640260887)
  ·
    refine ⟨122150982706860743460391331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81433988471240495640260887 122150982706860743460391331)
    ·
      refine ⟨183226474060291115190586997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122150982706860743460391331 183226474060291115190586997)
      ·
        refine ⟨17177481943152292049117531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 183226474060291115190586997 17177481943152292049117531)
        ·
          refine ⟨25766222914728438073676297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17177481943152292049117531 25766222914728438073676297)
          ·
            refine ⟨19324667186046328555257223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25766222914728438073676297 19324667186046328555257223)
            ·
              refine ⟨28987000779069492832885835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19324667186046328555257223 28987000779069492832885835)
              ·
                refine ⟨43480501168604239249328753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28987000779069492832885835 43480501168604239249328753)
                ·
                  refine ⟨32610375876453179436996565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43480501168604239249328753 32610375876453179436996565)
                  ·
                    refine ⟨764305684604371393054607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32610375876453179436996565 764305684604371393054607)
                    ·
                      rfl

theorem cell23_4465440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 2, 7].length) (baseStart_4465440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465440 prefixEnd_4465440 := by exact prefixLift 4465440
  have htrace : WordTrace (prefixWord ++ tailWord_4465440) baseStart_4465440 baseEnd_4465440 := by
    simpa [prefixWord, tailWord_4465440, baseEnd_4465440] using wordTrace_append hprefix tailTrace_4465440
  have hstable : (prefixWord ++ tailWord_4465440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465440).length < 2 ^ (prefixWord ++ tailWord_4465440).sum := by decide
  have hdescent : baseEnd_4465440 < baseStart_4465440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465444 : List Nat := [2, 3, 1, 3, 4, 1, 1, 8]
def baseStart_4465444 : Nat := 118140960795 + 4465444 * 2 ^ 59
def prefixEnd_4465444 : Nat := 4983230072969 + 3 ^ 40 * 4465444 * 2
def baseEnd_4465444 : Nat := 84922929916138228278289

theorem tailTrace_4465444 : CollatzResearch.WordTrace tailWord_4465444 prefixEnd_4465444 84922929916138228278289 := by
  unfold tailWord_4465444
  simp only [CollatzResearch.WordTrace]
  refine ⟨81434061417233249981833693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108578748556310999975778257 81434061417233249981833693)
  ·
    refine ⟨30537773031462468743187635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81434061417233249981833693 30537773031462468743187635)
    ·
      refine ⟨45806659547193703114781453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30537773031462468743187635 45806659547193703114781453)
      ·
        refine ⟨17177497330197638668043045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45806659547193703114781453 17177497330197638668043045)
        ·
          refine ⟨3220780749412057250258071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17177497330197638668043045 3220780749412057250258071)
          ·
            refine ⟨4831171124118085875387107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3220780749412057250258071 4831171124118085875387107)
            ·
              refine ⟨7246756686177128813080661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4831171124118085875387107 7246756686177128813080661)
              ·
                refine ⟨84922929916138228278289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7246756686177128813080661 84922929916138228278289)
                ·
                  rfl

theorem cell23_4465444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 8].length) (baseStart_4465444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465444 prefixEnd_4465444 := by exact prefixLift 4465444
  have htrace : WordTrace (prefixWord ++ tailWord_4465444) baseStart_4465444 baseEnd_4465444 := by
    simpa [prefixWord, tailWord_4465444, baseEnd_4465444] using wordTrace_append hprefix tailTrace_4465444
  have hstable : (prefixWord ++ tailWord_4465444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465444).length < 2 ^ (prefixWord ++ tailWord_4465444).sum := by decide
  have hdescent : baseEnd_4465444 < baseStart_4465444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465454 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_4465454 : Nat := 118140960795 + 4465454 * 2 ^ 59
def prefixEnd_4465454 : Nat := 4983230072969 + 3 ^ 40 * 4465454 * 2
def baseEnd_4465454 : Nat := 2292924242542277124388757

theorem tailTrace_4465454 : CollatzResearch.WordTrace tailWord_4465454 prefixEnd_4465454 2292924242542277124388757 := by
  unfold tailWord_4465454
  simp only [CollatzResearch.WordTrace]
  refine ⟨20358560945553783958941427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108578991709620181114354277 20358560945553783958941427)
  ·
    refine ⟨30537841418330675938412141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20358560945553783958941427 30537841418330675938412141)
    ·
      refine ⟨11451690531874003476904553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30537841418330675938412141 11451690531874003476904553)
      ·
        refine ⟨8588767898905502607678415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11451690531874003476904553 8588767898905502607678415)
        ·
          refine ⟨12883151848358253911517623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8588767898905502607678415 12883151848358253911517623)
          ·
            refine ⟨19324727772537380867276435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12883151848358253911517623 19324727772537380867276435)
            ·
              refine ⟨28987091658806071300914653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19324727772537380867276435 28987091658806071300914653)
              ·
                refine ⟨10870159372052276737842995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28987091658806071300914653 10870159372052276737842995)
                ·
                  refine ⟨16305239058078415106764493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10870159372052276737842995 16305239058078415106764493)
                  ·
                    refine ⟨6114464646779405665036685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16305239058078415106764493 6114464646779405665036685)
                    ·
                      refine ⟨2292924242542277124388757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6114464646779405665036685 2292924242542277124388757)
                      ·
                        rfl

theorem cell23_4465454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_4465454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465454 prefixEnd_4465454 := by exact prefixLift 4465454
  have htrace : WordTrace (prefixWord ++ tailWord_4465454) baseStart_4465454 baseEnd_4465454 := by
    simpa [prefixWord, tailWord_4465454, baseEnd_4465454] using wordTrace_append hprefix tailTrace_4465454
  have hstable : (prefixWord ++ tailWord_4465454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465454).length < 2 ^ (prefixWord ++ tailWord_4465454).sum := by decide
  have hdescent : baseEnd_4465454 < baseStart_4465454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465464 : List Nat := [2, 1, 2, 1, 3, 2, 2, 4, 1, 3, 2]
def baseStart_4465464 : Nat := 118140960795 + 4465464 * 2 ^ 59
def prefixEnd_4465464 : Nat := 4983230072969 + 3 ^ 40 * 4465464 * 2
def baseEnd_4465464 : Nat := 2292929377348822085263711

theorem tailTrace_4465464 : CollatzResearch.WordTrace tailWord_4465464 prefixEnd_4465464 2292929377348822085263711 := by
  unfold tailWord_4465464
  simp only [CollatzResearch.WordTrace]
  refine ⟨81434426147197021689697723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108579234862929362252930297 81434426147197021689697723)
  ·
    refine ⟨122151639220795532534546585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81434426147197021689697723 122151639220795532534546585)
    ·
      refine ⟨91613729415596649400909939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122151639220795532534546585 91613729415596649400909939)
      ·
        refine ⟨137420594123394974101364909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91613729415596649400909939 137420594123394974101364909)
        ·
          refine ⟨51532722796273115288011841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137420594123394974101364909 51532722796273115288011841)
          ·
            refine ⟨38649542097204836466008881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51532722796273115288011841 38649542097204836466008881)
            ·
              refine ⟨28987156572903627349506661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38649542097204836466008881 28987156572903627349506661)
              ·
                refine ⟨5435091857419430128032499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28987156572903627349506661 5435091857419430128032499)
                ·
                  refine ⟨8152637786129145192048749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5435091857419430128032499 8152637786129145192048749)
                  ·
                    refine ⟨3057239169798429447018281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8152637786129145192048749 3057239169798429447018281)
                    ·
                      refine ⟨2292929377348822085263711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3057239169798429447018281 2292929377348822085263711)
                      ·
                        rfl

theorem cell23_4465464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 1, 3, 2].length) (baseStart_4465464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465464 prefixEnd_4465464 := by exact prefixLift 4465464
  have htrace : WordTrace (prefixWord ++ tailWord_4465464) baseStart_4465464 baseEnd_4465464 := by
    simpa [prefixWord, tailWord_4465464, baseEnd_4465464] using wordTrace_append hprefix tailTrace_4465464
  have hstable : (prefixWord ++ tailWord_4465464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465464).length < 2 ^ (prefixWord ++ tailWord_4465464).sum := by decide
  have hdescent : baseEnd_4465464 < baseStart_4465464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465477 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 3, 4, 2]
def baseStart_4465477 : Nat := 118140960795 + 4465477 * 2 ^ 59
def prefixEnd_4465477 : Nat := 4983230072969 + 3 ^ 40 * 4465477 * 2
def baseEnd_4465477 : Nat := 2292936052597330534401151

theorem tailTrace_4465477 : CollatzResearch.WordTrace tailWord_4465477 prefixEnd_4465477 2292936052597330534401151 := by
  unfold tailWord_4465477
  simp only [CollatzResearch.WordTrace]
  refine ⟨162869326443346946599618685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108579550962231297733079123 162869326443346946599618685)
  ·
    refine ⟨61075997416255104974857007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162869326443346946599618685 61075997416255104974857007)
    ·
      refine ⟨91613996124382657462285511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61075997416255104974857007 91613996124382657462285511)
      ·
        refine ⟨137420994186573986193428267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91613996124382657462285511 137420994186573986193428267)
        ·
          refine ⟨206131491279860979290142401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137420994186573986193428267 206131491279860979290142401)
          ·
            refine ⟨154598618459895734467606801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206131491279860979290142401 154598618459895734467606801)
            ·
              refine ⟨115948963844921800850705101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154598618459895734467606801 115948963844921800850705101)
              ·
                refine ⟨43480861441845675319014413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115948963844921800850705101 43480861441845675319014413)
                ·
                  refine ⟨16305323040692128244630405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43480861441845675319014413 16305323040692128244630405)
                  ·
                    refine ⟨3057248070129774045868201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16305323040692128244630405 3057248070129774045868201)
                    ·
                      refine ⟨2292936052597330534401151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3057248070129774045868201 2292936052597330534401151)
                      ·
                        rfl

theorem cell23_4465477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 4, 2].length) (baseStart_4465477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465477 prefixEnd_4465477 := by exact prefixLift 4465477
  have htrace : WordTrace (prefixWord ++ tailWord_4465477) baseStart_4465477 baseEnd_4465477 := by
    simpa [prefixWord, tailWord_4465477, baseEnd_4465477] using wordTrace_append hprefix tailTrace_4465477
  have hstable : (prefixWord ++ tailWord_4465477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465477).length < 2 ^ (prefixWord ++ tailWord_4465477).sum := by decide
  have hdescent : baseEnd_4465477 < baseStart_4465477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465480 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_4465480 : Nat := 118140960795 + 4465480 * 2 ^ 59
def prefixEnd_4465480 : Nat := 4983230072969 + 3 ^ 40 * 4465480 * 2
def baseEnd_4465480 : Nat := 2292937593039294022663637

theorem tailTrace_4465480 : CollatzResearch.WordTrace tailWord_4465480 prefixEnd_4465480 2292937593039294022663637 := by
  unfold tailWord_4465480
  simp only [CollatzResearch.WordTrace]
  refine ⟨81434717931168039055988947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108579623908224052074651929 81434717931168039055988947)
  ·
    refine ⟨122152076896752058583983421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81434717931168039055988947 122152076896752058583983421)
    ·
      refine ⟨45807028836282021968993783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122152076896752058583983421 45807028836282021968993783)
      ·
        refine ⟨68710543254423032953490675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45807028836282021968993783 68710543254423032953490675)
        ·
          refine ⟨103065814881634549430236013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68710543254423032953490675 103065814881634549430236013)
          ·
            refine ⟨38649680580612956036338505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103065814881634549430236013 38649680580612956036338505)
            ·
              refine ⟨28987260435459717027253879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38649680580612956036338505 28987260435459717027253879)
              ·
                refine ⟨43480890653189575540880819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28987260435459717027253879 43480890653189575540880819)
                ·
                  refine ⟨65221335979784363311321229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43480890653189575540880819 65221335979784363311321229)
                  ·
                    refine ⟨24458000992419136241745461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65221335979784363311321229 24458000992419136241745461)
                    ·
                      refine ⟨2292937593039294022663637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24458000992419136241745461 2292937593039294022663637)
                      ·
                        rfl

theorem cell23_4465480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_4465480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465480 prefixEnd_4465480 := by exact prefixLift 4465480
  have htrace : WordTrace (prefixWord ++ tailWord_4465480) baseStart_4465480 baseEnd_4465480 := by
    simpa [prefixWord, tailWord_4465480, baseEnd_4465480] using wordTrace_append hprefix tailTrace_4465480
  have hstable : (prefixWord ++ tailWord_4465480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465480).length < 2 ^ (prefixWord ++ tailWord_4465480).sum := by decide
  have hdescent : baseEnd_4465480 < baseStart_4465480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465481 : List Nat := [1, 2, 1, 1, 2, 5, 4, 1, 1, 3, 2]
def baseStart_4465481 : Nat := 118140960795 + 4465481 * 2 ^ 59
def prefixEnd_4465481 : Nat := 4983230072969 + 3 ^ 40 * 4465481 * 2
def baseEnd_4465481 : Nat := 2292938106519948518751133

theorem tailTrace_4465481 : CollatzResearch.WordTrace tailWord_4465481 prefixEnd_4465481 2292938106519948518751133 := by
  unfold tailWord_4465481
  simp only [CollatzResearch.WordTrace]
  refine ⟨162869472335332455282764297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108579648223554970188509531 162869472335332455282764297)
  ·
    refine ⟨122152104251499341462073223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162869472335332455282764297 122152104251499341462073223)
    ·
      refine ⟨183228156377249012193109835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122152104251499341462073223 183228156377249012193109835)
      ·
        refine ⟨274842234565873518289664753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183228156377249012193109835 274842234565873518289664753)
        ·
          refine ⟨206131675924405138717248565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274842234565873518289664753 206131675924405138717248565)
          ·
            refine ⟨19324844617912981754742053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 206131675924405138717248565 19324844617912981754742053)
            ·
              refine ⟨3623408365858684079014135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19324844617912981754742053 3623408365858684079014135)
              ·
                refine ⟨5435112548788026118521203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3623408365858684079014135 5435112548788026118521203)
                ·
                  refine ⟨8152668823182039177781805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5435112548788026118521203 8152668823182039177781805)
                  ·
                    refine ⟨3057250808693264691668177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8152668823182039177781805 3057250808693264691668177)
                    ·
                      refine ⟨2292938106519948518751133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3057250808693264691668177 2292938106519948518751133)
                      ·
                        rfl

theorem cell23_4465481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 1, 3, 2].length) (baseStart_4465481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465481 prefixEnd_4465481 := by exact prefixLift 4465481
  have htrace : WordTrace (prefixWord ++ tailWord_4465481) baseStart_4465481 baseEnd_4465481 := by
    simpa [prefixWord, tailWord_4465481, baseEnd_4465481] using wordTrace_append hprefix tailTrace_4465481
  have hstable : (prefixWord ++ tailWord_4465481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465481).length < 2 ^ (prefixWord ++ tailWord_4465481).sum := by decide
  have hdescent : baseEnd_4465481 < baseStart_4465481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465507 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 4]
def baseStart_4465507 : Nat := 118140960795 + 4465507 * 2 ^ 59
def prefixEnd_4465507 : Nat := 4983230072969 + 3 ^ 40 * 4465507 * 2
def baseEnd_4465507 : Nat := 2292951457016965417026013

theorem tailTrace_4465507 : CollatzResearch.WordTrace tailWord_4465507 prefixEnd_4465507 2292951457016965417026013 := by
  unfold tailWord_4465507
  simp only [CollatzResearch.WordTrace]
  refine ⟨162870420633238261723210775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108580280422158841148807183 162870420633238261723210775)
  ·
    refine ⟨244305630949857392584816163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162870420633238261723210775 244305630949857392584816163)
    ·
      refine ⟨366458446424786088877224245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244305630949857392584816163 366458446424786088877224245)
      ·
        refine ⟨34355479352323695832239773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 366458446424786088877224245 34355479352323695832239773)
        ·
          refine ⟨12883304757121385937089915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34355479352323695832239773 12883304757121385937089915)
          ·
            refine ⟨19324957135682078905634873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12883304757121385937089915 19324957135682078905634873)
            ·
              refine ⟨14493717851761559179226155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19324957135682078905634873 14493717851761559179226155)
              ·
                refine ⟨21740576777642338768839233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14493717851761559179226155 21740576777642338768839233)
                ·
                  refine ⟨16305432583231754076629425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21740576777642338768839233 16305432583231754076629425)
                  ·
                    refine ⟨12229074437423815557472069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16305432583231754076629425 12229074437423815557472069)
                    ·
                      refine ⟨2292951457016965417026013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12229074437423815557472069 2292951457016965417026013)
                      ·
                        rfl

theorem cell23_4465507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_4465507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465507 prefixEnd_4465507 := by exact prefixLift 4465507
  have htrace : WordTrace (prefixWord ++ tailWord_4465507) baseStart_4465507 baseEnd_4465507 := by
    simpa [prefixWord, tailWord_4465507, baseEnd_4465507] using wordTrace_append hprefix tailTrace_4465507
  have hstable : (prefixWord ++ tailWord_4465507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465507).length < 2 ^ (prefixWord ++ tailWord_4465507).sum := by decide
  have hdescent : baseEnd_4465507 < baseStart_4465507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465511 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 1, 4, 2]
def baseStart_4465511 : Nat := 118140960795 + 4465511 * 2 ^ 59
def prefixEnd_4465511 : Nat := 4983230072969 + 3 ^ 40 * 4465511 * 2
def baseEnd_4465511 : Nat := 2292953510939583401375995

theorem tailTrace_4465511 : CollatzResearch.WordTrace tailWord_4465511 prefixEnd_4465511 2292953510939583401375995 := by
  unfold tailWord_4465511
  simp only [CollatzResearch.WordTrace]
  refine ⟨162870566525223770406356387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108580377683482513604237591 162870566525223770406356387)
  ·
    refine ⟨244305849787835655609534581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162870566525223770406356387 244305849787835655609534581)
    ·
      refine ⟨22903673417609592713393867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 244305849787835655609534581 22903673417609592713393867)
      ·
        refine ⟨34355510126414389070090801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22903673417609592713393867 34355510126414389070090801)
        ·
          refine ⟨25766632594810791802568101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34355510126414389070090801 25766632594810791802568101)
          ·
            refine ⟨4831243611527023462981519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25766632594810791802568101 4831243611527023462981519)
            ·
              refine ⟨7246865417290535194472279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4831243611527023462981519 7246865417290535194472279)
              ·
                refine ⟨10870298125935802791708419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7246865417290535194472279 10870298125935802791708419)
                ·
                  refine ⟨16305447188903704187562629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10870298125935802791708419 16305447188903704187562629)
                  ·
                    refine ⟨3057271347919444535167993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16305447188903704187562629 3057271347919444535167993)
                    ·
                      refine ⟨2292953510939583401375995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3057271347919444535167993 2292953510939583401375995)
                      ·
                        rfl

theorem cell23_4465511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_4465511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465511 prefixEnd_4465511 := by exact prefixLift 4465511
  have htrace : WordTrace (prefixWord ++ tailWord_4465511) baseStart_4465511 baseEnd_4465511 := by
    simpa [prefixWord, tailWord_4465511, baseEnd_4465511] using wordTrace_append hprefix tailTrace_4465511
  have hstable : (prefixWord ++ tailWord_4465511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465511).length < 2 ^ (prefixWord ++ tailWord_4465511).sum := by decide
  have hdescent : baseEnd_4465511 < baseStart_4465511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465557 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_4465557 : Nat := 118140960795 + 4465557 * 2 ^ 59
def prefixEnd_4465557 : Nat := 4983230072969 + 3 ^ 40 * 4465557 * 2
def baseEnd_4465557 : Nat := 2292977131049690221400783

theorem tailTrace_4465557 : CollatzResearch.WordTrace tailWord_4465557 prefixEnd_4465557 2292977131049690221400783 := by
  unfold tailWord_4465557
  simp only [CollatzResearch.WordTrace]
  refine ⟨162872244283057120262530925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108581496188704746841687283 162872244283057120262530925)
  ·
    refine ⟨61077091606146420098449097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162872244283057120262530925 61077091606146420098449097)
    ·
      refine ⟨45807818704609815073836823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61077091606146420098449097 45807818704609815073836823)
      ·
        refine ⟨68711728056914722610755235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45807818704609815073836823 68711728056914722610755235)
        ·
          refine ⟨103067592085372083916132853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68711728056914722610755235 103067592085372083916132853)
          ·
            refine ⟨9662586758003632867137455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103067592085372083916132853 9662586758003632867137455)
            ·
              refine ⟨14493880137005449300706183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9662586758003632867137455 14493880137005449300706183)
              ·
                refine ⟨21740820205508173951059275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14493880137005449300706183 21740820205508173951059275)
                ·
                  refine ⟨32611230308262260926588913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21740820205508173951059275 32611230308262260926588913)
                  ·
                    refine ⟨24458422731196695694941685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32611230308262260926588913 24458422731196695694941685)
                    ·
                      refine ⟨2292977131049690221400783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24458422731196695694941685 2292977131049690221400783)
                      ·
                        rfl

theorem cell23_4465557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_4465557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465557 prefixEnd_4465557 := by exact prefixLift 4465557
  have htrace : WordTrace (prefixWord ++ tailWord_4465557) baseStart_4465557 baseEnd_4465557 := by
    simpa [prefixWord, tailWord_4465557, baseEnd_4465557] using wordTrace_append hprefix tailTrace_4465557
  have hstable : (prefixWord ++ tailWord_4465557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465557).length < 2 ^ (prefixWord ++ tailWord_4465557).sum := by decide
  have hdescent : baseEnd_4465557 < baseStart_4465557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465562 : List Nat := [3, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2]
def baseStart_4465562 : Nat := 118140960795 + 4465562 * 2 ^ 59
def prefixEnd_4465562 : Nat := 4983230072969 + 3 ^ 40 * 4465562 * 2
def baseEnd_4465562 : Nat := 2292979698452962701838261

theorem tailTrace_4465562 : CollatzResearch.WordTrace tailWord_4465562 prefixEnd_4465562 2292979698452962701838261 := by
  unfold tailWord_4465562
  simp only [CollatzResearch.WordTrace]
  refine ⟨40718106662009751529115735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108581617765359337410975293 40718106662009751529115735)
  ·
    refine ⟨61077159993014627293673603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40718106662009751529115735 61077159993014627293673603)
    ·
      refine ⟨91615739989521940940510405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61077159993014627293673603 91615739989521940940510405)
      ·
        refine ⟨17177951248035363926345701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91615739989521940940510405 17177951248035363926345701)
        ·
          refine ⟨3220865859006630736189819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17177951248035363926345701 3220865859006630736189819)
          ·
            refine ⟨4831298788509946104284729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3220865859006630736189819 4831298788509946104284729)
            ·
              refine ⟨3623474091382459578213547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4831298788509946104284729 3623474091382459578213547)
              ·
                refine ⟨5435211137073689367320321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3623474091382459578213547 5435211137073689367320321)
                ·
                  refine ⟨4076408352805267025490241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5435211137073689367320321 4076408352805267025490241)
                  ·
                    refine ⟨3057306264603950269117681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4076408352805267025490241 3057306264603950269117681)
                    ·
                      refine ⟨2292979698452962701838261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3057306264603950269117681 2292979698452962701838261)
                      ·
                        rfl

theorem cell23_4465562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_4465562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465562 prefixEnd_4465562 := by exact prefixLift 4465562
  have htrace : WordTrace (prefixWord ++ tailWord_4465562) baseStart_4465562 baseEnd_4465562 := by
    simpa [prefixWord, tailWord_4465562, baseEnd_4465562] using wordTrace_append hprefix tailTrace_4465562
  have hstable : (prefixWord ++ tailWord_4465562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465562).length < 2 ^ (prefixWord ++ tailWord_4465562).sum := by decide
  have hdescent : baseEnd_4465562 < baseStart_4465562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465577 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 5, 4]
def baseStart_4465577 : Nat := 118140960795 + 4465577 * 2 ^ 59
def prefixEnd_4465577 : Nat := 4983230072969 + 3 ^ 40 * 4465577 * 2
def baseEnd_4465577 : Nat := 764329133554260047716897

theorem tailTrace_4465577 : CollatzResearch.WordTrace tailWord_4465577 prefixEnd_4465577 764329133554260047716897 := by
  unfold tailWord_4465577
  simp only [CollatzResearch.WordTrace]
  refine ⟨162872973742984663678258985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108581982495323109118839323 162872973742984663678258985)
  ·
    refine ⟨122154730307238497758694239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162872973742984663678258985 122154730307238497758694239)
    ·
      refine ⟨183232095460857746638041359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122154730307238497758694239 183232095460857746638041359)
      ·
        refine ⟨274848143191286619957062039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183232095460857746638041359 274848143191286619957062039)
        ·
          refine ⟨412272214786929929935593059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274848143191286619957062039 412272214786929929935593059)
          ·
            refine ⟨618408322180394894903389589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412272214786929929935593059 618408322180394894903389589)
            ·
              refine ⟨28987890102206010698596387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 618408322180394894903389589 28987890102206010698596387)
              ·
                refine ⟨43481835153309016047894581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28987890102206010698596387 43481835153309016047894581)
                ·
                  refine ⟨4076422045622720254490117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43481835153309016047894581 4076422045622720254490117)
                  ·
                    refine ⟨764329133554260047716897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4076422045622720254490117 764329133554260047716897)
                    ·
                      rfl

theorem cell23_4465577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 4].length) (baseStart_4465577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465577 prefixEnd_4465577 := by exact prefixLift 4465577
  have htrace : WordTrace (prefixWord ++ tailWord_4465577) baseStart_4465577 baseEnd_4465577 := by
    simpa [prefixWord, tailWord_4465577, baseEnd_4465577] using wordTrace_append hprefix tailTrace_4465577
  have hstable : (prefixWord ++ tailWord_4465577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465577).length < 2 ^ (prefixWord ++ tailWord_4465577).sum := by decide
  have hdescent : baseEnd_4465577 < baseStart_4465577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465607 : List Nat := [1, 1, 4, 1, 1, 2, 3, 4, 6]
def baseStart_4465607 : Nat := 118140960795 + 4465607 * 2 ^ 59
def prefixEnd_4465607 : Nat := 4983230072969 + 3 ^ 40 * 4465607 * 2
def baseEnd_4465607 : Nat := 254778089453601669530617

theorem tailTrace_4465607 : CollatzResearch.WordTrace tailWord_4465607 prefixEnd_4465607 254778089453601669530617 := by
  unfold tailWord_4465607
  simp only [CollatzResearch.WordTrace]
  refine ⟨162874067932875978801851075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108582711955250652534567383 162874067932875978801851075)
  ·
    refine ⟨244311101899313968202776613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162874067932875978801851075 244311101899313968202776613)
    ·
      refine ⟨45808331606121369038020615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 244311101899313968202776613 45808331606121369038020615)
      ·
        refine ⟨68712497409182053557030923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45808331606121369038020615 68712497409182053557030923)
        ·
          refine ⟨103068746113773080335546385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68712497409182053557030923 103068746113773080335546385)
          ·
            refine ⟨77301559585329810251659789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103068746113773080335546385 77301559585329810251659789)
            ·
              refine ⟨28988084844498678844372421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77301559585329810251659789 28988084844498678844372421)
              ·
                refine ⟨5435265908343502283319829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28988084844498678844372421 5435265908343502283319829)
                ·
                  refine ⟨254778089453601669530617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5435265908343502283319829 254778089453601669530617)
                  ·
                    rfl

theorem cell23_4465607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 6].length) (baseStart_4465607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465607 prefixEnd_4465607 := by exact prefixLift 4465607
  have htrace : WordTrace (prefixWord ++ tailWord_4465607) baseStart_4465607 baseEnd_4465607 := by
    simpa [prefixWord, tailWord_4465607, baseEnd_4465607] using wordTrace_append hprefix tailTrace_4465607
  have hstable : (prefixWord ++ tailWord_4465607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465607).length < 2 ^ (prefixWord ++ tailWord_4465607).sum := by decide
  have hdescent : baseEnd_4465607 < baseStart_4465607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465611 : List Nat := [1, 1, 1, 1, 3, 6, 1, 4, 1, 4]
def baseStart_4465611 : Nat := 118140960795 + 4465611 * 2 ^ 59
def prefixEnd_4465611 : Nat := 4983230072969 + 3 ^ 40 * 4465611 * 2
def baseEnd_4465611 : Nat := 764334953001677670041845

theorem tailTrace_4465611 : CollatzResearch.WordTrace tailWord_4465611 prefixEnd_4465611 764334953001677670041845 := by
  unfold tailWord_4465611
  simp only [CollatzResearch.WordTrace]
  refine ⟨162874213824861487484996687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108582809216574324989997791 162874213824861487484996687)
  ·
    refine ⟨244311320737292231227495031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162874213824861487484996687 244311320737292231227495031)
    ·
      refine ⟨366466981105938346841242547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244311320737292231227495031 366466981105938346841242547)
      ·
        refine ⟨549700471658907520261863821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366466981105938346841242547 549700471658907520261863821)
        ·
          refine ⟨206137676872090320098198933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 549700471658907520261863821 206137676872090320098198933)
          ·
            refine ⟨9662703603379233754603075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 206137676872090320098198933 9662703603379233754603075)
            ·
              refine ⟨14494055405068850631904613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9662703603379233754603075 14494055405068850631904613)
              ·
                refine ⟨2717635388450409493482115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14494055405068850631904613 2717635388450409493482115)
                ·
                  refine ⟨4076453082675614240223173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2717635388450409493482115 4076453082675614240223173)
                  ·
                    refine ⟨764334953001677670041845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4076453082675614240223173 764334953001677670041845)
                    ·
                      rfl

theorem cell23_4465611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 1, 4].length) (baseStart_4465611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465611 prefixEnd_4465611 := by exact prefixLift 4465611
  have htrace : WordTrace (prefixWord ++ tailWord_4465611) baseStart_4465611 baseEnd_4465611 := by
    simpa [prefixWord, tailWord_4465611, baseEnd_4465611] using wordTrace_append hprefix tailTrace_4465611
  have hstable : (prefixWord ++ tailWord_4465611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465611).length < 2 ^ (prefixWord ++ tailWord_4465611).sum := by decide
  have hdescent : baseEnd_4465611 < baseStart_4465611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465725 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 3, 2, 2]
def baseStart_4465725 : Nat := 118140960795 + 4465725 * 2 ^ 59
def prefixEnd_4465725 : Nat := 4983230072969 + 3 ^ 40 * 4465725 * 2
def baseEnd_4465725 : Nat := 2293063395799645564100011

theorem tailTrace_4465725 : CollatzResearch.WordTrace tailWord_4465725 prefixEnd_4465725 2293063395799645564100011 := by
  unfold tailWord_4465725
  simp only [CollatzResearch.WordTrace]
  refine ⟨162878371746448484954646629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108585581164298989969764419 162878371746448484954646629)
  ·
    refine ⟨30539694702459090928996243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162878371746448484954646629 30539694702459090928996243)
    ·
      refine ⟨45809542053688636393494365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30539694702459090928996243 45809542053688636393494365)
      ·
        refine ⟨17178578270133238647560387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45809542053688636393494365 17178578270133238647560387)
        ·
          refine ⟨25767867405199857971340581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17178578270133238647560387 25767867405199857971340581)
          ·
            refine ⟨4831475138474973369626359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25767867405199857971340581 4831475138474973369626359)
            ·
              refine ⟨7247212707712460054439539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4831475138474973369626359 7247212707712460054439539)
              ·
                refine ⟨10870819061568690081659309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7247212707712460054439539 10870819061568690081659309)
                ·
                  refine ⟨4076557148088258780622241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10870819061568690081659309 4076557148088258780622241)
                  ·
                    refine ⟨3057417861066194085466681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4076557148088258780622241 3057417861066194085466681)
                    ·
                      refine ⟨2293063395799645564100011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3057417861066194085466681 2293063395799645564100011)
                      ·
                        rfl

theorem cell23_4465725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_4465725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465725 prefixEnd_4465725 := by exact prefixLift 4465725
  have htrace : WordTrace (prefixWord ++ tailWord_4465725) baseStart_4465725 baseEnd_4465725 := by
    simpa [prefixWord, tailWord_4465725, baseEnd_4465725] using wordTrace_append hprefix tailTrace_4465725
  have hstable : (prefixWord ++ tailWord_4465725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465725).length < 2 ^ (prefixWord ++ tailWord_4465725).sum := by decide
  have hdescent : baseEnd_4465725 < baseStart_4465725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465727 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 2, 7]
def baseStart_4465727 : Nat := 118140960795 + 4465727 * 2 ^ 59
def prefixEnd_4465727 : Nat := 4983230072969 + 3 ^ 40 * 4465727 * 2
def baseEnd_4465727 : Nat := 764354807586984852091667

theorem tailTrace_4465727 : CollatzResearch.WordTrace tailWord_4465727 prefixEnd_4465727 764354807586984852091667 := by
  unfold tailWord_4465727
  simp only [CollatzResearch.WordTrace]
  refine ⟨162878444692441239296219435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108585629794960826197479623 162878444692441239296219435)
  ·
    refine ⟨244317667038661858944329153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162878444692441239296219435 244317667038661858944329153)
    ·
      refine ⟨183238250278996394208246865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244317667038661858944329153 183238250278996394208246865)
      ·
        refine ⟨137428687709247295656185149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183238250278996394208246865 137428687709247295656185149)
        ·
          refine ⟨51535757890967735871069431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137428687709247295656185149 51535757890967735871069431)
          ·
            refine ⟨77303636836451603806604147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51535757890967735871069431 77303636836451603806604147)
            ·
              refine ⟨115955455254677405709906221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77303636836451603806604147 115955455254677405709906221)
              ·
                refine ⟨43483295720504027141214833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115955455254677405709906221 43483295720504027141214833)
                ·
                  refine ⟨32612471790378020355911125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43483295720504027141214833 32612471790378020355911125)
                  ·
                    refine ⟨764354807586984852091667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32612471790378020355911125 764354807586984852091667)
                    ·
                      rfl

theorem cell23_4465727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 7].length) (baseStart_4465727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465727 prefixEnd_4465727 := by exact prefixLift 4465727
  have htrace : WordTrace (prefixWord ++ tailWord_4465727) baseStart_4465727 baseEnd_4465727 := by
    simpa [prefixWord, tailWord_4465727, baseEnd_4465727] using wordTrace_append hprefix tailTrace_4465727
  have hstable : (prefixWord ++ tailWord_4465727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465727).length < 2 ^ (prefixWord ++ tailWord_4465727).sum := by decide
  have hdescent : baseEnd_4465727 < baseStart_4465727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465737 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 1, 4, 5]
def baseStart_4465737 : Nat := 118140960795 + 4465737 * 2 ^ 59
def prefixEnd_4465737 : Nat := 4983230072969 + 3 ^ 40 * 4465737 * 2
def baseEnd_4465737 : Nat := 2293069557567499517149955

theorem tailTrace_4465737 : CollatzResearch.WordTrace tailWord_4465737 prefixEnd_4465737 2293069557567499517149955 := by
  unfold tailWord_4465737
  simp only [CollatzResearch.WordTrace]
  refine ⟨162878809422405011004083465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108585872948270007336055643 162878809422405011004083465)
  ·
    refine ⟨122159107066803758253062599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162878809422405011004083465 122159107066803758253062599)
    ·
      refine ⟨183238660600205637379593899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122159107066803758253062599 183238660600205637379593899)
      ·
        refine ⟨274857990900308456069390849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183238660600205637379593899 274857990900308456069390849)
        ·
          refine ⟨206143493175231342052043137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274857990900308456069390849 206143493175231342052043137)
          ·
            refine ⟨154607619881423506539032353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206143493175231342052043137 154607619881423506539032353)
            ·
              refine ⟨115955714911067629904274265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154607619881423506539032353 115955714911067629904274265)
              ·
                refine ⟨86966786183300722428205699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115955714911067629904274265 86966786183300722428205699)
                ·
                  refine ⟨130450179274951083642308549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86966786183300722428205699 130450179274951083642308549)
                  ·
                    refine ⟨24459408614053328182932853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 130450179274951083642308549 24459408614053328182932853)
                    ·
                      refine ⟨2293069557567499517149955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24459408614053328182932853 2293069557567499517149955)
                      ·
                        rfl

theorem cell23_4465737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_4465737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465737 prefixEnd_4465737 := by exact prefixLift 4465737
  have htrace : WordTrace (prefixWord ++ tailWord_4465737) baseStart_4465737 baseEnd_4465737 := by
    simpa [prefixWord, tailWord_4465737, baseEnd_4465737] using wordTrace_append hprefix tailTrace_4465737
  have hstable : (prefixWord ++ tailWord_4465737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465737).length < 2 ^ (prefixWord ++ tailWord_4465737).sum := by decide
  have hdescent : baseEnd_4465737 < baseStart_4465737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465784 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 2, 4, 3]
def baseStart_4465784 : Nat := 118140960795 + 4465784 * 2 ^ 59
def prefixEnd_4465784 : Nat := 4983230072969 + 3 ^ 40 * 4465784 * 2
def baseEnd_4465784 : Nat := 2293093691158260833262239

theorem tailTrace_4465784 : CollatzResearch.WordTrace tailWord_4465784 prefixEnd_4465784 2293093691158260833262239 := by
  unfold tailWord_4465784
  simp only [CollatzResearch.WordTrace]
  refine ⟨81440261826617369015522203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108587015768823158687362937 81440261826617369015522203)
  ·
    refine ⟨122160392739926053523283305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81440261826617369015522203 122160392739926053523283305)
    ·
      refine ⟨91620294554944540142462479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122160392739926053523283305 91620294554944540142462479)
      ·
        refine ⟨137430441832416810213693719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91620294554944540142462479 137430441832416810213693719)
        ·
          refine ⟨206145662748625215320540579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137430441832416810213693719 206145662748625215320540579)
          ·
            refine ⟨309218494122937822980810869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206145662748625215320540579 309218494122937822980810869)
            ·
              refine ⟨28989233824025420904451019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 309218494122937822980810869 28989233824025420904451019)
              ·
                refine ⟨43483850736038131356676529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28989233824025420904451019 43483850736038131356676529)
                ·
                  refine ⟨32612888052028598517507397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43483850736038131356676529 32612888052028598517507397)
                  ·
                    refine ⟨6114916509755362222032637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32612888052028598517507397 6114916509755362222032637)
                    ·
                      refine ⟨2293093691158260833262239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6114916509755362222032637 2293093691158260833262239)
                      ·
                        rfl

theorem cell23_4465784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_4465784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465784 prefixEnd_4465784 := by exact prefixLift 4465784
  have htrace : WordTrace (prefixWord ++ tailWord_4465784) baseStart_4465784 baseEnd_4465784 := by
    simpa [prefixWord, tailWord_4465784, baseEnd_4465784] using wordTrace_append hprefix tailTrace_4465784
  have hstable : (prefixWord ++ tailWord_4465784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465784).length < 2 ^ (prefixWord ++ tailWord_4465784).sum := by decide
  have hdescent : baseEnd_4465784 < baseStart_4465784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465787 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 11]
def baseStart_4465787 : Nat := 118140960795 + 4465787 * 2 ^ 59
def prefixEnd_4465787 : Nat := 4983230072969 + 3 ^ 40 * 4465787 * 2
def baseEnd_4465787 : Nat := 254788359066691591280525

theorem tailTrace_4465787 : CollatzResearch.WordTrace tailWord_4465787 prefixEnd_4465787 254788359066691591280525 := by
  unfold tailWord_4465787
  simp only [CollatzResearch.WordTrace]
  refine ⟨162880633072223869543403615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108587088714815913028935743 162880633072223869543403615)
  ·
    refine ⟨244320949608335804315105423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162880633072223869543403615 244320949608335804315105423)
    ·
      refine ⟨366481424412503706472658135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244320949608335804315105423 366481424412503706472658135)
      ·
        refine ⟨549722136618755559708987203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366481424412503706472658135 549722136618755559708987203)
        ·
          refine ⟨824583204928133339563480805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549722136618755559708987203 824583204928133339563480805)
          ·
            refine ⟨154609350924025001168152651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 824583204928133339563480805 154609350924025001168152651)
            ·
              refine ⟨231914026386037501752228977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154609350924025001168152651 231914026386037501752228977)
              ·
                refine ⟨173935519789528126314171733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231914026386037501752228977 173935519789528126314171733)
                ·
                  refine ⟨254788359066691591280525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 173935519789528126314171733 254788359066691591280525)
                  ·
                    rfl

theorem cell23_4465787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 11].length) (baseStart_4465787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465787 prefixEnd_4465787 := by exact prefixLift 4465787
  have htrace : WordTrace (prefixWord ++ tailWord_4465787) baseStart_4465787 baseEnd_4465787 := by
    simpa [prefixWord, tailWord_4465787, baseEnd_4465787] using wordTrace_append hprefix tailTrace_4465787
  have hstable : (prefixWord ++ tailWord_4465787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465787).length < 2 ^ (prefixWord ++ tailWord_4465787).sum := by decide
  have hdescent : baseEnd_4465787 < baseStart_4465787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465871 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 4, 4, 2]
def baseStart_4465871 : Nat := 118140960795 + 4465871 * 2 ^ 59
def prefixEnd_4465871 : Nat := 4983230072969 + 3 ^ 40 * 4465871 * 2
def baseEnd_4465871 : Nat := 2293138363975201992874339

theorem tailTrace_4465871 : CollatzResearch.WordTrace tailWord_4465871 prefixEnd_4465871 2293138363975201992874339 := by
  unfold tailWord_4465871
  simp only [CollatzResearch.WordTrace]
  refine ⟨162883696803919551889461467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108589131202613034592974311 162883696803919551889461467)
  ·
    refine ⟨244325545205879327834192201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162883696803919551889461467 244325545205879327834192201)
    ·
      refine ⟨183244158904409495875644151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244325545205879327834192201 183244158904409495875644151)
      ·
        refine ⟨274866238356614243813466227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183244158904409495875644151 274866238356614243813466227)
        ·
          refine ⟨412299357534921365720199341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274866238356614243813466227 412299357534921365720199341)
          ·
            refine ⟨154612259075595512145074753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 412299357534921365720199341 154612259075595512145074753)
            ·
              refine ⟨115959194306696634108806065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154612259075595512145074753 115959194306696634108806065)
              ·
                refine ⟨86969395730022475581604549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115959194306696634108806065 86969395730022475581604549)
                ·
                  refine ⟨16306761699379214171550853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86969395730022475581604549 16306761699379214171550853)
                  ·
                    refine ⟨3057517818633602657165785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16306761699379214171550853 3057517818633602657165785)
                    ·
                      refine ⟨2293138363975201992874339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3057517818633602657165785 2293138363975201992874339)
                      ·
                        rfl

theorem cell23_4465871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 4, 2].length) (baseStart_4465871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465871 prefixEnd_4465871 := by exact prefixLift 4465871
  have htrace : WordTrace (prefixWord ++ tailWord_4465871) baseStart_4465871 baseEnd_4465871 := by
    simpa [prefixWord, tailWord_4465871, baseEnd_4465871] using wordTrace_append hprefix tailTrace_4465871
  have hstable : (prefixWord ++ tailWord_4465871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465871).length < 2 ^ (prefixWord ++ tailWord_4465871).sum := by decide
  have hdescent : baseEnd_4465871 < baseStart_4465871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465898 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 3, 4]
def baseStart_4465898 : Nat := 118140960795 + 4465898 * 2 ^ 59
def prefixEnd_4465898 : Nat := 4983230072969 + 3 ^ 40 * 4465898 * 2
def baseEnd_4465898 : Nat := 764384075984291129078905

theorem tailTrace_4465898 : CollatzResearch.WordTrace tailWord_4465898 prefixEnd_4465898 764384075984291129078905 := by
  unfold tailWord_4465898
  simp only [CollatzResearch.WordTrace]
  refine ⟨40721170393705433875173587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108589787716547823667129565 40721170393705433875173587)
  ·
    refine ⟨61081755590558150812760381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40721170393705433875173587 61081755590558150812760381)
    ·
      refine ⟨22905658346459306554785143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61081755590558150812760381 22905658346459306554785143)
      ·
        refine ⟨34358487519688959832177715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22905658346459306554785143 34358487519688959832177715)
        ·
          refine ⟨51537731279533439748266573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34358487519688959832177715 51537731279533439748266573)
          ·
            refine ⟨19326649229825039905599965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51537731279533439748266573 19326649229825039905599965)
            ·
              refine ⟨7247493461184389964599987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19326649229825039905599965 7247493461184389964599987)
              ·
                refine ⟨10871240191776584946899981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7247493461184389964599987 10871240191776584946899981)
                ·
                  refine ⟨4076715071916219355087493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10871240191776584946899981 4076715071916219355087493)
                  ·
                    refine ⟨764384075984291129078905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4076715071916219355087493 764384075984291129078905)
                    ·
                      rfl

theorem cell23_4465898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_4465898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465898 prefixEnd_4465898 := by exact prefixLift 4465898
  have htrace : WordTrace (prefixWord ++ tailWord_4465898) baseStart_4465898 baseEnd_4465898 := by
    simpa [prefixWord, tailWord_4465898, baseEnd_4465898] using wordTrace_append hprefix tailTrace_4465898
  have hstable : (prefixWord ++ tailWord_4465898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465898).length < 2 ^ (prefixWord ++ tailWord_4465898).sum := by decide
  have hdescent : baseEnd_4465898 < baseStart_4465898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465949 : List Nat := [1, 4, 2, 3, 1, 3, 2, 2, 1, 4]
def baseStart_4465949 : Nat := 118140960795 + 4465949 * 2 ^ 59
def prefixEnd_4465949 : Nat := 4983230072969 + 3 ^ 40 * 4465949 * 2
def baseEnd_4465949 : Nat := 764392805155417562566327

theorem tailTrace_4465949 : CollatzResearch.WordTrace tailWord_4465949 prefixEnd_4465949 764392805155417562566327 := by
  unfold tailWord_4465949
  simp only [CollatzResearch.WordTrace]
  refine ⟨162886541697636971210800901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108591027798424647473867267 162886541697636971210800901)
  ·
    refine ⟨30541226568306932102025169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162886541697636971210800901 30541226568306932102025169)
    ·
      refine ⟨22905919926230199076518877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30541226568306932102025169 22905919926230199076518877)
      ·
        refine ⟨8589719972336324653694579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22905919926230199076518877 8589719972336324653694579)
        ·
          refine ⟨12884579958504486980541869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8589719972336324653694579 12884579958504486980541869)
          ·
            refine ⟨4831717484439182617703201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12884579958504486980541869 4831717484439182617703201)
            ·
              refine ⟨3623788113329386963277401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4831717484439182617703201 3623788113329386963277401)
              ·
                refine ⟨2717841084997040222458051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3623788113329386963277401 2717841084997040222458051)
                ·
                  refine ⟨4076761627495560333687077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2717841084997040222458051 4076761627495560333687077)
                  ·
                    refine ⟨764392805155417562566327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4076761627495560333687077 764392805155417562566327)
                    ·
                      rfl

theorem cell23_4465949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_4465949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465949 prefixEnd_4465949 := by exact prefixLift 4465949
  have htrace : WordTrace (prefixWord ++ tailWord_4465949) baseStart_4465949 baseEnd_4465949 := by
    simpa [prefixWord, tailWord_4465949, baseEnd_4465949] using wordTrace_append hprefix tailTrace_4465949
  have hstable : (prefixWord ++ tailWord_4465949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465949).length < 2 ^ (prefixWord ++ tailWord_4465949).sum := by decide
  have hdescent : baseEnd_4465949 < baseStart_4465949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465971 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 1, 6]
def baseStart_4465971 : Nat := 118140960795 + 4465971 * 2 ^ 59
def prefixEnd_4465971 : Nat := 4983230072969 + 3 ^ 40 * 4465971 * 2
def baseEnd_4465971 : Nat := 764396570680217200541293

theorem tailTrace_4465971 : CollatzResearch.WordTrace tailWord_4465971 prefixEnd_4465971 764396570680217200541293 := by
  unfold tailWord_4465971
  simp only [CollatzResearch.WordTrace]
  refine ⟨162887344103557268968101767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108591562735704845978734511 162887344103557268968101767)
  ·
    refine ⟨244331016155335903452152651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162887344103557268968101767 244331016155335903452152651)
    ·
      refine ⟨366496524233003855178228977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244331016155335903452152651 366496524233003855178228977)
      ·
        refine ⟨274872393174752891383671733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366496524233003855178228977 274872393174752891383671733)
        ·
          refine ⟨25769286860133083567219225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 274872393174752891383671733 25769286860133083567219225)
          ·
            refine ⟨19326965145099812675414419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25769286860133083567219225 19326965145099812675414419)
            ·
              refine ⟨28990447717649719013121629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19326965145099812675414419 28990447717649719013121629)
              ·
                refine ⟨10871417894118644629920611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28990447717649719013121629 10871417894118644629920611)
                ·
                  refine ⟨16307126841177966944880917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10871417894118644629920611 16307126841177966944880917)
                  ·
                    refine ⟨764396570680217200541293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16307126841177966944880917 764396570680217200541293)
                    ·
                      rfl

theorem cell23_4465971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 6].length) (baseStart_4465971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465971 prefixEnd_4465971 := by exact prefixLift 4465971
  have htrace : WordTrace (prefixWord ++ tailWord_4465971) baseStart_4465971 baseEnd_4465971 := by
    simpa [prefixWord, tailWord_4465971, baseEnd_4465971] using wordTrace_append hprefix tailTrace_4465971
  have hstable : (prefixWord ++ tailWord_4465971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465971).length < 2 ^ (prefixWord ++ tailWord_4465971).sum := by decide
  have hdescent : baseEnd_4465971 < baseStart_4465971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4465978 : List Nat := [3, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4]
def baseStart_4465978 : Nat := 118140960795 + 4465978 * 2 ^ 59
def prefixEnd_4465978 : Nat := 4983230072969 + 3 ^ 40 * 4465978 * 2
def baseEnd_4465978 : Nat := 2293193306405233074236347

theorem tailTrace_4465978 : CollatzResearch.WordTrace tailWord_4465978 prefixEnd_4465978 2293193306405233074236347 := by
  unfold tailWord_4465978
  simp only [CollatzResearch.WordTrace]
  refine ⟨40721899853632977290901647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108591732943021272775737725 40721899853632977290901647)
  ·
    refine ⟨61082849780449465936352471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40721899853632977290901647 61082849780449465936352471)
    ·
      refine ⟨91624274670674198904528707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61082849780449465936352471 91624274670674198904528707)
      ·
        refine ⟨137436412006011298356793061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91624274670674198904528707 137436412006011298356793061)
        ·
          refine ⟨25769327251127118441898699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137436412006011298356793061 25769327251127118441898699)
          ·
            refine ⟨38653990876690677662848049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25769327251127118441898699 38653990876690677662848049)
            ·
              refine ⟨28990493157518008247136037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38653990876690677662848049 28990493157518008247136037)
              ·
                refine ⟨5435717467034626546338007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28990493157518008247136037 5435717467034626546338007)
                ·
                  refine ⟨8153576200551939819507011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5435717467034626546338007 8153576200551939819507011)
                  ·
                    refine ⟨12230364300827909729260517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8153576200551939819507011 12230364300827909729260517)
                    ·
                      refine ⟨2293193306405233074236347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12230364300827909729260517 2293193306405233074236347)
                      ·
                        rfl

theorem cell23_4465978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_4465978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4465978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4465978 prefixEnd_4465978 := by exact prefixLift 4465978
  have htrace : WordTrace (prefixWord ++ tailWord_4465978) baseStart_4465978 baseEnd_4465978 := by
    simpa [prefixWord, tailWord_4465978, baseEnd_4465978] using wordTrace_append hprefix tailTrace_4465978
  have hstable : (prefixWord ++ tailWord_4465978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4465978).length < 2 ^ (prefixWord ++ tailWord_4465978).sum := by decide
  have hdescent : baseEnd_4465978 < baseStart_4465978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4465978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466005 : List Nat := [1, 3, 2, 2, 3, 1, 3, 2, 2, 4]
def baseStart_4466005 : Nat := 118140960795 + 4466005 * 2 ^ 59
def prefixEnd_4466005 : Nat := 4983230072969 + 3 ^ 40 * 4466005 * 2
def baseEnd_4466005 : Nat := 764402390127634822866241

theorem tailTrace_4466005 : CollatzResearch.WordTrace tailWord_4466005 prefixEnd_4466005 764402390127634822866241 := by
  unfold tailWord_4466005
  simp only [CollatzResearch.WordTrace]
  refine ⟨162888584185434092774839469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108592389456956061849892979 162888584185434092774839469)
  ·
    refine ⟨61083219069537784790564801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162888584185434092774839469 61083219069537784790564801)
    ·
      refine ⟨45812414302153338592923601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61083219069537784790564801 45812414302153338592923601)
      ·
        refine ⟨34359310726615003944692701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45812414302153338592923601 34359310726615003944692701)
        ·
          refine ⟨12884741522480626479259763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34359310726615003944692701 12884741522480626479259763)
          ·
            refine ⟨19327112283720939718889645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12884741522480626479259763 19327112283720939718889645)
            ·
              refine ⟨7247667106395352394583617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19327112283720939718889645 7247667106395352394583617)
              ·
                refine ⟨5435750329796514295937713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7247667106395352394583617 5435750329796514295937713)
                ·
                  refine ⟨4076812747347385721953285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5435750329796514295937713 4076812747347385721953285)
                  ·
                    refine ⟨764402390127634822866241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4076812747347385721953285 764402390127634822866241)
                    ·
                      rfl

theorem cell23_4466005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_4466005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466005 prefixEnd_4466005 := by exact prefixLift 4466005
  have htrace : WordTrace (prefixWord ++ tailWord_4466005) baseStart_4466005 baseEnd_4466005 := by
    simpa [prefixWord, tailWord_4466005, baseEnd_4466005] using wordTrace_append hprefix tailTrace_4466005
  have hstable : (prefixWord ++ tailWord_4466005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466005).length < 2 ^ (prefixWord ++ tailWord_4466005).sum := by decide
  have hdescent : baseEnd_4466005 < baseStart_4466005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466041 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 2, 2, 5]
def baseStart_4466041 : Nat := 118140960795 + 4466041 * 2 ^ 59
def prefixEnd_4466041 : Nat := 4983230072969 + 3 ^ 40 * 4466041 * 2
def baseEnd_4466041 : Nat := 2293225655686466327748557

theorem tailTrace_4466041 : CollatzResearch.WordTrace tailWord_4466041 prefixEnd_4466041 2293225655686466327748557 := by
  unfold tailWord_4466041
  simp only [CollatzResearch.WordTrace]
  refine ⟨162889897213303670923149977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108593264808869113948766651 162889897213303670923149977)
  ·
    refine ⟨122167422909977753192362483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162889897213303670923149977 122167422909977753192362483)
    ·
      refine ⟨183251134364966629788543725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122167422909977753192362483 183251134364966629788543725)
      ·
        refine ⟨68719175386862486170703897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183251134364966629788543725 68719175386862486170703897)
        ·
          refine ⟨51539381540146864628027923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68719175386862486170703897 51539381540146864628027923)
          ·
            refine ⟨77309072310220296942041885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51539381540146864628027923 77309072310220296942041885)
            ·
              refine ⟨28990902116332611353265707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77309072310220296942041885 28990902116332611353265707)
              ·
                refine ⟨43486353174498917029898561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28990902116332611353265707 43486353174498917029898561)
                ·
                  refine ⟨32614764880874187772423921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43486353174498917029898561 32614764880874187772423921)
                  ·
                    refine ⟨24461073660655640829317941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32614764880874187772423921 24461073660655640829317941)
                    ·
                      refine ⟨2293225655686466327748557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24461073660655640829317941 2293225655686466327748557)
                      ·
                        rfl

theorem cell23_4466041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_4466041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466041 prefixEnd_4466041 := by exact prefixLift 4466041
  have htrace : WordTrace (prefixWord ++ tailWord_4466041) baseStart_4466041 baseEnd_4466041 := by
    simpa [prefixWord, tailWord_4466041, baseEnd_4466041] using wordTrace_append hprefix tailTrace_4466041
  have hstable : (prefixWord ++ tailWord_4466041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466041).length < 2 ^ (prefixWord ++ tailWord_4466041).sum := by decide
  have hdescent : baseEnd_4466041 < baseStart_4466041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466071 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 5]
def baseStart_4466071 : Nat := 118140960795 + 4466071 * 2 ^ 59
def prefixEnd_4466071 : Nat := 4983230072969 + 3 ^ 40 * 4466071 * 2
def baseEnd_4466071 : Nat := 2293241060106101210373419

theorem tailTrace_4466071 : CollatzResearch.WordTrace tailWord_4466071 prefixEnd_4466071 2293241060106101210373419 := by
  unfold tailWord_4466071
  simp only [CollatzResearch.WordTrace]
  refine ⟨162890991403194986046742067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108593994268796657364494711 162890991403194986046742067)
  ·
    refine ⟨244336487104792479070113101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162890991403194986046742067 244336487104792479070113101)
    ·
      refine ⟨91626182664297179651292413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244336487104792479070113101 91626182664297179651292413)
      ·
        refine ⟨34359818499111442369234655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91626182664297179651292413 34359818499111442369234655)
        ·
          refine ⟨51539727748667163553851983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34359818499111442369234655 51539727748667163553851983)
          ·
            refine ⟨77309591623000745330777975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51539727748667163553851983 77309591623000745330777975)
            ·
              refine ⟨115964387434501117996166963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77309591623000745330777975 115964387434501117996166963)
              ·
                refine ⟨173946581151751676994250445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115964387434501117996166963 173946581151751676994250445)
                ·
                  refine ⟨65229967931906878872843917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 173946581151751676994250445 65229967931906878872843917)
                  ·
                    refine ⟨24461237974465079577316469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65229967931906878872843917 24461237974465079577316469)
                    ·
                      refine ⟨2293241060106101210373419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24461237974465079577316469 2293241060106101210373419)
                      ·
                        rfl

theorem cell23_4466071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_4466071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466071 prefixEnd_4466071 := by exact prefixLift 4466071
  have htrace : WordTrace (prefixWord ++ tailWord_4466071) baseStart_4466071 baseEnd_4466071 := by
    simpa [prefixWord, tailWord_4466071, baseEnd_4466071] using wordTrace_append hprefix tailTrace_4466071
  have hstable : (prefixWord ++ tailWord_4466071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466071).length < 2 ^ (prefixWord ++ tailWord_4466071).sum := by decide
  have hdescent : baseEnd_4466071 < baseStart_4466071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466079 : List Nat := [1, 1, 2, 5, 1, 4, 2, 1, 2, 1, 3]
def baseStart_4466079 : Nat := 118140960795 + 4466079 * 2 ^ 59
def prefixEnd_4466079 : Nat := 4983230072969 + 3 ^ 40 * 4466079 * 2
def baseEnd_4466079 : Nat := 2293245167951337179073383

theorem tailTrace_4466079 : CollatzResearch.WordTrace tailWord_4466079 prefixEnd_4466079 2293245167951337179073383 := by
  unfold tailWord_4466079
  simp only [CollatzResearch.WordTrace]
  refine ⟨162891283187166003413033291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108594188791444002275355527 162891283187166003413033291)
  ·
    refine ⟨244336924780749005119549937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162891283187166003413033291 244336924780749005119549937)
    ·
      refine ⟨183252693585561753839662453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244336924780749005119549937 183252693585561753839662453)
      ·
        refine ⟨17179940023646414422468355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 183252693585561753839662453 17179940023646414422468355)
        ·
          refine ⟨25769910035469621633702533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17179940023646414422468355 25769910035469621633702533)
          ·
            refine ⟨4831858131650554056319225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25769910035469621633702533 4831858131650554056319225)
            ·
              refine ⟨3623893598737915542239419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4831858131650554056319225 3623893598737915542239419)
              ·
                refine ⟨5435840398106873313359129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3623893598737915542239419 5435840398106873313359129)
                ·
                  refine ⟨4076880298580154985019347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5435840398106873313359129 4076880298580154985019347)
                  ·
                    refine ⟨6115320447870232477529021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4076880298580154985019347 6115320447870232477529021)
                    ·
                      refine ⟨2293245167951337179073383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6115320447870232477529021 2293245167951337179073383)
                      ·
                        rfl

theorem cell23_4466079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_4466079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466079 prefixEnd_4466079 := by exact prefixLift 4466079
  have htrace : WordTrace (prefixWord ++ tailWord_4466079) baseStart_4466079 baseEnd_4466079 := by
    simpa [prefixWord, tailWord_4466079, baseEnd_4466079] using wordTrace_append hprefix tailTrace_4466079
  have hstable : (prefixWord ++ tailWord_4466079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466079).length < 2 ^ (prefixWord ++ tailWord_4466079).sum := by decide
  have hdescent : baseEnd_4466079 < baseStart_4466079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466085 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 6, 2, 2]
def baseStart_4466085 : Nat := 118140960795 + 4466085 * 2 ^ 59
def prefixEnd_4466085 : Nat := 4983230072969 + 3 ^ 40 * 4466085 * 2
def baseEnd_4466085 : Nat := 2293248248835264155598355

theorem tailTrace_4466085 : CollatzResearch.WordTrace tailWord_4466085 prefixEnd_4466085 2293248248835264155598355 := by
  unfold tailWord_4466085
  simp only [CollatzResearch.WordTrace]
  refine ⟨162891502025144266437751709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108594334683429510958501139 162891502025144266437751709)
  ·
    refine ⟨61084313259429099914156891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162891502025144266437751709 61084313259429099914156891)
    ·
      refine ⟨91626469889143649871235337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61084313259429099914156891 91626469889143649871235337)
      ·
        refine ⟨68719852416857737403426503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91626469889143649871235337 68719852416857737403426503)
        ·
          refine ⟨103079778625286606105139755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68719852416857737403426503 103079778625286606105139755)
          ·
            refine ⟨154619667937929909157709633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103079778625286606105139755 154619667937929909157709633)
            ·
              refine ⟨115964750953447431868282225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154619667937929909157709633 115964750953447431868282225)
              ·
                refine ⟨86973563215085573901211669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115964750953447431868282225 86973563215085573901211669)
                ·
                  refine ⟨4076885775707136276619297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86973563215085573901211669 4076885775707136276619297)
                  ·
                    refine ⟨3057664331780352207464473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4076885775707136276619297 3057664331780352207464473)
                    ·
                      refine ⟨2293248248835264155598355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3057664331780352207464473 2293248248835264155598355)
                      ·
                        rfl

theorem cell23_4466085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_4466085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466085 prefixEnd_4466085 := by exact prefixLift 4466085
  have htrace : WordTrace (prefixWord ++ tailWord_4466085) baseStart_4466085 baseEnd_4466085 := by
    simpa [prefixWord, tailWord_4466085, baseEnd_4466085] using wordTrace_append hprefix tailTrace_4466085
  have hstable : (prefixWord ++ tailWord_4466085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466085).length < 2 ^ (prefixWord ++ tailWord_4466085).sum := by decide
  have hdescent : baseEnd_4466085 < baseStart_4466085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466114 : List Nat := [3, 5, 2, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_4466114 : Nat := 118140960795 + 4466114 * 2 ^ 59
def prefixEnd_4466114 : Nat := 4983230072969 + 3 ^ 40 * 4466114 * 2
def baseEnd_4466114 : Nat := 2293263139774244542135723

theorem tailTrace_4466114 : CollatzResearch.WordTrace tailWord_4466114 prefixEnd_4466114 2293263139774244542135723 := by
  unfold tailWord_4466114
  simp only [CollatzResearch.WordTrace]
  refine ⟨40723139935509801097639349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108595039828026136260371597 40723139935509801097639349)
  ·
    refine ⟨3817794368954043852903689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40723139935509801097639349 3817794368954043852903689)
    ·
      refine ⟨2863345776715532889677767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3817794368954043852903689 2863345776715532889677767)
      ·
        refine ⟨4295018665073299334516651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2863345776715532889677767 4295018665073299334516651)
        ·
          refine ⟨6442527997609949001774977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4295018665073299334516651 6442527997609949001774977)
          ·
            refine ⟨4831895998207461751331233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6442527997609949001774977 4831895998207461751331233)
            ·
              refine ⟨3623921998655596313498425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4831895998207461751331233 3623921998655596313498425)
              ·
                refine ⟨2717941498991697235123819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3623921998655596313498425 2717941498991697235123819)
                ·
                  refine ⟨4076912248487545852685729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2717941498991697235123819 4076912248487545852685729)
                  ·
                    refine ⟨3057684186365659389514297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4076912248487545852685729 3057684186365659389514297)
                    ·
                      refine ⟨2293263139774244542135723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3057684186365659389514297 2293263139774244542135723)
                      ·
                        rfl

theorem cell23_4466114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_4466114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466114 prefixEnd_4466114 := by exact prefixLift 4466114
  have htrace : WordTrace (prefixWord ++ tailWord_4466114) baseStart_4466114 baseEnd_4466114 := by
    simpa [prefixWord, tailWord_4466114, baseEnd_4466114] using wordTrace_append hprefix tailTrace_4466114
  have hstable : (prefixWord ++ tailWord_4466114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466114).length < 2 ^ (prefixWord ++ tailWord_4466114).sum := by decide
  have hdescent : baseEnd_4466114 < baseStart_4466114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466121 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 3, 7]
def baseStart_4466121 : Nat := 118140960795 + 4466121 * 2 ^ 59
def prefixEnd_4466121 : Nat := 4983230072969 + 3 ^ 40 * 4466121 * 2
def baseEnd_4466121 : Nat := 764422244712942004916063

theorem tailTrace_4466121 : CollatzResearch.WordTrace tailWord_4466121 prefixEnd_4466121 764422244712942004916063 := by
  unfold tailWord_4466121
  simp only [CollatzResearch.WordTrace]
  refine ⟨162892815053013844586062217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108595210035342563057374811 162892815053013844586062217)
  ·
    refine ⟨122169611289760383439546663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162892815053013844586062217 122169611289760383439546663)
    ·
      refine ⟨183254416934640575159319995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122169611289760383439546663 183254416934640575159319995)
      ·
        refine ⟨274881625401960862738979993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183254416934640575159319995 274881625401960862738979993)
        ·
          refine ⟨206161219051470647054234995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274881625401960862738979993 206161219051470647054234995)
          ·
            refine ⟨309241828577205970581352493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206161219051470647054234995 309241828577205970581352493)
            ·
              refine ⟨115965685716452238968007185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 309241828577205970581352493 115965685716452238968007185)
              ·
                refine ⟨86974264287339179226005389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115965685716452238968007185 86974264287339179226005389)
                ·
                  refine ⟨32615349107752192209752021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86974264287339179226005389 32615349107752192209752021)
                  ·
                    refine ⟨764422244712942004916063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32615349107752192209752021 764422244712942004916063)
                    ·
                      rfl

theorem cell23_4466121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 7].length) (baseStart_4466121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466121 prefixEnd_4466121 := by exact prefixLift 4466121
  have htrace : WordTrace (prefixWord ++ tailWord_4466121) baseStart_4466121 baseEnd_4466121 := by
    simpa [prefixWord, tailWord_4466121, baseEnd_4466121] using wordTrace_append hprefix tailTrace_4466121
  have hstable : (prefixWord ++ tailWord_4466121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466121).length < 2 ^ (prefixWord ++ tailWord_4466121).sum := by decide
  have hdescent : baseEnd_4466121 < baseStart_4466121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466185 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 3, 4]
def baseStart_4466185 : Nat := 118140960795 + 4466185 * 2 ^ 59
def prefixEnd_4466185 : Nat := 4983230072969 + 3 ^ 40 * 4466185 * 2
def baseEnd_4466185 : Nat := 764433198966904588115965

theorem tailTrace_4466185 : CollatzResearch.WordTrace tailWord_4466185 prefixEnd_4466185 764433198966904588115965 := by
  unfold tailWord_4466185
  simp only [CollatzResearch.WordTrace]
  refine ⟨162895149324781983516392009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108596766216521322344261339 162895149324781983516392009)
  ·
    refine ⟨122171361993586487637294007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162895149324781983516392009 122171361993586487637294007)
    ·
      refine ⟨183257042990379731455941011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122171361993586487637294007 183257042990379731455941011)
      ·
        refine ⟨274885564485569597183911517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183257042990379731455941011 274885564485569597183911517)
        ·
          refine ⟨103082086682088598943966819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274885564485569597183911517 103082086682088598943966819)
          ·
            refine ⟨154623130023132898415950229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103082086682088598943966819 154623130023132898415950229)
            ·
              refine ⟨7247959219834354613247667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 154623130023132898415950229 7247959219834354613247667)
              ·
                refine ⟨10871938829751531919871501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7247959219834354613247667 10871938829751531919871501)
                ·
                  refine ⟨4076977061156824469951813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10871938829751531919871501 4076977061156824469951813)
                  ·
                    refine ⟨764433198966904588115965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4076977061156824469951813 764433198966904588115965)
                    ·
                      rfl

theorem cell23_4466185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 4].length) (baseStart_4466185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466185 prefixEnd_4466185 := by exact prefixLift 4466185
  have htrace : WordTrace (prefixWord ++ tailWord_4466185) baseStart_4466185 baseEnd_4466185 := by
    simpa [prefixWord, tailWord_4466185, baseEnd_4466185] using wordTrace_append hprefix tailTrace_4466185
  have hstable : (prefixWord ++ tailWord_4466185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466185).length < 2 ^ (prefixWord ++ tailWord_4466185).sum := by decide
  have hdescent : baseEnd_4466185 < baseStart_4466185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466236 : List Nat := [2, 2, 2, 2, 4, 1, 3, 2, 1, 4]
def baseStart_4466236 : Nat := 118140960795 + 4466236 * 2 ^ 59
def prefixEnd_4466236 : Nat := 4983230072969 + 3 ^ 40 * 4466236 * 2
def baseEnd_4466236 : Nat := 764441928138031021603387

theorem tailTrace_4466236 : CollatzResearch.WordTrace tailWord_4466236 prefixEnd_4466236 764441928138031021603387 := by
  unfold tailWord_4466236
  simp only [CollatzResearch.WordTrace]
  refine ⟨81448504723798609613249281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108598006298398146150999041 81448504723798609613249281)
  ·
    refine ⟨61086378542848957209936961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81448504723798609613249281 61086378542848957209936961)
    ·
      refine ⟨45814783907136717907452721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61086378542848957209936961 45814783907136717907452721)
      ·
        refine ⟨34361087930352538430589541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45814783907136717907452721 34361087930352538430589541)
        ·
          refine ⟨6442703986941100955735539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34361087930352538430589541 6442703986941100955735539)
          ·
            refine ⟨9664055980411651433603309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6442703986941100955735539 9664055980411651433603309)
            ·
              refine ⟨3624020992654369287601241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9664055980411651433603309 3624020992654369287601241)
              ·
                refine ⟨2718015744490776965700931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3624020992654369287601241 2718015744490776965700931)
                ·
                  refine ⟨4077023616736165448551397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718015744490776965700931 4077023616736165448551397)
                  ·
                    refine ⟨764441928138031021603387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4077023616736165448551397 764441928138031021603387)
                    ·
                      rfl

theorem cell23_4466236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_4466236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466236 prefixEnd_4466236 := by exact prefixLift 4466236
  have htrace : WordTrace (prefixWord ++ tailWord_4466236) baseStart_4466236 baseEnd_4466236 := by
    simpa [prefixWord, tailWord_4466236, baseEnd_4466236] using wordTrace_append hprefix tailTrace_4466236
  have hstable : (prefixWord ++ tailWord_4466236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466236).length < 2 ^ (prefixWord ++ tailWord_4466236).sum := by decide
  have hdescent : baseEnd_4466236 < baseStart_4466236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466248 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_4466248 : Nat := 118140960795 + 4466248 * 2 ^ 59
def prefixEnd_4466248 : Nat := 4983230072969 + 3 ^ 40 * 4466248 * 2
def baseEnd_4466248 : Nat := 2293331946181947017860105

theorem tailTrace_4466248 : CollatzResearch.WordTrace tailWord_4466248 prefixEnd_4466248 2293331946181947017860105 := by
  unfold tailWord_4466248
  simp only [CollatzResearch.WordTrace]
  refine ⟨81448723561776872637967699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108598298082369163517290265 81448723561776872637967699)
  ·
    refine ⟨122173085342665308956951549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81448723561776872637967699 122173085342665308956951549)
    ·
      refine ⟨45814907003499490858856831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122173085342665308956951549 45814907003499490858856831)
      ·
        refine ⟨68722360505249236288285247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45814907003499490858856831 68722360505249236288285247)
        ·
          refine ⟨103083540757873854432427871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68722360505249236288285247 103083540757873854432427871)
          ·
            refine ⟨154625311136810781648641807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103083540757873854432427871 154625311136810781648641807)
            ·
              refine ⟨231937966705216172472962711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154625311136810781648641807 231937966705216172472962711)
              ·
                refine ⟨347906950057824258709444067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231937966705216172472962711 347906950057824258709444067)
                ·
                  refine ⟨521860425086736388064166101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 347906950057824258709444067 521860425086736388064166101)
                  ·
                    refine ⟨12231103712970384095253893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 521860425086736388064166101 12231103712970384095253893)
                    ·
                      refine ⟨2293331946181947017860105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12231103712970384095253893 2293331946181947017860105)
                      ·
                        rfl

theorem cell23_4466248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_4466248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466248 prefixEnd_4466248 := by exact prefixLift 4466248
  have htrace : WordTrace (prefixWord ++ tailWord_4466248) baseStart_4466248 baseEnd_4466248 := by
    simpa [prefixWord, tailWord_4466248, baseEnd_4466248] using wordTrace_append hprefix tailTrace_4466248
  have hstable : (prefixWord ++ tailWord_4466248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466248).length < 2 ^ (prefixWord ++ tailWord_4466248).sum := by decide
  have hdescent : baseEnd_4466248 < baseStart_4466248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466265 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 2, 6, 2]
def baseStart_4466265 : Nat := 118140960795 + 4466265 * 2 ^ 59
def prefixEnd_4466265 : Nat := 4983230072969 + 3 ^ 40 * 4466265 * 2
def baseEnd_4466265 : Nat := 2293340675353073451347527

theorem tailTrace_4466265 : CollatzResearch.WordTrace tailWord_4466265 prefixEnd_4466265 2293340675353073451347527 := by
  unfold tailWord_4466265
  simp only [CollatzResearch.WordTrace]
  refine ⟨162898067164492157179304249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108598711442994771452869499 162898067164492157179304249)
  ·
    refine ⟨122173550373369117884478187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162898067164492157179304249 122173550373369117884478187)
    ·
      refine ⟨183260325560053676826717281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122173550373369117884478187 183260325560053676826717281)
      ·
        refine ⟨137445244170040257620037961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183260325560053676826717281 137445244170040257620037961)
        ·
          refine ⟨103083933127530193215028471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137445244170040257620037961 103083933127530193215028471)
          ·
            refine ⟨154625899691295289822542707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103083933127530193215028471 154625899691295289822542707)
            ·
              refine ⟨231938849536942934733814061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154625899691295289822542707 231938849536942934733814061)
              ·
                refine ⟨86977068576353600525180273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231938849536942934733814061 86977068576353600525180273)
                ·
                  refine ⟨65232801432265200393885205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86977068576353600525180273 65232801432265200393885205)
                  ·
                    refine ⟨3057787567137431268463369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65232801432265200393885205 3057787567137431268463369)
                    ·
                      refine ⟨2293340675353073451347527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3057787567137431268463369 2293340675353073451347527)
                      ·
                        rfl

theorem cell23_4466265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 6, 2].length) (baseStart_4466265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466265 prefixEnd_4466265 := by exact prefixLift 4466265
  have htrace : WordTrace (prefixWord ++ tailWord_4466265) baseStart_4466265 baseEnd_4466265 := by
    simpa [prefixWord, tailWord_4466265, baseEnd_4466265] using wordTrace_append hprefix tailTrace_4466265
  have hstable : (prefixWord ++ tailWord_4466265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466265).length < 2 ^ (prefixWord ++ tailWord_4466265).sum := by decide
  have hdescent : baseEnd_4466265 < baseStart_4466265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466275 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 1, 6]
def baseStart_4466275 : Nat := 118140960795 + 4466275 * 2 ^ 59
def prefixEnd_4466275 : Nat := 4983230072969 + 3 ^ 40 * 4466275 * 2
def baseEnd_4466275 : Nat := 764448603386539470740827

theorem tailTrace_4466275 : CollatzResearch.WordTrace tailWord_4466275 prefixEnd_4466275 764448603386539470740827 := by
  unfold tailWord_4466275
  simp only [CollatzResearch.WordTrace]
  refine ⟨162898431894455928887168279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108598954596303952591445519 162898431894455928887168279)
  ·
    refine ⟨244347647841683893330752419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162898431894455928887168279 244347647841683893330752419)
    ·
      refine ⟨366521471762525839996128629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244347647841683893330752419 366521471762525839996128629)
      ·
        refine ⟨34361387977736797499637059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 366521471762525839996128629 34361387977736797499637059)
        ·
          refine ⟨51542081966605196249455589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34361387977736797499637059 51542081966605196249455589)
          ·
            refine ⟨9664140368738474296772923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51542081966605196249455589 9664140368738474296772923)
            ·
              refine ⟨14496210553107711445159385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9664140368738474296772923 14496210553107711445159385)
              ·
                refine ⟨10872157914830783583869539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14496210553107711445159385 10872157914830783583869539)
                ·
                  refine ⟨16308236872246175375804309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10872157914830783583869539 16308236872246175375804309)
                  ·
                    refine ⟨764448603386539470740827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16308236872246175375804309 764448603386539470740827)
                    ·
                      rfl

theorem cell23_4466275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 6].length) (baseStart_4466275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466275 prefixEnd_4466275 := by exact prefixLift 4466275
  have htrace : WordTrace (prefixWord ++ tailWord_4466275) baseStart_4466275 baseEnd_4466275 := by
    simpa [prefixWord, tailWord_4466275, baseEnd_4466275] using wordTrace_append hprefix tailTrace_4466275
  have hstable : (prefixWord ++ tailWord_4466275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466275).length < 2 ^ (prefixWord ++ tailWord_4466275).sum := by decide
  have hdescent : baseEnd_4466275 < baseStart_4466275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466288 : List Nat := [2, 1, 1, 1, 6, 12]
def baseStart_4466288 : Nat := 118140960795 + 4466288 * 2 ^ 59
def prefixEnd_4466288 : Nat := 4983230072969 + 3 ^ 40 * 4466288 * 2
def baseEnd_4466288 : Nat := 9437664549004637289547

theorem tailTrace_4466288 : CollatzResearch.WordTrace tailWord_4466288 prefixEnd_4466288 9437664549004637289547 := by
  unfold tailWord_4466288
  simp only [CollatzResearch.WordTrace]
  refine ⟨81449453021704416053695759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108599270695605888071594345 81449453021704416053695759)
  ·
    refine ⟨122174179532556624080543639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81449453021704416053695759 122174179532556624080543639)
    ·
      refine ⟨183261269298834936120815459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122174179532556624080543639 183261269298834936120815459)
      ·
        refine ⟨274891903948252404181223189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183261269298834936120815459 274891903948252404181223189)
        ·
          refine ⟨12885557997574331445994837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 274891903948252404181223189 12885557997574331445994837)
          ·
            refine ⟨9437664549004637289547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 12885557997574331445994837 9437664549004637289547)
            ·
              rfl

theorem cell23_4466288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 12].length) (baseStart_4466288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466288 prefixEnd_4466288 := by exact prefixLift 4466288
  have htrace : WordTrace (prefixWord ++ tailWord_4466288) baseStart_4466288 baseEnd_4466288 := by
    simpa [prefixWord, tailWord_4466288, baseEnd_4466288] using wordTrace_append hprefix tailTrace_4466288
  have hstable : (prefixWord ++ tailWord_4466288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466288).length < 2 ^ (prefixWord ++ tailWord_4466288).sum := by decide
  have hdescent : baseEnd_4466288 < baseStart_4466288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466293 : List Nat := [1, 3, 4, 2, 1, 1, 4, 2, 1, 1, 3]
def baseStart_4466293 : Nat := 118140960795 + 4466293 * 2 ^ 59
def prefixEnd_4466293 : Nat := 4983230072969 + 3 ^ 40 * 4466293 * 2
def baseEnd_4466293 : Nat := 2293355052811399341797399

theorem tailTrace_4466293 : CollatzResearch.WordTrace tailWord_4466293 prefixEnd_4466293 2293355052811399341797399 := by
  unfold tailWord_4466293
  simp only [CollatzResearch.WordTrace]
  refine ⟨162899088408390717961323533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108599392272260478640882355 162899088408390717961323533)
  ·
    refine ⟨61087158153146519235496325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162899088408390717961323533 61087158153146519235496325)
    ·
      refine ⟨11453842153714972356655561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61087158153146519235496325 11453842153714972356655561)
      ·
        refine ⟨8590381615286229267491671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11453842153714972356655561 8590381615286229267491671)
        ·
          refine ⟨12885572422929343901237507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8590381615286229267491671 12885572422929343901237507)
          ·
            refine ⟨19328358634394015851856261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12885572422929343901237507 19328358634394015851856261)
            ·
              refine ⟨3624067243948877972223049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19328358634394015851856261 3624067243948877972223049)
              ·
                refine ⟨2718050432961658479167287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3624067243948877972223049 2718050432961658479167287)
                ·
                  refine ⟨4077075649442487718750931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718050432961658479167287 4077075649442487718750931)
                  ·
                    refine ⟨6115613474163731578126397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4077075649442487718750931 6115613474163731578126397)
                    ·
                      refine ⟨2293355052811399341797399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6115613474163731578126397 2293355052811399341797399)
                      ·
                        rfl

theorem cell23_4466293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_4466293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466293 prefixEnd_4466293 := by exact prefixLift 4466293
  have htrace : WordTrace (prefixWord ++ tailWord_4466293) baseStart_4466293 baseEnd_4466293 := by
    simpa [prefixWord, tailWord_4466293, baseEnd_4466293] using wordTrace_append hprefix tailTrace_4466293
  have hstable : (prefixWord ++ tailWord_4466293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466293).length < 2 ^ (prefixWord ++ tailWord_4466293).sum := by decide
  have hdescent : baseEnd_4466293 < baseStart_4466293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466298 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7]
def baseStart_4466298 : Nat := 118140960795 + 4466298 * 2 ^ 59
def prefixEnd_4466298 : Nat := 4983230072969 + 3 ^ 40 * 4466298 * 2
def baseEnd_4466298 : Nat := 2293357620214671822234875

theorem tailTrace_4466298 : CollatzResearch.WordTrace tailWord_4466298 prefixEnd_4466298 2293357620214671822234875 := by
  unfold tailWord_4466298
  simp only [CollatzResearch.WordTrace]
  refine ⟨40724817693343150953813887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108599513848915069210170365 40724817693343150953813887)
  ·
    refine ⟨61087226540014726430720831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40724817693343150953813887 61087226540014726430720831)
    ·
      refine ⟨91630839810022089646081247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61087226540014726430720831 91630839810022089646081247)
      ·
        refine ⟨137446259715033134469121871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91630839810022089646081247 137446259715033134469121871)
        ·
          refine ⟨206169389572549701703682807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137446259715033134469121871 206169389572549701703682807)
          ·
            refine ⟨309254084358824552555524211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206169389572549701703682807 309254084358824552555524211)
            ·
              refine ⟨463881126538236828833286317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309254084358824552555524211 463881126538236828833286317)
              ·
                refine ⟨173955422451838810812482369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 463881126538236828833286317 173955422451838810812482369)
                ·
                  refine ⟨130466566838879108109361777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173955422451838810812482369 130466566838879108109361777)
                  ·
                    refine ⟨97849925129159331082021333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 130466566838879108109361777 97849925129159331082021333)
                    ·
                      refine ⟨2293357620214671822234875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97849925129159331082021333 2293357620214671822234875)
                      ·
                        rfl

theorem cell23_4466298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_4466298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466298 prefixEnd_4466298 := by exact prefixLift 4466298
  have htrace : WordTrace (prefixWord ++ tailWord_4466298) baseStart_4466298 baseEnd_4466298 := by
    simpa [prefixWord, tailWord_4466298, baseEnd_4466298] using wordTrace_append hprefix tailTrace_4466298
  have hstable : (prefixWord ++ tailWord_4466298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466298).length < 2 ^ (prefixWord ++ tailWord_4466298).sum := by decide
  have hdescent : baseEnd_4466298 < baseStart_4466298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466305 : List Nat := [1, 2, 4, 2, 1, 2, 3, 8]
def baseStart_4466305 : Nat := 118140960795 + 4466305 * 2 ^ 59
def prefixEnd_4466305 : Nat := 4983230072969 + 3 ^ 40 * 4466305 * 2
def baseEnd_4466305 : Nat := 84939304243676047957309

theorem tailTrace_4466305 : CollatzResearch.WordTrace tailWord_4466305 prefixEnd_4466305 84939304243676047957309 := by
  unfold tailWord_4466305
  simp only [CollatzResearch.WordTrace]
  refine ⟨162899526084347244010760369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108599684056231496007173579 162899526084347244010760369)
  ·
    refine ⟨122174644563260433008070277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162899526084347244010760369 122174644563260433008070277)
    ·
      refine ⟨22907745855611331189013177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122174644563260433008070277 22907745855611331189013177)
      ·
        refine ⟨17180809391708498391759883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22907745855611331189013177 17180809391708498391759883)
        ·
          refine ⟨25771214087562747587639825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17180809391708498391759883 25771214087562747587639825)
          ·
            refine ⟨19328410565672060690729869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25771214087562747587639825 19328410565672060690729869)
            ·
              refine ⟨7248153962127022759023701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19328410565672060690729869 7248153962127022759023701)
              ·
                refine ⟨84939304243676047957309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7248153962127022759023701 84939304243676047957309)
                ·
                  rfl

theorem cell23_4466305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 8].length) (baseStart_4466305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466305 prefixEnd_4466305 := by exact prefixLift 4466305
  have htrace : WordTrace (prefixWord ++ tailWord_4466305) baseStart_4466305 baseEnd_4466305 := by
    simpa [prefixWord, tailWord_4466305, baseEnd_4466305] using wordTrace_append hprefix tailTrace_4466305
  have hstable : (prefixWord ++ tailWord_4466305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466305).length < 2 ^ (prefixWord ++ tailWord_4466305).sum := by decide
  have hdescent : baseEnd_4466305 < baseStart_4466305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466336 : List Nat := [2, 1, 1, 4, 3, 3, 2, 1, 1, 2, 3]
def baseStart_4466336 : Nat := 118140960795 + 4466336 * 2 ^ 59
def prefixEnd_4466336 : Nat := 4983230072969 + 3 ^ 40 * 4466336 * 2
def baseEnd_4466336 : Nat := 2293377132479542673559701

theorem tailTrace_4466336 : CollatzResearch.WordTrace tailWord_4466336 prefixEnd_4466336 2293377132479542673559701 := by
  unfold tailWord_4466336
  simp only [CollatzResearch.WordTrace]
  refine ⟨81450328373617468152569431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108600437831489957536759241 81450328373617468152569431)
  ·
    refine ⟨122175492560426202228854147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81450328373617468152569431 122175492560426202228854147)
    ·
      refine ⟨183263238840639303343281221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122175492560426202228854147 183263238840639303343281221)
      ·
        refine ⟨34361857282619869376865229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183263238840639303343281221 34361857282619869376865229)
        ·
          refine ⟨12885696480982451016324461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34361857282619869376865229 12885696480982451016324461)
          ·
            refine ⟨4832136180368419131121673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12885696480982451016324461 4832136180368419131121673)
            ·
              refine ⟨3624102135276314348341255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4832136180368419131121673 3624102135276314348341255)
              ·
                refine ⟨5436153202914471522511883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3624102135276314348341255 5436153202914471522511883)
                ·
                  refine ⟨8154229804371707283767825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5436153202914471522511883 8154229804371707283767825)
                  ·
                    refine ⟨6115672353278780462825869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8154229804371707283767825 6115672353278780462825869)
                    ·
                      refine ⟨2293377132479542673559701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6115672353278780462825869 2293377132479542673559701)
                      ·
                        rfl

theorem cell23_4466336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_4466336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466336 prefixEnd_4466336 := by exact prefixLift 4466336
  have htrace : WordTrace (prefixWord ++ tailWord_4466336) baseStart_4466336 baseEnd_4466336 := by
    simpa [prefixWord, tailWord_4466336, baseEnd_4466336] using wordTrace_append hprefix tailTrace_4466336
  have hstable : (prefixWord ++ tailWord_4466336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466336).length < 2 ^ (prefixWord ++ tailWord_4466336).sum := by decide
  have hdescent : baseEnd_4466336 < baseStart_4466336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466349 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_4466349 : Nat := 118140960795 + 4466349 * 2 ^ 59
def prefixEnd_4466349 : Nat := 4983230072969 + 3 ^ 40 * 4466349 * 2
def baseEnd_4466349 : Nat := 2293383807728051122697141

theorem tailTrace_4466349 : CollatzResearch.WordTrace tailWord_4466349 prefixEnd_4466349 2293383807728051122697141 := by
  unfold tailWord_4466349
  simp only [CollatzResearch.WordTrace]
  refine ⟨162901130896187839525362101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108600753930791893016908067 162901130896187839525362101)
  ·
    refine ⟨15271981021517609955502697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162901130896187839525362101 15271981021517609955502697)
    ·
      refine ⟨11453985766138207466627023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15271981021517609955502697 11453985766138207466627023)
      ·
        refine ⟨17180978649207311199940535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11453985766138207466627023 17180978649207311199940535)
        ·
          refine ⟨25771467973810966799910803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17180978649207311199940535 25771467973810966799910803)
          ·
            refine ⟨38657201960716450199866205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25771467973810966799910803 38657201960716450199866205)
            ·
              refine ⟨14496450735268668824949827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38657201960716450199866205 14496450735268668824949827)
              ·
                refine ⟨21744676102903003237424741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14496450735268668824949827 21744676102903003237424741)
                ·
                  refine ⟨4077126769294313107017139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21744676102903003237424741 4077126769294313107017139)
                  ·
                    refine ⟨6115690153941469660525709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4077126769294313107017139 6115690153941469660525709)
                    ·
                      refine ⟨2293383807728051122697141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6115690153941469660525709 2293383807728051122697141)
                      ·
                        rfl

theorem cell23_4466349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_4466349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466349 prefixEnd_4466349 := by exact prefixLift 4466349
  have htrace : WordTrace (prefixWord ++ tailWord_4466349) baseStart_4466349 baseEnd_4466349 := by
    simpa [prefixWord, tailWord_4466349, baseEnd_4466349] using wordTrace_append hprefix tailTrace_4466349
  have hstable : (prefixWord ++ tailWord_4466349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466349).length < 2 ^ (prefixWord ++ tailWord_4466349).sum := by decide
  have hdescent : baseEnd_4466349 < baseStart_4466349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466365 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 2, 6]
def baseStart_4466365 : Nat := 118140960795 + 4466365 * 2 ^ 59
def prefixEnd_4466365 : Nat := 4983230072969 + 3 ^ 40 * 4466365 * 2
def baseEnd_4466365 : Nat := 764464007806174353365689

theorem tailTrace_4466365 : CollatzResearch.WordTrace tailWord_4466365 prefixEnd_4466365 764464007806174353365689 := by
  unfold tailWord_4466365
  simp only [CollatzResearch.WordTrace]
  refine ⟨162901714464129874257944549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108601142976086582838629699 162901714464129874257944549)
  ·
    refine ⟨30544071462024351423364603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162901714464129874257944549 30544071462024351423364603)
    ·
      refine ⟨45816107193036527135046905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30544071462024351423364603 45816107193036527135046905)
      ·
        refine ⟨34362080394777395351285179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45816107193036527135046905 34362080394777395351285179)
        ·
          refine ⟨51543120592166093026927769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34362080394777395351285179 51543120592166093026927769)
          ·
            refine ⟨38657340444124569770195827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51543120592166093026927769 38657340444124569770195827)
            ·
              refine ⟨57986010666186854655293741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38657340444124569770195827 57986010666186854655293741)
              ·
                refine ⟨21744753999820070495735153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57986010666186854655293741 21744753999820070495735153)
                ·
                  refine ⟨16308565499865052871801365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21744753999820070495735153 16308565499865052871801365)
                  ·
                    refine ⟨764464007806174353365689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16308565499865052871801365 764464007806174353365689)
                    ·
                      rfl

theorem cell23_4466365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_4466365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466365 prefixEnd_4466365 := by exact prefixLift 4466365
  have htrace : WordTrace (prefixWord ++ tailWord_4466365) baseStart_4466365 baseEnd_4466365 := by
    simpa [prefixWord, tailWord_4466365, baseEnd_4466365] using wordTrace_append hprefix tailTrace_4466365
  have hstable : (prefixWord ++ tailWord_4466365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466365).length < 2 ^ (prefixWord ++ tailWord_4466365).sum := by decide
  have hdescent : baseEnd_4466365 < baseStart_4466365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466370 : List Nat := [3, 5, 1, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_4466370 : Nat := 118140960795 + 4466370 * 2 ^ 59
def prefixEnd_4466370 : Nat := 4983230072969 + 3 ^ 40 * 4466370 * 2
def baseEnd_4466370 : Nat := 2293394590821795540534545

theorem tailTrace_4466370 : CollatzResearch.WordTrace tailWord_4466370 prefixEnd_4466370 2293394590821795540534545 := by
  unfold tailWord_4466370
  simp only [CollatzResearch.WordTrace]
  refine ⟨40725474207277940027969141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108601264552741173407917709 40725474207277940027969141)
  ·
    refine ⟨3818013206932306877622107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40725474207277940027969141 3818013206932306877622107)
    ·
      refine ⟨5727019810398460316433161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3818013206932306877622107 5727019810398460316433161)
      ·
        refine ⟨4295264857798845237324871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5727019810398460316433161 4295264857798845237324871)
        ·
          refine ⟨6442897286698267855987307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4295264857798845237324871 6442897286698267855987307)
          ·
            refine ⟨9664345930047401783980961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6442897286698267855987307 9664345930047401783980961)
            ·
              refine ⟨7248259447535551337985721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9664345930047401783980961 7248259447535551337985721)
              ·
                refine ⟨5436194585651663503489291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7248259447535551337985721 5436194585651663503489291)
                ·
                  refine ⟨8154291878477495255233937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5436194585651663503489291 8154291878477495255233937)
                  ·
                    refine ⟨6115718908858121441425453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8154291878477495255233937 6115718908858121441425453)
                    ·
                      refine ⟨2293394590821795540534545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6115718908858121441425453 2293394590821795540534545)
                      ·
                        rfl

theorem cell23_4466370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_4466370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466370 prefixEnd_4466370 := by exact prefixLift 4466370
  have htrace : WordTrace (prefixWord ++ tailWord_4466370) baseStart_4466370 baseEnd_4466370 := by
    simpa [prefixWord, tailWord_4466370, baseEnd_4466370] using wordTrace_append hprefix tailTrace_4466370
  have hstable : (prefixWord ++ tailWord_4466370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466370).length < 2 ^ (prefixWord ++ tailWord_4466370).sum := by decide
  have hdescent : baseEnd_4466370 < baseStart_4466370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466375 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_4466375 : Nat := 118140960795 + 4466375 * 2 ^ 59
def prefixEnd_4466375 : Nat := 4983230072969 + 3 ^ 40 * 4466375 * 2
def baseEnd_4466375 : Nat := 2293397158225068020972021

theorem tailTrace_4466375 : CollatzResearch.WordTrace tailWord_4466375 prefixEnd_4466375 2293397158225068020972021 := by
  unfold tailWord_4466375
  simp only [CollatzResearch.WordTrace]
  refine ⟨162902079194093645965808579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108601386129395763977205719 162902079194093645965808579)
  ·
    refine ⟨244353118791140468948712869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162902079194093645965808579 244353118791140468948712869)
    ·
      refine ⟨45816209773338837927883663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 244353118791140468948712869 45816209773338837927883663)
      ·
        refine ⟨68724314660008256891825495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45816209773338837927883663 68724314660008256891825495)
        ·
          refine ⟨103086471990012385337738243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68724314660008256891825495 103086471990012385337738243)
          ·
            refine ⟨154629707985018578006607365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103086471990012385337738243 154629707985018578006607365)
            ·
              refine ⟨28993070247190983376238881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154629707985018578006607365 28993070247190983376238881)
              ·
                refine ⟨21744802685393237532179161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28993070247190983376238881 21744802685393237532179161)
                ·
                  refine ⟨16308602014044928149134371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21744802685393237532179161 16308602014044928149134371)
                  ·
                    refine ⟨24462903021067392223701557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16308602014044928149134371 24462903021067392223701557)
                    ·
                      refine ⟨2293397158225068020972021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24462903021067392223701557 2293397158225068020972021)
                      ·
                        rfl

theorem cell23_4466375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_4466375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466375 prefixEnd_4466375 := by exact prefixLift 4466375
  have htrace : WordTrace (prefixWord ++ tailWord_4466375) baseStart_4466375 baseEnd_4466375 := by
    simpa [prefixWord, tailWord_4466375, baseEnd_4466375] using wordTrace_append hprefix tailTrace_4466375
  have hstable : (prefixWord ++ tailWord_4466375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466375).length < 2 ^ (prefixWord ++ tailWord_4466375).sum := by decide
  have hdescent : baseEnd_4466375 < baseStart_4466375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466405 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 7]
def baseStart_4466405 : Nat := 118140960795 + 4466405 * 2 ^ 59
def prefixEnd_4466405 : Nat := 4983230072969 + 3 ^ 40 * 4466405 * 2
def baseEnd_4466405 : Nat := 2293412562644702903596883

theorem tailTrace_4466405 : CollatzResearch.WordTrace tailWord_4466405 prefixEnd_4466405 2293412562644702903596883 := by
  unfold tailWord_4466405
  simp only [CollatzResearch.WordTrace]
  refine ⟨162903173383984961089400669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108602115589323307392933779 162903173383984961089400669)
  ·
    refine ⟨61088690018994360408525251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162903173383984961089400669 61088690018994360408525251)
    ·
      refine ⟨91633035028491540612787877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61088690018994360408525251 91633035028491540612787877)
      ·
        refine ⟨17181194067842163864897727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91633035028491540612787877 17181194067842163864897727)
        ·
          refine ⟨25771791101763245797346591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17181194067842163864897727 25771791101763245797346591)
          ·
            refine ⟨38657686652644868696019887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25771791101763245797346591 38657686652644868696019887)
            ·
              refine ⟨57986529978967303044029831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38657686652644868696019887 57986529978967303044029831)
              ·
                refine ⟨86979794968450954566044747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57986529978967303044029831 86979794968450954566044747)
                ·
                  refine ⟨130469692452676431849067121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86979794968450954566044747 130469692452676431849067121)
                  ·
                    refine ⟨97852269339507323886800341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 130469692452676431849067121 97852269339507323886800341)
                    ·
                      refine ⟨2293412562644702903596883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97852269339507323886800341 2293412562644702903596883)
                      ·
                        rfl

theorem cell23_4466405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_4466405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466405 prefixEnd_4466405 := by exact prefixLift 4466405
  have htrace : WordTrace (prefixWord ++ tailWord_4466405) baseStart_4466405 baseEnd_4466405 := by
    simpa [prefixWord, tailWord_4466405, baseEnd_4466405] using wordTrace_append hprefix tailTrace_4466405
  have hstable : (prefixWord ++ tailWord_4466405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466405).length < 2 ^ (prefixWord ++ tailWord_4466405).sum := by decide
  have hdescent : baseEnd_4466405 < baseStart_4466405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466412 : List Nat := [2, 2, 1, 1, 2, 2, 2, 6, 5]
def baseStart_4466412 : Nat := 118140960795 + 4466412 * 2 ^ 59
def prefixEnd_4466412 : Nat := 4983230072969 + 3 ^ 40 * 4466412 * 2
def baseEnd_4466412 : Nat := 254824017445476041801039

theorem tailTrace_4466412 : CollatzResearch.WordTrace tailWord_4466412 prefixEnd_4466412 254824017445476041801039 := by
  unfold tailWord_4466412
  simp only [CollatzResearch.WordTrace]
  refine ⟨81451714347479800642452745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108602285796639734189936993 81451714347479800642452745)
  ·
    refine ⟨61088785760609850481839559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81451714347479800642452745 61088785760609850481839559)
    ·
      refine ⟨91633178640914775722759339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61088785760609850481839559 91633178640914775722759339)
      ·
        refine ⟨137449767961372163584139009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91633178640914775722759339 137449767961372163584139009)
        ·
          refine ⟨103087325971029122688104257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137449767961372163584139009 103087325971029122688104257)
          ·
            refine ⟨77315494478271842016078193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103087325971029122688104257 77315494478271842016078193)
            ·
              refine ⟨57986620858703881512058645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77315494478271842016078193 57986620858703881512058645)
              ·
                refine ⟨2718122852751744445877749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57986620858703881512058645 2718122852751744445877749)
                ·
                  refine ⟨254824017445476041801039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2718122852751744445877749 254824017445476041801039)
                  ·
                    rfl

theorem cell23_4466412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 5].length) (baseStart_4466412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466412 prefixEnd_4466412 := by exact prefixLift 4466412
  have htrace : WordTrace (prefixWord ++ tailWord_4466412) baseStart_4466412 baseEnd_4466412 := by
    simpa [prefixWord, tailWord_4466412, baseEnd_4466412] using wordTrace_append hprefix tailTrace_4466412
  have hstable : (prefixWord ++ tailWord_4466412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466412).length < 2 ^ (prefixWord ++ tailWord_4466412).sum := by decide
  have hdescent : baseEnd_4466412 < baseStart_4466412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466432 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 2, 5, 2]
def baseStart_4466432 : Nat := 118140960795 + 4466432 * 2 ^ 59
def prefixEnd_4466432 : Nat := 4983230072969 + 3 ^ 40 * 4466432 * 2
def baseEnd_4466432 : Nat := 2293426426622374297959259

theorem tailTrace_4466432 : CollatzResearch.WordTrace tailWord_4466432 prefixEnd_4466432 2293426426622374297959259 := by
  unfold tailWord_4466432
  simp only [CollatzResearch.WordTrace]
  refine ⟨81452079077443572350316775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108602772103258096467089033 81452079077443572350316775)
  ·
    refine ⟨122178118616165358525475163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81452079077443572350316775 122178118616165358525475163)
    ·
      refine ⟨183267177924248037788212745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122178118616165358525475163 183267177924248037788212745)
      ·
        refine ⟨137450383443186028341159559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183267177924248037788212745 137450383443186028341159559)
        ·
          refine ⟨206175575164779042511739339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137450383443186028341159559 206175575164779042511739339)
          ·
            refine ⟨309263362747168563767609009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206175575164779042511739339 309263362747168563767609009)
            ·
              refine ⟨231947522060376422825706757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309263362747168563767609009 231947522060376422825706757)
              ·
                refine ⟨43490160386320579279820017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231947522060376422825706757 43490160386320579279820017)
                ·
                  refine ⟨32617620289740434459865013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43490160386320579279820017 32617620289740434459865013)
                  ·
                    refine ⟨3057901902163165730612345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32617620289740434459865013 3057901902163165730612345)
                    ·
                      refine ⟨2293426426622374297959259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3057901902163165730612345 2293426426622374297959259)
                      ·
                        rfl

theorem cell23_4466432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2, 5, 2].length) (baseStart_4466432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466432 prefixEnd_4466432 := by exact prefixLift 4466432
  have htrace : WordTrace (prefixWord ++ tailWord_4466432) baseStart_4466432 baseEnd_4466432 := by
    simpa [prefixWord, tailWord_4466432, baseEnd_4466432] using wordTrace_append hprefix tailTrace_4466432
  have hstable : (prefixWord ++ tailWord_4466432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466432).length < 2 ^ (prefixWord ++ tailWord_4466432).sum := by decide
  have hdescent : baseEnd_4466432 < baseStart_4466432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466442 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 2, 5]
def baseStart_4466442 : Nat := 118140960795 + 4466442 * 2 ^ 59
def prefixEnd_4466442 : Nat := 4983230072969 + 3 ^ 40 * 4466442 * 2
def baseEnd_4466442 : Nat := 764477187142973086278071

theorem tailTrace_4466442 : CollatzResearch.WordTrace tailWord_4466442 prefixEnd_4466442 764477187142973086278071 := by
  unfold tailWord_4466442
  simp only [CollatzResearch.WordTrace]
  refine ⟨40726130721212729102124395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108603015256567277605665053 40726130721212729102124395)
  ·
    refine ⟨61089196081819093653186593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40726130721212729102124395 61089196081819093653186593)
    ·
      refine ⟨45816897061364320239889945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61089196081819093653186593 45816897061364320239889945)
      ·
        refine ⟨34362672796023240179917459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45816897061364320239889945 34362672796023240179917459)
        ·
          refine ⟨51544009194034860269876189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34362672796023240179917459 51544009194034860269876189)
          ·
            refine ⟨19329003447763072601203571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51544009194034860269876189 19329003447763072601203571)
            ·
              refine ⟨28993505171644608901805357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19329003447763072601203571 28993505171644608901805357)
              ·
                refine ⟨10872564439366728338177009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28993505171644608901805357 10872564439366728338177009)
                ·
                  refine ⟨8154423329525046253632757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10872564439366728338177009 8154423329525046253632757)
                  ·
                    refine ⟨764477187142973086278071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8154423329525046253632757 764477187142973086278071)
                    ·
                      rfl

theorem cell23_4466442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_4466442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466442 prefixEnd_4466442 := by exact prefixLift 4466442
  have htrace : WordTrace (prefixWord ++ tailWord_4466442) baseStart_4466442 baseEnd_4466442 := by
    simpa [prefixWord, tailWord_4466442, baseEnd_4466442] using wordTrace_append hprefix tailTrace_4466442
  have hstable : (prefixWord ++ tailWord_4466442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466442).length < 2 ^ (prefixWord ++ tailWord_4466442).sum := by decide
  have hdescent : baseEnd_4466442 < baseStart_4466442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466499 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 3]
def baseStart_4466499 : Nat := 118140960795 + 4466499 * 2 ^ 59
def prefixEnd_4466499 : Nat := 4983230072969 + 3 ^ 40 * 4466499 * 2
def baseEnd_4466499 : Nat := 2293460829826225535821451

theorem tailTrace_4466499 : CollatzResearch.WordTrace tailWord_4466499 prefixEnd_4466499 2293460829826225535821451 := by
  unfold tailWord_4466499
  simp only [CollatzResearch.WordTrace]
  refine ⟨162906601845644415143322551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108604401230429610095548367 162906601845644415143322551)
  ·
    refine ⟨244359902768466622714983827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162906601845644415143322551 244359902768466622714983827)
    ·
      refine ⟨366539854152699934072475741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244359902768466622714983827 366539854152699934072475741)
      ·
        refine ⟨137452445307262475277178403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 366539854152699934072475741 137452445307262475277178403)
        ·
          refine ⟨206178667960893712915767605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137452445307262475277178403 206178667960893712915767605)
          ·
            refine ⟨19329250121333785585853213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 206178667960893712915767605 19329250121333785585853213)
            ·
              refine ⟨7248468795500169594694955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19329250121333785585853213 7248468795500169594694955)
              ·
                refine ⟨10872703193250254392042433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7248468795500169594694955 10872703193250254392042433)
                ·
                  refine ⟨8154527394937690794031825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10872703193250254392042433 8154527394937690794031825)
                  ·
                    refine ⟨6115895546203268095523869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8154527394937690794031825 6115895546203268095523869)
                    ·
                      refine ⟨2293460829826225535821451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6115895546203268095523869 2293460829826225535821451)
                      ·
                        rfl

theorem cell23_4466499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_4466499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466499 prefixEnd_4466499 := by exact prefixLift 4466499
  have htrace : WordTrace (prefixWord ++ tailWord_4466499) baseStart_4466499 baseEnd_4466499 := by
    simpa [prefixWord, tailWord_4466499, baseEnd_4466499] using wordTrace_append hprefix tailTrace_4466499
  have hstable : (prefixWord ++ tailWord_4466499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466499).length < 2 ^ (prefixWord ++ tailWord_4466499).sum := by decide
  have hdescent : baseEnd_4466499 < baseStart_4466499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466506 : List Nat := [3, 1, 2, 1, 1, 1, 6, 3, 1, 4]
def baseStart_4466506 : Nat := 118140960795 + 4466506 * 2 ^ 59
def prefixEnd_4466506 : Nat := 4983230072969 + 3 ^ 40 * 4466506 * 2
def baseEnd_4466506 : Nat := 764488141396935669477973

theorem tailTrace_4466506 : CollatzResearch.WordTrace tailWord_4466506 prefixEnd_4466506 764488141396935669477973 := by
  unfold tailWord_4466506
  simp only [CollatzResearch.WordTrace]
  refine ⟨40726714289154763834706843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108604571437746036892551581 40726714289154763834706843)
  ·
    refine ⟨61090071433732145752060265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40726714289154763834706843 61090071433732145752060265)
    ·
      refine ⟨45817553575299109314045199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61090071433732145752060265 45817553575299109314045199)
      ·
        refine ⟨68726330362948663971067799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45817553575299109314045199 68726330362948663971067799)
        ·
          refine ⟨103089495544422995956601699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68726330362948663971067799 103089495544422995956601699)
          ·
            refine ⟨154634243316634493934902549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103089495544422995956601699 154634243316634493934902549)
            ·
              refine ⟨7248480155467241903198557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 154634243316634493934902549 7248480155467241903198557)
              ·
                refine ⟨2718180058300215713699459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7248480155467241903198557 2718180058300215713699459)
                ·
                  refine ⟨4077270087450323570549189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718180058300215713699459 4077270087450323570549189)
                  ·
                    refine ⟨764488141396935669477973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4077270087450323570549189 764488141396935669477973)
                    ·
                      rfl

theorem cell23_4466506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_4466506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466506 prefixEnd_4466506 := by exact prefixLift 4466506
  have htrace : WordTrace (prefixWord ++ tailWord_4466506) baseStart_4466506 baseEnd_4466506 := by
    simpa [prefixWord, tailWord_4466506, baseEnd_4466506] using wordTrace_append hprefix tailTrace_4466506
  have hstable : (prefixWord ++ tailWord_4466506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466506).length < 2 ^ (prefixWord ++ tailWord_4466506).sum := by decide
  have hdescent : baseEnd_4466506 < baseStart_4466506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466509 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_4466509 : Nat := 118140960795 + 4466509 * 2 ^ 59
def prefixEnd_4466509 : Nat := 4983230072969 + 3 ^ 40 * 4466509 * 2
def baseEnd_4466509 : Nat := 2293465964632770496696405

theorem tailTrace_4466509 : CollatzResearch.WordTrace tailWord_4466509 prefixEnd_4466509 2293465964632770496696405 := by
  unfold tailWord_4466509
  simp only [CollatzResearch.WordTrace]
  refine ⟨162906966575608186851186581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108604644383738791234124387 162906966575608186851186581)
  ·
    refine ⟨7636264058231633758649371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 162906966575608186851186581 7636264058231633758649371)
    ·
      refine ⟨11454396087347450637974057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7636264058231633758649371 11454396087347450637974057)
      ·
        refine ⟨8590797065510587978480543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11454396087347450637974057 8590797065510587978480543)
        ·
          refine ⟨12886195598265881967720815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8590797065510587978480543 12886195598265881967720815)
          ·
            refine ⟨19329293397398822951581223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12886195598265881967720815 19329293397398822951581223)
            ·
              refine ⟨28993940096098234427371835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19329293397398822951581223 28993940096098234427371835)
              ·
                refine ⟨43490910144147351641057753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28993940096098234427371835 43490910144147351641057753)
                ·
                  refine ⟨32618182608110513730793315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43490910144147351641057753 32618182608110513730793315)
                  ·
                    refine ⟨48927273912165770596189973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32618182608110513730793315 48927273912165770596189973)
                    ·
                      refine ⟨2293465964632770496696405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48927273912165770596189973 2293465964632770496696405)
                      ·
                        rfl

theorem cell23_4466509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_4466509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466509 prefixEnd_4466509 := by exact prefixLift 4466509
  have htrace : WordTrace (prefixWord ++ tailWord_4466509) baseStart_4466509 baseEnd_4466509 := by
    simpa [prefixWord, tailWord_4466509, baseEnd_4466509] using wordTrace_append hprefix tailTrace_4466509
  have hstable : (prefixWord ++ tailWord_4466509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466509).length < 2 ^ (prefixWord ++ tailWord_4466509).sum := by decide
  have hdescent : baseEnd_4466509 < baseStart_4466509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466552 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 7, 1, 4]
def baseStart_4466552 : Nat := 118140960795 + 4466552 * 2 ^ 59
def prefixEnd_4466552 : Nat := 4983230072969 + 3 ^ 40 * 4466552 * 2
def baseEnd_4466552 : Nat := 2293488044300913828458707

theorem tailTrace_4466552 : CollatzResearch.WordTrace tailWord_4466552 prefixEnd_4466552 2293488044300913828458707 := by
  unfold tailWord_4466552
  simp only [CollatzResearch.WordTrace]
  refine ⟨81454267457226202597500955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108605689942968270130001273 81454267457226202597500955)
  ·
    refine ⟨122181401185839303896251433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81454267457226202597500955 122181401185839303896251433)
    ·
      refine ⟨91636050889379477922188575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122181401185839303896251433 91636050889379477922188575)
      ·
        refine ⟨137454076334069216883282863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91636050889379477922188575 137454076334069216883282863)
        ·
          refine ⟨206181114501103825324924295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137454076334069216883282863 206181114501103825324924295)
          ·
            refine ⟨309271671751655737987386443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206181114501103825324924295 309271671751655737987386443)
            ·
              refine ⟨463907507627483606981079665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309271671751655737987386443 463907507627483606981079665)
              ·
                refine ⟨347930630720612705235809749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 463907507627483606981079665 347930630720612705235809749)
                ·
                  refine ⟨8154624157514360278964291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 347930630720612705235809749 8154624157514360278964291)
                  ·
                    refine ⟨12231936236271540418446437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8154624157514360278964291 12231936236271540418446437)
                    ·
                      refine ⟨2293488044300913828458707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12231936236271540418446437 2293488044300913828458707)
                      ·
                        rfl

theorem cell23_4466552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_4466552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466552 prefixEnd_4466552 := by exact prefixLift 4466552
  have htrace : WordTrace (prefixWord ++ tailWord_4466552) baseStart_4466552 baseEnd_4466552 := by
    simpa [prefixWord, tailWord_4466552, baseEnd_4466552] using wordTrace_append hprefix tailTrace_4466552
  have hstable : (prefixWord ++ tailWord_4466552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466552).length < 2 ^ (prefixWord ++ tailWord_4466552).sum := by decide
  have hdescent : baseEnd_4466552 < baseStart_4466552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466563 : List Nat := [1, 1, 1, 3, 4, 2, 3, 3, 1, 1, 3]
def baseStart_4466563 : Nat := 118140960795 + 4466563 * 2 ^ 59
def prefixEnd_4466563 : Nat := 4983230072969 + 3 ^ 40 * 4466563 * 2
def baseEnd_4466563 : Nat := 2293493692588113285421157

theorem tailTrace_4466563 : CollatzResearch.WordTrace tailWord_4466563 prefixEnd_4466563 2293493692588113285421157 := by
  unfold tailWord_4466563
  simp only [CollatzResearch.WordTrace]
  refine ⟨162908936117412554073652343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108605957411608369382434895 162908936117412554073652343)
  ·
    refine ⟨244363404176118831110478515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162908936117412554073652343 244363404176118831110478515)
    ·
      refine ⟨366545106264178246665717773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244363404176118831110478515 366545106264178246665717773)
      ·
        refine ⟨137454414849066842499644165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 366545106264178246665717773 137454414849066842499644165)
        ·
          refine ⟨25772702784200032968683281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137454414849066842499644165 25772702784200032968683281)
          ·
            refine ⟨19329527088150024726512461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25772702784200032968683281 19329527088150024726512461)
            ·
              refine ⟨7248572658056259272442173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19329527088150024726512461 7248572658056259272442173)
              ·
                refine ⟨2718214746771097227165815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7248572658056259272442173 2718214746771097227165815)
                ·
                  refine ⟨4077322120156645840748723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718214746771097227165815 4077322120156645840748723)
                  ·
                    refine ⟨6115983180234968761123085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4077322120156645840748723 6115983180234968761123085)
                    ·
                      refine ⟨2293493692588113285421157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6115983180234968761123085 2293493692588113285421157)
                      ·
                        rfl

theorem cell23_4466563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 1, 1, 3].length) (baseStart_4466563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466563 prefixEnd_4466563 := by exact prefixLift 4466563
  have htrace : WordTrace (prefixWord ++ tailWord_4466563) baseStart_4466563 baseEnd_4466563 := by
    simpa [prefixWord, tailWord_4466563, baseEnd_4466563] using wordTrace_append hprefix tailTrace_4466563
  have hstable : (prefixWord ++ tailWord_4466563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466563).length < 2 ^ (prefixWord ++ tailWord_4466563).sum := by decide
  have hdescent : baseEnd_4466563 < baseStart_4466563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466569 : List Nat := [1, 2, 1, 1, 5, 1, 1, 5, 1, 1, 4]
def baseStart_4466569 : Nat := 118140960795 + 4466569 * 2 ^ 59
def prefixEnd_4466569 : Nat := 4983230072969 + 3 ^ 40 * 4466569 * 2
def baseEnd_4466569 : Nat := 2293496773472040261946129

theorem tailTrace_4466569 : CollatzResearch.WordTrace tailWord_4466569 prefixEnd_4466569 2293496773472040261946129 := by
  unfold tailWord_4466569
  simp only [CollatzResearch.WordTrace]
  refine ⟨162909154955390817098370761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108606103303593878065580507 162909154955390817098370761)
  ·
    refine ⟨122181866216543112823778071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162909154955390817098370761 122181866216543112823778071)
    ·
      refine ⟨183272799324814669235667107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122181866216543112823778071 183272799324814669235667107)
      ·
        refine ⟨274909198987222003853500661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183272799324814669235667107 274909198987222003853500661)
        ·
          refine ⟨25772737405052062861265687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 274909198987222003853500661 25772737405052062861265687)
          ·
            refine ⟨38659106107578094291898531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25772737405052062861265687 38659106107578094291898531)
            ·
              refine ⟨57988659161367141437847797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38659106107578094291898531 57988659161367141437847797)
              ·
                refine ⟨5436436796378169509798231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57988659161367141437847797 5436436796378169509798231)
                ·
                  refine ⟨8154655194567254264697347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5436436796378169509798231 8154655194567254264697347)
                  ·
                    refine ⟨12231982791850881397046021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8154655194567254264697347 12231982791850881397046021)
                    ·
                      refine ⟨2293496773472040261946129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12231982791850881397046021 2293496773472040261946129)
                      ·
                        rfl

theorem cell23_4466569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 1, 4].length) (baseStart_4466569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466569 prefixEnd_4466569 := by exact prefixLift 4466569
  have htrace : WordTrace (prefixWord ++ tailWord_4466569) baseStart_4466569 baseEnd_4466569 := by
    simpa [prefixWord, tailWord_4466569, baseEnd_4466569] using wordTrace_append hprefix tailTrace_4466569
  have hstable : (prefixWord ++ tailWord_4466569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466569).length < 2 ^ (prefixWord ++ tailWord_4466569).sum := by decide
  have hdescent : baseEnd_4466569 < baseStart_4466569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466589 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_4466589 : Nat := 118140960795 + 4466589 * 2 ^ 59
def prefixEnd_4466589 : Nat := 4983230072969 + 3 ^ 40 * 4466589 * 2
def baseEnd_4466589 : Nat := 2293507043085130183696037

theorem tailTrace_4466589 : CollatzResearch.WordTrace tailWord_4466589 prefixEnd_4466589 2293507043085130183696037 := by
  unfold tailWord_4466589
  simp only [CollatzResearch.WordTrace]
  refine ⟨162909884415318360514098821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108606589610212240342732547 162909884415318360514098821)
  ·
    refine ⟨30545603327872192596393529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162909884415318360514098821 30545603327872192596393529)
    ·
      refine ⟨22909202495904144447295147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30545603327872192596393529 22909202495904144447295147)
      ·
        refine ⟨34363803743856216670942721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22909202495904144447295147 34363803743856216670942721)
        ·
          refine ⟨25772852807892162503207041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34363803743856216670942721 25772852807892162503207041)
          ·
            refine ⟨19329639605919121877405281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25772852807892162503207041 19329639605919121877405281)
            ·
              refine ⟨14497229704439341408053961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19329639605919121877405281 14497229704439341408053961)
              ·
                refine ⟨10872922278329506056040471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14497229704439341408053961 10872922278329506056040471)
                ·
                  refine ⟨16309383417494259084060707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10872922278329506056040471 16309383417494259084060707)
                  ·
                    refine ⟨24464075126241388626091061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16309383417494259084060707 24464075126241388626091061)
                    ·
                      refine ⟨2293507043085130183696037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24464075126241388626091061 2293507043085130183696037)
                      ·
                        rfl

theorem cell23_4466589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_4466589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466589 prefixEnd_4466589 := by exact prefixLift 4466589
  have htrace : WordTrace (prefixWord ++ tailWord_4466589) baseStart_4466589 baseEnd_4466589 := by
    simpa [prefixWord, tailWord_4466589, baseEnd_4466589] using wordTrace_append hprefix tailTrace_4466589
  have hstable : (prefixWord ++ tailWord_4466589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466589).length < 2 ^ (prefixWord ++ tailWord_4466589).sum := by decide
  have hdescent : baseEnd_4466589 < baseStart_4466589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466596 : List Nat := [2, 3, 1, 2, 1, 4, 1, 3, 2, 4]
def baseStart_4466596 : Nat := 118140960795 + 4466596 * 2 ^ 59
def prefixEnd_4466596 : Nat := 4983230072969 + 3 ^ 40 * 4466596 * 2
def baseEnd_4466596 : Nat := 764503545816570552102835

theorem tailTrace_4466596 : CollatzResearch.WordTrace tailWord_4466596 prefixEnd_4466596 764503545816570552102835 := by
  unfold tailWord_4466596
  simp only [CollatzResearch.WordTrace]
  refine ⟨81455069863146500354801821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108606759817528667139735761 81455069863146500354801821)
  ·
    refine ⟨30545651198679937633050683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81455069863146500354801821 30545651198679937633050683)
    ·
      refine ⟨45818476798019906449576025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30545651198679937633050683 45818476798019906449576025)
      ·
        refine ⟨34363857598514929837182019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45818476798019906449576025 34363857598514929837182019)
        ·
          refine ⟨51545786397772394755773029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34363857598514929837182019 51545786397772394755773029)
          ·
            refine ⟨9664834949582324016707443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51545786397772394755773029 9664834949582324016707443)
            ·
              refine ⟨14497252424373486025061165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9664834949582324016707443 14497252424373486025061165)
              ·
                refine ⟨5436469659140057259397937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14497252424373486025061165 5436469659140057259397937)
                ·
                  refine ⟨4077352244355042944548453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5436469659140057259397937 4077352244355042944548453)
                  ·
                    refine ⟨764503545816570552102835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4077352244355042944548453 764503545816570552102835)
                    ·
                      rfl

theorem cell23_4466596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_4466596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466596 prefixEnd_4466596 := by exact prefixLift 4466596
  have htrace : WordTrace (prefixWord ++ tailWord_4466596) baseStart_4466596 baseEnd_4466596 := by
    simpa [prefixWord, tailWord_4466596, baseEnd_4466596] using wordTrace_append hprefix tailTrace_4466596
  have hstable : (prefixWord ++ tailWord_4466596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466596).length < 2 ^ (prefixWord ++ tailWord_4466596).sum := by decide
  have hdescent : baseEnd_4466596 < baseStart_4466596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466599 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_4466599 : Nat := 118140960795 + 4466599 * 2 ^ 59
def prefixEnd_4466599 : Nat := 4983230072969 + 3 ^ 40 * 4466599 * 2
def baseEnd_4466599 : Nat := 2293512177891675144570991

theorem tailTrace_4466599 : CollatzResearch.WordTrace tailWord_4466599 prefixEnd_4466599 2293512177891675144570991 := by
  unfold tailWord_4466599
  simp only [CollatzResearch.WordTrace]
  refine ⟨162910249145282132221962851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108606832763521421481308567 162910249145282132221962851)
  ·
    refine ⟨244365373717923198332944277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162910249145282132221962851 244365373717923198332944277)
    ·
      refine ⟨11454626893027649921856763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 244365373717923198332944277 11454626893027649921856763)
      ·
        refine ⟨17181940339541474882785145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11454626893027649921856763 17181940339541474882785145)
        ·
          refine ⟨12886455254656106162088859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17181940339541474882785145 12886455254656106162088859)
          ·
            refine ⟨19329682881984159243133289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12886455254656106162088859 19329682881984159243133289)
            ·
              refine ⟨14497262161488119432349967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19329682881984159243133289 14497262161488119432349967)
              ·
                refine ⟨21745893242232179148524951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14497262161488119432349967 21745893242232179148524951)
                ·
                  refine ⟨32618839863348268722787427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21745893242232179148524951 32618839863348268722787427)
                  ·
                    refine ⟨48928259795022403084181141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32618839863348268722787427 48928259795022403084181141)
                    ·
                      refine ⟨2293512177891675144570991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48928259795022403084181141 2293512177891675144570991)
                      ·
                        rfl

theorem cell23_4466599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_4466599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466599 prefixEnd_4466599 := by exact prefixLift 4466599
  have htrace : WordTrace (prefixWord ++ tailWord_4466599) baseStart_4466599 baseEnd_4466599 := by
    simpa [prefixWord, tailWord_4466599, baseEnd_4466599] using wordTrace_append hprefix tailTrace_4466599
  have hstable : (prefixWord ++ tailWord_4466599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466599).length < 2 ^ (prefixWord ++ tailWord_4466599).sum := by decide
  have hdescent : baseEnd_4466599 < baseStart_4466599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466600 : List Nat := [2, 1, 6, 2, 1, 2, 1, 2, 1, 5]
def baseStart_4466600 : Nat := 118140960795 + 4466600 * 2 ^ 59
def prefixEnd_4466600 : Nat := 4983230072969 + 3 ^ 40 * 4466600 * 2
def baseEnd_4466600 : Nat := 764504230457443213552829

theorem tailTrace_4466600 : CollatzResearch.WordTrace tailWord_4466600 prefixEnd_4466600 764504230457443213552829 := by
  unfold tailWord_4466600
  simp only [CollatzResearch.WordTrace]
  refine ⟨81455142809139254696374627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108606857078852339595166169 81455142809139254696374627)
  ·
    refine ⟨122182714213708882044561941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81455142809139254696374627 122182714213708882044561941)
    ·
      refine ⟨5727314728767603845838841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 122182714213708882044561941 5727314728767603845838841)
      ·
        refine ⟨4295486046575702884379131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5727314728767603845838841 4295486046575702884379131)
        ·
          refine ⟨6443229069863554326568697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4295486046575702884379131 6443229069863554326568697)
          ·
            refine ⟨4832421802397665744926523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6443229069863554326568697 4832421802397665744926523)
            ·
              refine ⟨7248632703596498617389785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4832421802397665744926523 7248632703596498617389785)
              ·
                refine ⟨5436474527697373963042339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7248632703596498617389785 5436474527697373963042339)
                ·
                  refine ⟨8154711791546060944563509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5436474527697373963042339 8154711791546060944563509)
                  ·
                    refine ⟨764504230457443213552829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8154711791546060944563509 764504230457443213552829)
                    ·
                      rfl

theorem cell23_4466600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_4466600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466600 prefixEnd_4466600 := by exact prefixLift 4466600
  have htrace : WordTrace (prefixWord ++ tailWord_4466600) baseStart_4466600 baseEnd_4466600 := by
    simpa [prefixWord, tailWord_4466600, baseEnd_4466600] using wordTrace_append hprefix tailTrace_4466600
  have hstable : (prefixWord ++ tailWord_4466600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466600).length < 2 ^ (prefixWord ++ tailWord_4466600).sum := by decide
  have hdescent : baseEnd_4466600 < baseStart_4466600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466620 : List Nat := [2, 2, 2, 5, 1, 1, 3, 1, 1, 1, 4]
def baseStart_4466620 : Nat := 118140960795 + 4466620 * 2 ^ 59
def prefixEnd_4466620 : Nat := 4983230072969 + 3 ^ 40 * 4466620 * 2
def baseEnd_4466620 : Nat := 2293522960985419562408395

theorem tailTrace_4466620 : CollatzResearch.WordTrace tailWord_4466620 prefixEnd_4466620 2293522960985419562408395 := by
  unfold tailWord_4466620
  simp only [CollatzResearch.WordTrace]
  refine ⟨81455507539103026404238657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108607343385470701872318209 81455507539103026404238657)
  ·
    refine ⟨61091630654327269803178993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81455507539103026404238657 61091630654327269803178993)
    ·
      refine ⟨45818722990745452352384245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61091630654327269803178993 45818722990745452352384245)
      ·
        refine ⟨4295505280382386158036023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45818722990745452352384245 4295505280382386158036023)
        ·
          refine ⟨6443257920573579237054035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4295505280382386158036023 6443257920573579237054035)
          ·
            refine ⟨9664886880860368855581053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6443257920573579237054035 9664886880860368855581053)
            ·
              refine ⟨3624332580322638320842895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9664886880860368855581053 3624332580322638320842895)
              ·
                refine ⟨5436498870483957481264343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3624332580322638320842895 5436498870483957481264343)
                ·
                  refine ⟨8154748305725936221896515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5436498870483957481264343 8154748305725936221896515)
                  ·
                    refine ⟨12232122458588904332844773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8154748305725936221896515 12232122458588904332844773)
                    ·
                      refine ⟨2293522960985419562408395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12232122458588904332844773 2293522960985419562408395)
                      ·
                        rfl

theorem cell23_4466620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_4466620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466620 prefixEnd_4466620 := by exact prefixLift 4466620
  have htrace : WordTrace (prefixWord ++ tailWord_4466620) baseStart_4466620 baseEnd_4466620 := by
    simpa [prefixWord, tailWord_4466620, baseEnd_4466620] using wordTrace_append hprefix tailTrace_4466620
  have hstable : (prefixWord ++ tailWord_4466620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466620).length < 2 ^ (prefixWord ++ tailWord_4466620).sum := by decide
  have hdescent : baseEnd_4466620 < baseStart_4466620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466653 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_4466653 : Nat := 118140960795 + 4466653 * 2 ^ 59
def prefixEnd_4466653 : Nat := 4983230072969 + 3 ^ 40 * 4466653 * 2
def baseEnd_4466653 : Nat := 2293539905847017933295743

theorem tailTrace_4466653 : CollatzResearch.WordTrace tailWord_4466653 prefixEnd_4466653 2293539905847017933295743 := by
  unfold tailWord_4466653
  simp only [CollatzResearch.WordTrace]
  refine ⟨162912218687086499444428613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108608145791390999629619075 162912218687086499444428613)
  ·
    refine ⟨30546041003828718645830365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162912218687086499444428613 30546041003828718645830365)
    ·
      refine ⟨11454765376435769492186387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30546041003828718645830365 11454765376435769492186387)
      ·
        refine ⟨17182148064653654238279581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11454765376435769492186387 17182148064653654238279581)
        ·
          refine ⟨6443305524245120339354843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17182148064653654238279581 6443305524245120339354843)
          ·
            refine ⟨9664958286367680509032265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6443305524245120339354843 9664958286367680509032265)
            ·
              refine ⟨7248718714775760381774199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9664958286367680509032265 7248718714775760381774199)
              ·
                refine ⟨10873078072163640572661299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7248718714775760381774199 10873078072163640572661299)
                ·
                  refine ⟨16309617108245460858991949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10873078072163640572661299 16309617108245460858991949)
                  ·
                    refine ⟨6116106415592047822121981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16309617108245460858991949 6116106415592047822121981)
                    ·
                      refine ⟨2293539905847017933295743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6116106415592047822121981 2293539905847017933295743)
                      ·
                        rfl

theorem cell23_4466653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_4466653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466653 prefixEnd_4466653 := by exact prefixLift 4466653
  have htrace : WordTrace (prefixWord ++ tailWord_4466653) baseStart_4466653 baseEnd_4466653 := by
    simpa [prefixWord, tailWord_4466653, baseEnd_4466653] using wordTrace_append hprefix tailTrace_4466653
  have hstable : (prefixWord ++ tailWord_4466653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466653).length < 2 ^ (prefixWord ++ tailWord_4466653).sum := by decide
  have hdescent : baseEnd_4466653 < baseStart_4466653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466686 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_4466686 : Nat := 118140960795 + 4466686 * 2 ^ 59
def prefixEnd_4466686 : Nat := 4983230072969 + 3 ^ 40 * 4466686 * 2
def baseEnd_4466686 : Nat := 764518950236205434727697

theorem tailTrace_4466686 : CollatzResearch.WordTrace tailWord_4466686 prefixEnd_4466686 764518950236205434727697 := by
  unfold tailWord_4466686
  simp only [CollatzResearch.WordTrace]
  refine ⟨20364177786995868260047489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108608948197311297386919941 20364177786995868260047489)
  ·
    refine ⟨15273133340246901195035617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20364177786995868260047489 15273133340246901195035617)
    ·
      refine ⟨11454850005185175896276713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15273133340246901195035617 11454850005185175896276713)
      ·
        refine ⟨8591137503888881922207535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11454850005185175896276713 8591137503888881922207535)
        ·
          refine ⟨12886706255833322883311303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8591137503888881922207535 12886706255833322883311303)
          ·
            refine ⟨19330059383749984324966955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12886706255833322883311303 19330059383749984324966955)
            ·
              refine ⟨28995089075624976487450433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19330059383749984324966955 28995089075624976487450433)
              ·
                refine ⟨21746316806718732365587825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28995089075624976487450433 21746316806718732365587825)
                ·
                  refine ⟨16309737605039049274190869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21746316806718732365587825 16309737605039049274190869)
                  ·
                    refine ⟨764518950236205434727697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16309737605039049274190869 764518950236205434727697)
                    ·
                      rfl

theorem cell23_4466686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_4466686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466686 prefixEnd_4466686 := by exact prefixLift 4466686
  have htrace : WordTrace (prefixWord ++ tailWord_4466686) baseStart_4466686 baseEnd_4466686 := by
    simpa [prefixWord, tailWord_4466686, baseEnd_4466686] using wordTrace_append hprefix tailTrace_4466686
  have hstable : (prefixWord ++ tailWord_4466686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466686).length < 2 ^ (prefixWord ++ tailWord_4466686).sum := by decide
  have hdescent : baseEnd_4466686 < baseStart_4466686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466689 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_4466689 : Nat := 118140960795 + 4466689 * 2 ^ 59
def prefixEnd_4466689 : Nat := 4983230072969 + 3 ^ 40 * 4466689 * 2
def baseEnd_4466689 : Nat := 2293558391150579792445577

theorem tailTrace_4466689 : CollatzResearch.WordTrace tailWord_4466689 prefixEnd_4466689 2293558391150579792445577 := by
  unfold tailWord_4466689
  simp only [CollatzResearch.WordTrace]
  refine ⟨162913531714956077592739121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108609021143304051728492747 162913531714956077592739121)
  ·
    refine ⟨122185148786217058194554341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162913531714956077592739121 122185148786217058194554341)
    ·
      refine ⟨22909715397415698411478939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122185148786217058194554341 22909715397415698411478939)
      ·
        refine ⟨34364573096123547617218409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22909715397415698411478939 34364573096123547617218409)
        ·
          refine ⟨25773429822092660712913807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34364573096123547617218409 25773429822092660712913807)
          ·
            refine ⟨38660144733138991069370711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25773429822092660712913807 38660144733138991069370711)
            ·
              refine ⟨57990217099708486604056067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38660144733138991069370711 57990217099708486604056067)
              ·
                refine ⟨86985325649562729906084101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57990217099708486604056067 86985325649562729906084101)
                ·
                  refine ⟨16309748559293011857390769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86985325649562729906084101 16309748559293011857390769)
                  ·
                    refine ⟨12232311419469758893043077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16309748559293011857390769 12232311419469758893043077)
                    ·
                      refine ⟨2293558391150579792445577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12232311419469758893043077 2293558391150579792445577)
                      ·
                        rfl

theorem cell23_4466689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_4466689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466689 prefixEnd_4466689 := by exact prefixLift 4466689
  have htrace : WordTrace (prefixWord ++ tailWord_4466689) baseStart_4466689 baseEnd_4466689 := by
    simpa [prefixWord, tailWord_4466689, baseEnd_4466689] using wordTrace_append hprefix tailTrace_4466689
  have hstable : (prefixWord ++ tailWord_4466689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466689).length < 2 ^ (prefixWord ++ tailWord_4466689).sum := by decide
  have hdescent : baseEnd_4466689 < baseStart_4466689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466693 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 4, 2, 2]
def baseStart_4466693 : Nat := 118140960795 + 4466693 * 2 ^ 59
def prefixEnd_4466693 : Nat := 4983230072969 + 3 ^ 40 * 4466693 * 2
def baseEnd_4466693 : Nat := 2293560445073197776795559

theorem tailTrace_4466693 : CollatzResearch.WordTrace tailWord_4466693 prefixEnd_4466693 2293560445073197776795559 := by
  unfold tailWord_4466693
  simp only [CollatzResearch.WordTrace]
  refine ⟨162913677606941586275884733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108609118404627724183923155 162913677606941586275884733)
  ·
    refine ⟨61092629102603094853456775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162913677606941586275884733 61092629102603094853456775)
    ·
      refine ⟨91638943653904642280185163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61092629102603094853456775 91638943653904642280185163)
      ·
        refine ⟨137458415480856963420277745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91638943653904642280185163 137458415480856963420277745)
        ·
          refine ⟨103093811610642722565208309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137458415480856963420277745 103093811610642722565208309)
          ·
            refine ⟨9665044838497755240488279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103093811610642722565208309 9665044838497755240488279)
            ·
              refine ⟨14497567257746632860732419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9665044838497755240488279 14497567257746632860732419)
              ·
                refine ⟨21746350886619949291098629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14497567257746632860732419 21746350886619949291098629)
                ·
                  refine ⟨4077440791241240492080993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21746350886619949291098629 4077440791241240492080993)
                  ·
                    refine ⟨3058080593430930369060745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4077440791241240492080993 3058080593430930369060745)
                    ·
                      refine ⟨2293560445073197776795559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3058080593430930369060745 2293560445073197776795559)
                      ·
                        rfl

theorem cell23_4466693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 2, 2].length) (baseStart_4466693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466693 prefixEnd_4466693 := by exact prefixLift 4466693
  have htrace : WordTrace (prefixWord ++ tailWord_4466693) baseStart_4466693 baseEnd_4466693 := by
    simpa [prefixWord, tailWord_4466693, baseEnd_4466693] using wordTrace_append hprefix tailTrace_4466693
  have hstable : (prefixWord ++ tailWord_4466693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466693).length < 2 ^ (prefixWord ++ tailWord_4466693).sum := by decide
  have hdescent : baseEnd_4466693 < baseStart_4466693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466699 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 7]
def baseStart_4466699 : Nat := 118140960795 + 4466699 * 2 ^ 59
def prefixEnd_4466699 : Nat := 4983230072969 + 3 ^ 40 * 4466699 * 2
def baseEnd_4466699 : Nat := 254840391773013861480059

theorem tailTrace_4466699 : CollatzResearch.WordTrace tailWord_4466699 prefixEnd_4466699 254840391773013861480059 := by
  unfold tailWord_4466699
  simp only [CollatzResearch.WordTrace]
  refine ⟨162913896444919849300603151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108609264296613232867068767 162913896444919849300603151)
  ·
    refine ⟨244370844667379773950904727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162913896444919849300603151 244370844667379773950904727)
    ·
      refine ⟨366556267001069660926357091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244370844667379773950904727 366556267001069660926357091)
      ·
        refine ⟨549834400501604491389535637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366556267001069660926357091 549834400501604491389535637)
        ·
          refine ⟨25773487523512710533884483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 549834400501604491389535637 25773487523512710533884483)
          ·
            refine ⟨38660231285269065800826725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25773487523512710533884483 38660231285269065800826725)
            ·
              refine ⟨7248793365987949837655011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38660231285269065800826725 7248793365987949837655011)
              ·
                refine ⟨10873190048981924756482517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7248793365987949837655011 10873190048981924756482517)
                ·
                  refine ⟨254840391773013861480059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10873190048981924756482517 254840391773013861480059)
                  ·
                    rfl

theorem cell23_4466699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 7].length) (baseStart_4466699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466699 prefixEnd_4466699 := by exact prefixLift 4466699
  have htrace : WordTrace (prefixWord ++ tailWord_4466699) baseStart_4466699 baseEnd_4466699 := by
    simpa [prefixWord, tailWord_4466699, baseEnd_4466699] using wordTrace_append hprefix tailTrace_4466699
  have hstable : (prefixWord ++ tailWord_4466699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466699).length < 2 ^ (prefixWord ++ tailWord_4466699).sum := by decide
  have hdescent : baseEnd_4466699 < baseStart_4466699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466750 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 7]
def baseStart_4466750 : Nat := 118140960795 + 4466750 * 2 ^ 59
def prefixEnd_4466750 : Nat := 4983230072969 + 3 ^ 40 * 4466750 * 2
def baseEnd_4466750 : Nat := 254843301496722672642533

theorem tailTrace_4466750 : CollatzResearch.WordTrace tailWord_4466750 prefixEnd_4466750 254843301496722672642533 := by
  unfold tailWord_4466750
  simp only [CollatzResearch.WordTrace]
  refine ⟨20364469570966885626338713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108610504378490056673806469 20364469570966885626338713)
  ·
    refine ⟨15273352178225164219754035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20364469570966885626338713 15273352178225164219754035)
    ·
      refine ⟨22910028267337746329631053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15273352178225164219754035 22910028267337746329631053)
      ·
        refine ⟨8591260600251654873611645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22910028267337746329631053 8591260600251654873611645)
        ·
          refine ⟨3221722725094370577604367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8591260600251654873611645 3221722725094370577604367)
          ·
            refine ⟨4832584087641555866406551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3221722725094370577604367 4832584087641555866406551)
            ·
              refine ⟨7248876131462333799609827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4832584087641555866406551 7248876131462333799609827)
              ·
                refine ⟨10873314197193500699414741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7248876131462333799609827 10873314197193500699414741)
                ·
                  refine ⟨254843301496722672642533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10873314197193500699414741 254843301496722672642533)
                  ·
                    rfl

theorem cell23_4466750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_4466750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466750 prefixEnd_4466750 := by exact prefixLift 4466750
  have htrace : WordTrace (prefixWord ++ tailWord_4466750) baseStart_4466750 baseEnd_4466750 := by
    simpa [prefixWord, tailWord_4466750, baseEnd_4466750] using wordTrace_append hprefix tailTrace_4466750
  have hstable : (prefixWord ++ tailWord_4466750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466750).length < 2 ^ (prefixWord ++ tailWord_4466750).sum := by decide
  have hdescent : baseEnd_4466750 < baseStart_4466750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466793 : List Nat := [1, 2, 1, 1, 1, 5, 2, 5, 1, 4]
def baseStart_4466793 : Nat := 118140960795 + 4466793 * 2 ^ 59
def prefixEnd_4466793 : Nat := 4983230072969 + 3 ^ 40 * 4466793 * 2
def baseEnd_4466793 : Nat := 764537264379549128515033

theorem tailTrace_4466793 : CollatzResearch.WordTrace tailWord_4466793 prefixEnd_4466793 764537264379549128515033 := by
  unfold tailWord_4466793
  simp only [CollatzResearch.WordTrace]
  refine ⟨162917324906579303354525033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108611549937719535569683355 162917324906579303354525033)
  ·
    refine ⟨122187993679934477515893775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162917324906579303354525033 122187993679934477515893775)
    ·
      refine ⟨183281990519901716273840663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122187993679934477515893775 183281990519901716273840663)
      ·
        refine ⟨274922985779852574410760995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183281990519901716273840663 274922985779852574410760995)
        ·
          refine ⟨412384478669778861616141493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274922985779852574410760995 412384478669778861616141493)
          ·
            refine ⟨38661044875291768276513265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 412384478669778861616141493 38661044875291768276513265)
            ·
              refine ⟨28995783656468826207384949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38661044875291768276513265 28995783656468826207384949)
              ·
                refine ⟨2718354717793952456942339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28995783656468826207384949 2718354717793952456942339)
                ·
                  refine ⟨4077532076690928685413509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718354717793952456942339 4077532076690928685413509)
                  ·
                    refine ⟨764537264379549128515033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4077532076690928685413509 764537264379549128515033)
                    ·
                      rfl

theorem cell23_4466793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 1, 4].length) (baseStart_4466793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466793 prefixEnd_4466793 := by exact prefixLift 4466793
  have htrace : WordTrace (prefixWord ++ tailWord_4466793) baseStart_4466793 baseEnd_4466793 := by
    simpa [prefixWord, tailWord_4466793, baseEnd_4466793] using wordTrace_append hprefix tailTrace_4466793
  have hstable : (prefixWord ++ tailWord_4466793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466793).length < 2 ^ (prefixWord ++ tailWord_4466793).sum := by decide
  have hdescent : baseEnd_4466793 < baseStart_4466793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466879 : List Nat := [1, 1, 2, 2, 2, 2, 1, 12]
def baseStart_4466879 : Nat := 118140960795 + 4466879 * 2 ^ 59
def prefixEnd_4466879 : Nat := 4983230072969 + 3 ^ 40 * 4466879 * 2
def baseEnd_4466879 : Nat := 84950220462034594409989

theorem tailTrace_4466879 : CollatzResearch.WordTrace tailWord_4466879 prefixEnd_4466879 84950220462034594409989 := by
  unfold tailWord_4466879
  simp only [CollatzResearch.WordTrace]
  refine ⟨162920461584267740042155691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108613641056178493361437127 162920461584267740042155691)
  ·
    refine ⟨244380692376401610063233537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162920461584267740042155691 244380692376401610063233537)
    ·
      refine ⟨183285519282301207547425153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244380692376401610063233537 183285519282301207547425153)
      ·
        refine ⟨137464139461725905660568865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183285519282301207547425153 137464139461725905660568865)
        ·
          refine ⟨103098104596294429245426649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137464139461725905660568865 103098104596294429245426649)
          ·
            refine ⟨77323578447220821934069987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103098104596294429245426649 77323578447220821934069987)
            ·
              refine ⟨115985367670831232901104981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77323578447220821934069987 115985367670831232901104981)
              ·
                refine ⟨84950220462034594409989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 115985367670831232901104981 84950220462034594409989)
                ·
                  rfl

theorem cell23_4466879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 12].length) (baseStart_4466879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466879 prefixEnd_4466879 := by exact prefixLift 4466879
  have htrace : WordTrace (prefixWord ++ tailWord_4466879) baseStart_4466879 baseEnd_4466879 := by
    simpa [prefixWord, tailWord_4466879, baseEnd_4466879] using wordTrace_append hprefix tailTrace_4466879
  have hstable : (prefixWord ++ tailWord_4466879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466879).length < 2 ^ (prefixWord ++ tailWord_4466879).sum := by decide
  have hdescent : baseEnd_4466879 < baseStart_4466879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466890 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 3, 2, 2]
def baseStart_4466890 : Nat := 118140960795 + 4466890 * 2 ^ 59
def prefixEnd_4466890 : Nat := 4983230072969 + 3 ^ 40 * 4466890 * 2
def baseEnd_4466890 : Nat := 2293661600762133506032153

theorem tailTrace_4466890 : CollatzResearch.WordTrace tailWord_4466890 prefixEnd_4466890 2293661600762133506032153 := by
  unfold tailWord_4466890
  simp only [CollatzResearch.WordTrace]
  refine ⟨40730215696806972230201531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108613908524818592613870749 40730215696806972230201531)
  ·
    refine ⟨61095323545210458345302297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40730215696806972230201531 61095323545210458345302297)
    ·
      refine ⟨45821492658907843758976723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61095323545210458345302297 45821492658907843758976723)
      ·
        refine ⟨68732238988361765638465085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45821492658907843758976723 68732238988361765638465085)
        ·
          refine ⟨25774589620635662114424407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68732238988361765638465085 25774589620635662114424407)
          ·
            refine ⟨38661884430953493171636611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25774589620635662114424407 38661884430953493171636611)
            ·
              refine ⟨57992826646430239757454917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38661884430953493171636611 57992826646430239757454917)
              ·
                refine ⟨10873654996205669954522797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57992826646430239757454917 10873654996205669954522797)
                ·
                  refine ⟨4077620623577126232946049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10873654996205669954522797 4077620623577126232946049)
                  ·
                    refine ⟨3058215467682844674709537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4077620623577126232946049 3058215467682844674709537)
                    ·
                      refine ⟨2293661600762133506032153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3058215467682844674709537 2293661600762133506032153)
                      ·
                        rfl

theorem cell23_4466890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_4466890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466890 prefixEnd_4466890 := by exact prefixLift 4466890
  have htrace : WordTrace (prefixWord ++ tailWord_4466890) baseStart_4466890 baseEnd_4466890 := by
    simpa [prefixWord, tailWord_4466890, baseEnd_4466890] using wordTrace_append hprefix tailTrace_4466890
  have hstable : (prefixWord ++ tailWord_4466890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466890).length < 2 ^ (prefixWord ++ tailWord_4466890).sum := by decide
  have hdescent : baseEnd_4466890 < baseStart_4466890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466901 : List Nat := [1, 3, 2, 4, 3, 1, 1, 3, 1, 1, 3]
def baseStart_4466901 : Nat := 118140960795 + 4466901 * 2 ^ 59
def prefixEnd_4466901 : Nat := 4983230072969 + 3 ^ 40 * 4466901 * 2
def baseEnd_4466901 : Nat := 2293667249049332962994603

theorem tailTrace_4466901 : CollatzResearch.WordTrace tailWord_4466901 prefixEnd_4466901 2293667249049332962994603 := by
  unfold tailWord_4466901
  simp only [CollatzResearch.WordTrace]
  refine ⟨162921263990188037799456557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108614175993458691866304371 162921263990188037799456557)
  ·
    refine ⟨61095473996320514174796209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162921263990188037799456557 61095473996320514174796209)
    ·
      refine ⟨45821605497240385631097157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61095473996320514174796209 45821605497240385631097157)
      ·
        refine ⟨8591551030732572305830717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45821605497240385631097157 8591551030732572305830717)
        ·
          refine ⟨3221831636524714614686519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8591551030732572305830717 3221831636524714614686519)
          ·
            refine ⟨4832747454787071922029779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3221831636524714614686519 4832747454787071922029779)
            ·
              refine ⟨7249121182180607883044669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4832747454787071922029779 7249121182180607883044669)
              ·
                refine ⟨2718420443317727956141751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7249121182180607883044669 2718420443317727956141751)
                ·
                  refine ⟨4077630664976591934212627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718420443317727956141751 4077630664976591934212627)
                  ·
                    refine ⟨6116445997464887901318941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4077630664976591934212627 6116445997464887901318941)
                    ·
                      refine ⟨2293667249049332962994603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6116445997464887901318941 2293667249049332962994603)
                      ·
                        rfl

theorem cell23_4466901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_4466901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466901 prefixEnd_4466901 := by exact prefixLift 4466901
  have htrace : WordTrace (prefixWord ++ tailWord_4466901) baseStart_4466901 baseEnd_4466901 := by
    simpa [prefixWord, tailWord_4466901, baseEnd_4466901] using wordTrace_append hprefix tailTrace_4466901
  have hstable : (prefixWord ++ tailWord_4466901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466901).length < 2 ^ (prefixWord ++ tailWord_4466901).sum := by decide
  have hdescent : baseEnd_4466901 < baseStart_4466901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466923 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 4, 1, 3]
def baseStart_4466923 : Nat := 118140960795 + 4466923 * 2 ^ 59
def prefixEnd_4466923 : Nat := 4983230072969 + 3 ^ 40 * 4466923 * 2
def baseEnd_4466923 : Nat := 2293678545623731876919501

theorem tailTrace_4466923 : CollatzResearch.WordTrace tailWord_4466923 prefixEnd_4466923 2293678545623731876919501 := by
  unfold tailWord_4466923
  simp only [CollatzResearch.WordTrace]
  refine ⟨162922066396108335556757423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108614710930738890371171615 162922066396108335556757423)
  ·
    refine ⟨244383099594162503335136135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162922066396108335556757423 244383099594162503335136135)
    ·
      refine ⟨366574649391243755002704203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244383099594162503335136135 366574649391243755002704203)
      ·
        refine ⟨549861974086865632504056305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366574649391243755002704203 549861974086865632504056305)
        ·
          refine ⟨412396480565149224378042229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 549861974086865632504056305 412396480565149224378042229)
          ·
            refine ⟨38662170052982739785441459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 412396480565149224378042229 38662170052982739785441459)
            ·
              refine ⟨57993255079474109678162189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38662170052982739785441459 57993255079474109678162189)
              ·
                refine ⟨21747470654802791129310821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57993255079474109678162189 21747470654802791129310821)
                ·
                  refine ⟨4077650747775523336745779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21747470654802791129310821 4077650747775523336745779)
                  ·
                    refine ⟨6116476121663285005118669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4077650747775523336745779 6116476121663285005118669)
                    ·
                      refine ⟨2293678545623731876919501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6116476121663285005118669 2293678545623731876919501)
                      ·
                        rfl

theorem cell23_4466923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 1, 3].length) (baseStart_4466923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466923 prefixEnd_4466923 := by exact prefixLift 4466923
  have htrace : WordTrace (prefixWord ++ tailWord_4466923) baseStart_4466923 baseEnd_4466923 := by
    simpa [prefixWord, tailWord_4466923, baseEnd_4466923] using wordTrace_append hprefix tailTrace_4466923
  have hstable : (prefixWord ++ tailWord_4466923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466923).length < 2 ^ (prefixWord ++ tailWord_4466923).sum := by decide
  have hdescent : baseEnd_4466923 < baseStart_4466923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466924 : List Nat := [2, 2, 1, 1, 2, 3, 5, 2, 1, 2, 2]
def baseStart_4466924 : Nat := 118140960795 + 4466924 * 2 ^ 59
def prefixEnd_4466924 : Nat := 4983230072969 + 3 ^ 40 * 4466924 * 2
def baseEnd_4466924 : Nat := 2293679059104386373006997

theorem tailTrace_4466924 : CollatzResearch.WordTrace tailWord_4466924 prefixEnd_4466924 2293679059104386373006997 := by
  unfold tailWord_4466924
  simp only [CollatzResearch.WordTrace]
  refine ⟨81461051434552356363771913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108614735246069808485029217 81461051434552356363771913)
  ·
    refine ⟨61095788575914267272828935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81461051434552356363771913 61095788575914267272828935)
    ·
      refine ⟨91643682863871400909243403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61095788575914267272828935 91643682863871400909243403)
      ·
        refine ⟨137465524295807101363865105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91643682863871400909243403 137465524295807101363865105)
        ·
          refine ⟨103099143221855326022898829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137465524295807101363865105 103099143221855326022898829)
          ·
            refine ⟨38662178708195747258587061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103099143221855326022898829 38662178708195747258587061)
            ·
              refine ⟨3624579253893351305492537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38662178708195747258587061 3624579253893351305492537)
              ·
                refine ⟨2718434440420013479119403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3624579253893351305492537 2718434440420013479119403)
                ·
                  refine ⟨4077651660630020218679105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718434440420013479119403 4077651660630020218679105)
                  ·
                    refine ⟨3058238745472515164009329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4077651660630020218679105 3058238745472515164009329)
                    ·
                      refine ⟨2293679059104386373006997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3058238745472515164009329 2293679059104386373006997)
                      ·
                        rfl

theorem cell23_4466924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 1, 2, 2].length) (baseStart_4466924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466924 prefixEnd_4466924 := by exact prefixLift 4466924
  have htrace : WordTrace (prefixWord ++ tailWord_4466924) baseStart_4466924 baseEnd_4466924 := by
    simpa [prefixWord, tailWord_4466924, baseEnd_4466924] using wordTrace_append hprefix tailTrace_4466924
  have hstable : (prefixWord ++ tailWord_4466924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466924).length < 2 ^ (prefixWord ++ tailWord_4466924).sum := by decide
  have hdescent : baseEnd_4466924 < baseStart_4466924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466926 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 2, 7]
def baseStart_4466926 : Nat := 118140960795 + 4466926 * 2 ^ 59
def prefixEnd_4466926 : Nat := 4983230072969 + 3 ^ 40 * 4466926 * 2
def baseEnd_4466926 : Nat := 764560028688565121727329

theorem tailTrace_4466926 : CollatzResearch.WordTrace tailWord_4466926 prefixEnd_4466926 764560028688565121727329 := by
  unfold tailWord_4466926
  simp only [CollatzResearch.WordTrace]
  refine ⟨20365271976887183383639579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108614783876731644712744421 20365271976887183383639579)
  ·
    refine ⟨30547907965330775075459369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20365271976887183383639579 30547907965330775075459369)
    ·
      refine ⟨22910930973998081306594527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30547907965330775075459369 22910930973998081306594527)
      ·
        refine ⟨34366396460997121959891791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22910930973998081306594527 34366396460997121959891791)
        ·
          refine ⟨51549594691495682939837687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34366396460997121959891791 51549594691495682939837687)
          ·
            refine ⟨77324392037243524409756531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51549594691495682939837687 77324392037243524409756531)
            ·
              refine ⟨115986588055865286614634797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77324392037243524409756531 115986588055865286614634797)
              ·
                refine ⟨43494970520949482480488049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115986588055865286614634797 43494970520949482480488049)
                ·
                  refine ⟨32621227890712111860366037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43494970520949482480488049 32621227890712111860366037)
                  ·
                    refine ⟨764560028688565121727329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32621227890712111860366037 764560028688565121727329)
                    ·
                      rfl

theorem cell23_4466926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_4466926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466926 prefixEnd_4466926 := by exact prefixLift 4466926
  have htrace : WordTrace (prefixWord ++ tailWord_4466926) baseStart_4466926 baseEnd_4466926 := by
    simpa [prefixWord, tailWord_4466926, baseEnd_4466926] using wordTrace_append hprefix tailTrace_4466926
  have hstable : (prefixWord ++ tailWord_4466926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466926).length < 2 ^ (prefixWord ++ tailWord_4466926).sum := by decide
  have hdescent : baseEnd_4466926 < baseStart_4466926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466974 : List Nat := [4, 3, 2, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_4466974 : Nat := 118140960795 + 4466974 * 2 ^ 59
def prefixEnd_4466974 : Nat := 4983230072969 + 3 ^ 40 * 4466974 * 2
def baseEnd_4466974 : Nat := 2293704733137111177381767

theorem tailTrace_4466974 : CollatzResearch.WordTrace tailWord_4466974 prefixEnd_4466974 2293704733137111177381767 := by
  unfold tailWord_4466974
  simp only [CollatzResearch.WordTrace]
  refine ⟨20365490814865446408357997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108615951012615714177909317 20365490814865446408357997)
  ·
    refine ⟨7637059055574542403134249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20365490814865446408357997 7637059055574542403134249)
    ·
      refine ⟨5727794291680906802350687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7637059055574542403134249 5727794291680906802350687)
      ·
        refine ⟨8591691437521360203526031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5727794291680906802350687 8591691437521360203526031)
        ·
          refine ⟨12887537156282040305289047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8591691437521360203526031 12887537156282040305289047)
          ·
            refine ⟨19331305734423060457933571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12887537156282040305289047 19331305734423060457933571)
            ·
              refine ⟨28996958601634590686900357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19331305734423060457933571 28996958601634590686900357)
              ·
                refine ⟨5436929737806485753793817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28996958601634590686900357 5436929737806485753793817)
                ·
                  refine ⟨4077697303354864315345363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5436929737806485753793817 4077697303354864315345363)
                  ·
                    refine ⟨6116545955032296473018045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4077697303354864315345363 6116545955032296473018045)
                    ·
                      refine ⟨2293704733137111177381767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6116545955032296473018045 2293704733137111177381767)
                      ·
                        rfl

theorem cell23_4466974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_4466974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466974 prefixEnd_4466974 := by exact prefixLift 4466974
  have htrace : WordTrace (prefixWord ++ tailWord_4466974) baseStart_4466974 baseEnd_4466974 := by
    simpa [prefixWord, tailWord_4466974, baseEnd_4466974] using wordTrace_append hprefix tailTrace_4466974
  have hstable : (prefixWord ++ tailWord_4466974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466974).length < 2 ^ (prefixWord ++ tailWord_4466974).sum := by decide
  have hdescent : baseEnd_4466974 < baseStart_4466974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4466997 : List Nat := [1, 3, 3, 1, 2, 1, 1, 5, 2, 2, 2]
def baseStart_4466997 : Nat := 118140960795 + 4466997 * 2 ^ 59
def prefixEnd_4466997 : Nat := 4983230072969 + 3 ^ 40 * 4466997 * 2
def baseEnd_4466997 : Nat := 2293716543192164587394161

theorem tailTrace_4466997 : CollatzResearch.WordTrace tailWord_4466997 prefixEnd_4466997 2293716543192164587394161 := by
  unfold tailWord_4466997
  simp only [CollatzResearch.WordTrace]
  refine ⟨162924765397840246194951245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108616510265226830796634163 162924765397840246194951245)
  ·
    refine ⟨61096787024190092323106717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162924765397840246194951245 61096787024190092323106717)
    ·
      refine ⟨22911295134071284621165019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61096787024190092323106717 22911295134071284621165019)
      ·
        refine ⟨34366942701106926931747529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22911295134071284621165019 34366942701106926931747529)
        ·
          refine ⟨25775207025830195198810647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34366942701106926931747529 25775207025830195198810647)
          ·
            refine ⟨38662810538745292798215971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25775207025830195198810647 38662810538745292798215971)
            ·
              refine ⟨57994215808117939197323957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38662810538745292798215971 57994215808117939197323957)
              ·
                refine ⟨5436957732011056799749121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57994215808117939197323957 5436957732011056799749121)
                ·
                  refine ⟨4077718299008292599811841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5436957732011056799749121 4077718299008292599811841)
                  ·
                    refine ⟨3058288724256219449858881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4077718299008292599811841 3058288724256219449858881)
                    ·
                      refine ⟨2293716543192164587394161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3058288724256219449858881 2293716543192164587394161)
                      ·
                        rfl

theorem cell23_4466997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_4466997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4466997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4466997 prefixEnd_4466997 := by exact prefixLift 4466997
  have htrace : WordTrace (prefixWord ++ tailWord_4466997) baseStart_4466997 baseEnd_4466997 := by
    simpa [prefixWord, tailWord_4466997, baseEnd_4466997] using wordTrace_append hprefix tailTrace_4466997
  have hstable : (prefixWord ++ tailWord_4466997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4466997).length < 2 ^ (prefixWord ++ tailWord_4466997).sum := by decide
  have hdescent : baseEnd_4466997 < baseStart_4466997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4466997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467020 : List Nat := [2, 2, 1, 3, 2, 1, 4, 3, 5]
def baseStart_4467020 : Nat := 118140960795 + 4467020 * 2 ^ 59
def prefixEnd_4467020 : Nat := 4983230072969 + 3 ^ 40 * 4467020 * 2
def baseEnd_4467020 : Nat := 254858705916357555267395

theorem tailTrace_4467020 : CollatzResearch.WordTrace tailWord_4467020 prefixEnd_4467020 254858705916357555267395 := by
  unfold tailWord_4467020
  simp only [CollatzResearch.WordTrace]
  refine ⟨81462802138378460561519257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108617069517837947415359009 81462802138378460561519257)
  ·
    refine ⟨61097101603783845421139443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81462802138378460561519257 61097101603783845421139443)
    ·
      refine ⟨91645652405675768131709165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61097101603783845421139443 91645652405675768131709165)
      ·
        refine ⟨34367119652128413049390937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91645652405675768131709165 34367119652128413049390937)
        ·
          refine ⟨25775339739096309787043203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34367119652128413049390937 25775339739096309787043203)
          ·
            refine ⟨38663009608644464680564805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25775339739096309787043203 38663009608644464680564805)
            ·
              refine ⟨7249314301620837127605901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38663009608644464680564805 7249314301620837127605901)
              ·
                refine ⟨2718492863107813922852213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7249314301620837127605901 2718492863107813922852213)
                ·
                  refine ⟨254858705916357555267395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2718492863107813922852213 254858705916357555267395)
                  ·
                    rfl

theorem cell23_4467020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 5].length) (baseStart_4467020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467020 prefixEnd_4467020 := by exact prefixLift 4467020
  have htrace : WordTrace (prefixWord ++ tailWord_4467020) baseStart_4467020 baseEnd_4467020 := by
    simpa [prefixWord, tailWord_4467020, baseEnd_4467020] using wordTrace_append hprefix tailTrace_4467020
  have hstable : (prefixWord ++ tailWord_4467020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467020).length < 2 ^ (prefixWord ++ tailWord_4467020).sum := by decide
  have hdescent : baseEnd_4467020 < baseStart_4467020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467023 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 1, 7, 2]
def baseStart_4467023 : Nat := 118140960795 + 4467023 * 2 ^ 59
def prefixEnd_4467023 : Nat := 4983230072969 + 3 ^ 40 * 4467023 * 2
def baseEnd_4467023 : Nat := 2293729893689181485669041

theorem tailTrace_4467023 : CollatzResearch.WordTrace tailWord_4467023 prefixEnd_4467023 2293729893689181485669041 := by
  unfold tailWord_4467023
  simp only [CollatzResearch.WordTrace]
  refine ⟨162925713695746052635397723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108617142463830701756931815 162925713695746052635397723)
  ·
    refine ⟨244388570543619078953096585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162925713695746052635397723 244388570543619078953096585)
    ·
      refine ⟨183291427907714309214822439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244388570543619078953096585 183291427907714309214822439)
      ·
        refine ⟨274937141861571463822233659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183291427907714309214822439 274937141861571463822233659)
        ·
          refine ⟨412405712792357195733350489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274937141861571463822233659 412405712792357195733350489)
          ·
            refine ⟨309304284594267896800012867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 412405712792357195733350489 309304284594267896800012867)
            ·
              refine ⟨463956426891401845200019301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309304284594267896800012867 463956426891401845200019301)
              ·
                refine ⟨86991830042137845975003619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 463956426891401845200019301 86991830042137845975003619)
                ·
                  refine ⟨130487745063206768962505429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86991830042137845975003619 130487745063206768962505429)
                  ·
                    refine ⟨3058306524918908647558721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 130487745063206768962505429 3058306524918908647558721)
                    ·
                      refine ⟨2293729893689181485669041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3058306524918908647558721 2293729893689181485669041)
                      ·
                        rfl

theorem cell23_4467023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 7, 2].length) (baseStart_4467023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467023 prefixEnd_4467023 := by exact prefixLift 4467023
  have htrace : WordTrace (prefixWord ++ tailWord_4467023) baseStart_4467023 baseEnd_4467023 := by
    simpa [prefixWord, tailWord_4467023, baseEnd_4467023] using wordTrace_append hprefix tailTrace_4467023
  have hstable : (prefixWord ++ tailWord_4467023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467023).length < 2 ^ (prefixWord ++ tailWord_4467023).sum := by decide
  have hdescent : baseEnd_4467023 < baseStart_4467023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467053 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_4467053 : Nat := 118140960795 + 4467053 * 2 ^ 59
def prefixEnd_4467053 : Nat := 4983230072969 + 3 ^ 40 * 4467053 * 2
def baseEnd_4467053 : Nat := 2293745298108816368293903

theorem tailTrace_4467053 : CollatzResearch.WordTrace tailWord_4467053 prefixEnd_4467053 2293745298108816368293903 := by
  unfold tailWord_4467053
  simp only [CollatzResearch.WordTrace]
  refine ⟨162926807885637367758989813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108617871923758245172659875 162926807885637367758989813)
  ·
    refine ⟨15274388239278503227405295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162926807885637367758989813 15274388239278503227405295)
    ·
      refine ⟨22911582358917754841107943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15274388239278503227405295 22911582358917754841107943)
      ·
        refine ⟨34367373538376632261661915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22911582358917754841107943 34367373538376632261661915)
        ·
          refine ⟨51551060307564948392492873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34367373538376632261661915 51551060307564948392492873)
          ·
            refine ⟨38663295230673711294369655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51551060307564948392492873 38663295230673711294369655)
            ·
              refine ⟨57994942846010566941554483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38663295230673711294369655 57994942846010566941554483)
              ·
                refine ⟨86992414269015850412331725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57994942846010566941554483 86992414269015850412331725)
                ·
                  refine ⟨32622155350880943904624397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86992414269015850412331725 32622155350880943904624397)
                  ·
                    refine ⟨12233308256580353964234149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32622155350880943904624397 12233308256580353964234149)
                    ·
                      refine ⟨2293745298108816368293903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12233308256580353964234149 2293745298108816368293903)
                      ·
                        rfl

theorem cell23_4467053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_4467053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467053 prefixEnd_4467053 := by exact prefixLift 4467053
  have htrace : WordTrace (prefixWord ++ tailWord_4467053) baseStart_4467053 baseEnd_4467053 := by
    simpa [prefixWord, tailWord_4467053, baseEnd_4467053] using wordTrace_append hprefix tailTrace_4467053
  have hstable : (prefixWord ++ tailWord_4467053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467053).length < 2 ^ (prefixWord ++ tailWord_4467053).sum := by decide
  have hdescent : baseEnd_4467053 < baseStart_4467053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467063 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 5, 4]
def baseStart_4467063 : Nat := 118140960795 + 4467063 * 2 ^ 59
def prefixEnd_4467063 : Nat := 4983230072969 + 3 ^ 40 * 4467063 * 2
def baseEnd_4467063 : Nat := 764583477638453776389619

theorem tailTrace_4467063 : CollatzResearch.WordTrace tailWord_4467063 prefixEnd_4467063 764583477638453776389619 := by
  unfold tailWord_4467063
  simp only [CollatzResearch.WordTrace]
  refine ⟨162927172615601139466853843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108618115077067426311235895 162927172615601139466853843)
  ·
    refine ⟨244390758923401709200280765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162927172615601139466853843 244390758923401709200280765)
    ·
      refine ⟨91646534596275640950105287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244390758923401709200280765 91646534596275640950105287)
      ·
        refine ⟨137469801894413461425157931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91646534596275640950105287 137469801894413461425157931)
        ·
          refine ⟨206204702841620192137736897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137469801894413461425157931 206204702841620192137736897)
          ·
            refine ⟨154653527131215144103302673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206204702841620192137736897 154653527131215144103302673)
            ·
              refine ⟨115990145348411358077477005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154653527131215144103302673 115990145348411358077477005)
              ·
                refine ⟨43496304505654259279053877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115990145348411358077477005 43496304505654259279053877)
                ·
                  refine ⟨4077778547405086807411301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43496304505654259279053877 4077778547405086807411301)
                  ·
                    refine ⟨764583477638453776389619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4077778547405086807411301 764583477638453776389619)
                    ·
                      rfl

theorem cell23_4467063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_4467063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467063 prefixEnd_4467063 := by exact prefixLift 4467063
  have htrace : WordTrace (prefixWord ++ tailWord_4467063) baseStart_4467063 baseEnd_4467063 := by
    simpa [prefixWord, tailWord_4467063, baseEnd_4467063] using wordTrace_append hprefix tailTrace_4467063
  have hstable : (prefixWord ++ tailWord_4467063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467063).length < 2 ^ (prefixWord ++ tailWord_4467063).sum := by decide
  have hdescent : baseEnd_4467063 < baseStart_4467063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467093 : List Nat := [1, 3, 2, 1, 1, 2, 1, 6, 6]
def baseStart_4467093 : Nat := 118140960795 + 4467093 * 2 ^ 59
def prefixEnd_4467093 : Nat := 4983230072969 + 3 ^ 40 * 4467093 * 2
def baseEnd_4467093 : Nat := 254862870814999579088191

theorem tailTrace_4467093 : CollatzResearch.WordTrace tailWord_4467093 prefixEnd_4467093 254862870814999579088191 := by
  unfold tailWord_4467093
  simp only [CollatzResearch.WordTrace]
  refine ⟨162928266805492454590445933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108618844536994969726963955 162928266805492454590445933)
  ·
    refine ⟨61098100052059670471417225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162928266805492454590445933 61098100052059670471417225)
    ·
      refine ⟨45823575039044752853562919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61098100052059670471417225 45823575039044752853562919)
      ·
        refine ⟨68735362558567129280344379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45823575039044752853562919 68735362558567129280344379)
        ·
          refine ⟨103103043837850693920516569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68735362558567129280344379 103103043837850693920516569)
          ·
            refine ⟨77327282878388020440387427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103103043837850693920516569 77327282878388020440387427)
            ·
              refine ⟨115990924317582030660581141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77327282878388020440387427 115990924317582030660581141)
              ·
                refine ⟨5437074577386657687214741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 115990924317582030660581141 5437074577386657687214741)
                ·
                  refine ⟨254862870814999579088191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5437074577386657687214741 254862870814999579088191)
                  ·
                    rfl

theorem cell23_4467093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 6].length) (baseStart_4467093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467093 prefixEnd_4467093 := by exact prefixLift 4467093
  have htrace : WordTrace (prefixWord ++ tailWord_4467093) baseStart_4467093 baseEnd_4467093 := by
    simpa [prefixWord, tailWord_4467093, baseEnd_4467093] using wordTrace_append hprefix tailTrace_4467093
  have hstable : (prefixWord ++ tailWord_4467093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467093).length < 2 ^ (prefixWord ++ tailWord_4467093).sum := by decide
  have hdescent : baseEnd_4467093 < baseStart_4467093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467130 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2]
def baseStart_4467130 : Nat := 118140960795 + 4467130 * 2 ^ 59
def prefixEnd_4467130 : Nat := 4983230072969 + 3 ^ 40 * 4467130 * 2
def baseEnd_4467130 : Nat := 2293784836119212567031049

theorem tailTrace_4467130 : CollatzResearch.WordTrace tailWord_4467130 prefixEnd_4467130 2293784836119212567031049 := by
  unfold tailWord_4467130
  simp only [CollatzResearch.WordTrace]
  refine ⟨40732404076589602477385711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108619744204238939939695229 40732404076589602477385711)
  ·
    refine ⟨61098606114884403716078567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40732404076589602477385711 61098606114884403716078567)
    ·
      refine ⟨91647909172326605574117851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61098606114884403716078567 91647909172326605574117851)
      ·
        refine ⟨137471863758489908361176777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91647909172326605574117851 137471863758489908361176777)
        ·
          refine ⟨103103897818867431270882583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137471863758489908361176777 103103897818867431270882583)
          ·
            refine ⟨154655846728301146906323875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103103897818867431270882583 154655846728301146906323875)
            ·
              refine ⟨231983770092451720359485813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154655846728301146906323875 231983770092451720359485813)
              ·
                refine ⟨21748478446167348783701795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 231983770092451720359485813 21748478446167348783701795)
                ·
                  refine ⟨32622717669251023175552693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21748478446167348783701795 32622717669251023175552693)
                  ·
                    refine ⟨3058379781492283422708065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32622717669251023175552693 3058379781492283422708065)
                    ·
                      refine ⟨2293784836119212567031049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3058379781492283422708065 2293784836119212567031049)
                      ·
                        rfl

theorem cell23_4467130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2].length) (baseStart_4467130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467130 prefixEnd_4467130 := by exact prefixLift 4467130
  have htrace : WordTrace (prefixWord ++ tailWord_4467130) baseStart_4467130 baseEnd_4467130 := by
    simpa [prefixWord, tailWord_4467130, baseEnd_4467130] using wordTrace_append hprefix tailTrace_4467130
  have hstable : (prefixWord ++ tailWord_4467130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467130).length < 2 ^ (prefixWord ++ tailWord_4467130).sum := by decide
  have hdescent : baseEnd_4467130 < baseStart_4467130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467148 : List Nat := [2, 2, 1, 4, 4, 1, 2, 2, 1, 4]
def baseStart_4467148 : Nat := 118140960795 + 4467148 * 2 ^ 59
def prefixEnd_4467148 : Nat := 4983230072969 + 3 ^ 40 * 4467148 * 2
def baseEnd_4467148 : Nat := 764598026256997832201989

theorem tailTrace_4467148 : CollatzResearch.WordTrace tailWord_4467148 prefixEnd_4467148 764598026256997832201989 := by
  unfold tailWord_4467148
  simp only [CollatzResearch.WordTrace]
  refine ⟨81465136410146599491849049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108620181880195465989132065 81465136410146599491849049)
  ·
    refine ⟨61098852307609949618886787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81465136410146599491849049 61098852307609949618886787)
    ·
      refine ⟨91648278461414924428330181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61098852307609949618886787 91648278461414924428330181)
      ·
        refine ⟨17184052211515298330311909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91648278461414924428330181 17184052211515298330311909)
        ·
          refine ⟨3222009789659118436933483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17184052211515298330311909 3222009789659118436933483)
          ·
            refine ⟨4833014684488677655400225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3222009789659118436933483 4833014684488677655400225)
            ·
              refine ⟨3624761013366508241550169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4833014684488677655400225 3624761013366508241550169)
              ·
                refine ⟨2718570760024881181162627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3624761013366508241550169 2718570760024881181162627)
                ·
                  refine ⟨4077856140037321771743941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718570760024881181162627 4077856140037321771743941)
                  ·
                    refine ⟨764598026256997832201989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4077856140037321771743941 764598026256997832201989)
                    ·
                      rfl

theorem cell23_4467148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 1, 4].length) (baseStart_4467148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467148 prefixEnd_4467148 := by exact prefixLift 4467148
  have htrace : WordTrace (prefixWord ++ tailWord_4467148) baseStart_4467148 baseEnd_4467148 := by
    simpa [prefixWord, tailWord_4467148, baseEnd_4467148] using wordTrace_append hprefix tailTrace_4467148
  have hstable : (prefixWord ++ tailWord_4467148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467148).length < 2 ^ (prefixWord ++ tailWord_4467148).sum := by decide
  have hdescent : baseEnd_4467148 < baseStart_4467148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467160 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 2, 6, 2]
def baseStart_4467160 : Nat := 118140960795 + 4467160 * 2 ^ 59
def prefixEnd_4467160 : Nat := 4983230072969 + 3 ^ 40 * 4467160 * 2
def baseEnd_4467160 : Nat := 2293800240538847449655911

theorem tailTrace_4467160 : CollatzResearch.WordTrace tailWord_4467160 prefixEnd_4467160 2293800240538847449655911 := by
  unfold tailWord_4467160
  simp only [CollatzResearch.WordTrace]
  refine ⟨81465355248124862516567467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108620473664166483355423289 81465355248124862516567467)
  ·
    refine ⟨122198032872187293774851201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81465355248124862516567467 122198032872187293774851201)
    ·
      refine ⟨91648524654140470331138401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122198032872187293774851201 91648524654140470331138401)
      ·
        refine ⟨68736393490605352748353801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91648524654140470331138401 68736393490605352748353801)
        ·
          refine ⟨51552295117954014561265351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68736393490605352748353801 51552295117954014561265351)
          ·
            refine ⟨77328442676931021841898027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51552295117954014561265351 77328442676931021841898027)
            ·
              refine ⟨115992664015396532762847041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77328442676931021841898027 115992664015396532762847041)
              ·
                refine ⟨86994498011547399572135281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115992664015396532762847041 86994498011547399572135281)
                ·
                  refine ⟨65245873508660549679101461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86994498011547399572135281 65245873508660549679101461)
                  ·
                    refine ⟨3058400320718463266207881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65245873508660549679101461 3058400320718463266207881)
                    ·
                      refine ⟨2293800240538847449655911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3058400320718463266207881 2293800240538847449655911)
                      ·
                        rfl

theorem cell23_4467160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_4467160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467160 prefixEnd_4467160 := by exact prefixLift 4467160
  have htrace : WordTrace (prefixWord ++ tailWord_4467160) baseStart_4467160 baseEnd_4467160 := by
    simpa [prefixWord, tailWord_4467160, baseEnd_4467160] using wordTrace_append hprefix tailTrace_4467160
  have hstable : (prefixWord ++ tailWord_4467160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467160).length < 2 ^ (prefixWord ++ tailWord_4467160).sum := by decide
  have hdescent : baseEnd_4467160 < baseStart_4467160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467180 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 3]
def baseStart_4467180 : Nat := 118140960795 + 4467180 * 2 ^ 59
def prefixEnd_4467180 : Nat := 4983230072969 + 3 ^ 40 * 4467180 * 2
def baseEnd_4467180 : Nat := 2293810510151937371405819

theorem tailTrace_4467180 : CollatzResearch.WordTrace tailWord_4467180 prefixEnd_4467180 2293810510151937371405819 := by
  unfold tailWord_4467180
  simp only [CollatzResearch.WordTrace]
  refine ⟨81465719978088634224431497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108620959970784845632575329 81465719978088634224431497)
  ·
    refine ⟨61099289983566475668323623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81465719978088634224431497 61099289983566475668323623)
    ·
      refine ⟨91648934975349713502485435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61099289983566475668323623 91648934975349713502485435)
      ·
        refine ⟨137473402463024570253728153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91648934975349713502485435 137473402463024570253728153)
        ·
          refine ⟨103105051847268427690296115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137473402463024570253728153 103105051847268427690296115)
          ·
            refine ⟨154657577770902641535444173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103105051847268427690296115 154657577770902641535444173)
            ·
              refine ⟨57996591664088490575791565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154657577770902641535444173 57996591664088490575791565)
              ·
                refine ⟨21748721874033183965921837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57996591664088490575791565 21748721874033183965921837)
                ·
                  refine ⟨8155770702762443987220689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21748721874033183965921837 8155770702762443987220689)
                  ·
                    refine ⟨6116828027071832990415517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8155770702762443987220689 6116828027071832990415517)
                    ·
                      refine ⟨2293810510151937371405819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6116828027071832990415517 2293810510151937371405819)
                      ·
                        rfl

theorem cell23_4467180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_4467180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467180 prefixEnd_4467180 := by exact prefixLift 4467180
  have htrace : WordTrace (prefixWord ++ tailWord_4467180) baseStart_4467180 baseEnd_4467180 := by
    simpa [prefixWord, tailWord_4467180, baseEnd_4467180] using wordTrace_append hprefix tailTrace_4467180
  have hstable : (prefixWord ++ tailWord_4467180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467180).length < 2 ^ (prefixWord ++ tailWord_4467180).sum := by decide
  have hdescent : baseEnd_4467180 < baseStart_4467180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467181 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 2, 3, 2]
def baseStart_4467181 : Nat := 118140960795 + 4467181 * 2 ^ 59
def prefixEnd_4467181 : Nat := 4983230072969 + 3 ^ 40 * 4467181 * 2
def baseEnd_4467181 : Nat := 2293811023632591867493315

theorem tailTrace_4467181 : CollatzResearch.WordTrace tailWord_4467181 prefixEnd_4467181 2293811023632591867493315 := by
  unfold tailWord_4467181
  simp only [CollatzResearch.WordTrace]
  refine ⟨162931476429173645619649397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108620984286115763746432931 162931476429173645619649397)
  ·
    refine ⟨15274825915235029276842131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 162931476429173645619649397 15274825915235029276842131)
    ·
      refine ⟨22912238872852543915263197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15274825915235029276842131 22912238872852543915263197)
      ·
        refine ⟨8592089577319703968223699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22912238872852543915263197 8592089577319703968223699)
        ·
          refine ⟨12888134365979555952335549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8592089577319703968223699 12888134365979555952335549)
          ·
            refine ⟨4833050387242333482125831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12888134365979555952335549 4833050387242333482125831)
            ·
              refine ⟨7249575580863500223188747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4833050387242333482125831 7249575580863500223188747)
              ·
                refine ⟨10874363371295250334783121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7249575580863500223188747 10874363371295250334783121)
                ·
                  refine ⟨8155772528471437751087341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10874363371295250334783121 8155772528471437751087341)
                  ·
                    refine ⟨3058414698176789156657753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8155772528471437751087341 3058414698176789156657753)
                    ·
                      refine ⟨2293811023632591867493315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3058414698176789156657753 2293811023632591867493315)
                      ·
                        rfl

theorem cell23_4467181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_4467181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467181 prefixEnd_4467181 := by exact prefixLift 4467181
  have htrace : WordTrace (prefixWord ++ tailWord_4467181) baseStart_4467181 baseEnd_4467181 := by
    simpa [prefixWord, tailWord_4467181, baseEnd_4467181] using wordTrace_append hprefix tailTrace_4467181
  have hstable : (prefixWord ++ tailWord_4467181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467181).length < 2 ^ (prefixWord ++ tailWord_4467181).sum := by decide
  have hdescent : baseEnd_4467181 < baseStart_4467181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467197 : List Nat := [1, 4, 1, 1, 1, 3, 3, 3, 1, 2, 3]
def baseStart_4467197 : Nat := 118140960795 + 4467197 * 2 ^ 59
def prefixEnd_4467197 : Nat := 4983230072969 + 3 ^ 40 * 4467197 * 2
def baseEnd_4467197 : Nat := 2293819239323063804893241

theorem tailTrace_4467197 : CollatzResearch.WordTrace tailWord_4467197 prefixEnd_4467197 2293819239323063804893241 := by
  unfold tailWord_4467197
  simp only [CollatzResearch.WordTrace]
  refine ⟨162932059997115680352231845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108621373331410453568154563 162932059997115680352231845)
  ·
    refine ⟨30549761249459190066043471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162932059997115680352231845 30549761249459190066043471)
    ·
      refine ⟨45824641874188785099065207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30549761249459190066043471 45824641874188785099065207)
      ·
        refine ⟨68736962811283177648597811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45824641874188785099065207 68736962811283177648597811)
        ·
          refine ⟨103105444216924766472896717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68736962811283177648597811 103105444216924766472896717)
          ·
            refine ⟨38664541581346787427336269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103105444216924766472896717 38664541581346787427336269)
            ·
              refine ⟨14499203093005045285251101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38664541581346787427336269 14499203093005045285251101)
              ·
                refine ⟨5437201159876891981969163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14499203093005045285251101 5437201159876891981969163)
                ·
                  refine ⟨8155801739815337972953745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5437201159876891981969163 8155801739815337972953745)
                  ·
                    refine ⟨6116851304861503479715309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8155801739815337972953745 6116851304861503479715309)
                    ·
                      refine ⟨2293819239323063804893241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6116851304861503479715309 2293819239323063804893241)
                      ·
                        rfl

theorem cell23_4467197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_4467197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467197 prefixEnd_4467197 := by exact prefixLift 4467197
  have htrace : WordTrace (prefixWord ++ tailWord_4467197) baseStart_4467197 baseEnd_4467197 := by
    simpa [prefixWord, tailWord_4467197, baseEnd_4467197] using wordTrace_append hprefix tailTrace_4467197
  have hstable : (prefixWord ++ tailWord_4467197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467197).length < 2 ^ (prefixWord ++ tailWord_4467197).sum := by decide
  have hdescent : baseEnd_4467197 < baseStart_4467197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467204 : List Nat := [2, 3, 2, 3, 1, 1, 3, 2, 2, 4]
def baseStart_4467204 : Nat := 118140960795 + 4467204 * 2 ^ 59
def prefixEnd_4467204 : Nat := 4983230072969 + 3 ^ 40 * 4467204 * 2
def baseEnd_4467204 : Nat := 764607611229215092501903

theorem tailTrace_4467204 : CollatzResearch.WordTrace tailWord_4467204 prefixEnd_4467204 764607611229215092501903 := by
  unfold tailWord_4467204
  simp only [CollatzResearch.WordTrace]
  refine ⟨81466157654045160273868333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108621543538726880365157777 81466157654045160273868333)
  ·
    refine ⟨30549809120266935102700625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81466157654045160273868333 30549809120266935102700625)
    ·
      refine ⟨22912356840200201327025469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30549809120266935102700625 22912356840200201327025469)
      ·
        refine ⟨8592133815075075497634551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22912356840200201327025469 8592133815075075497634551)
        ·
          refine ⟨12888200722612613246451827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8592133815075075497634551 12888200722612613246451827)
          ·
            refine ⟨19332301083918919869677741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12888200722612613246451827 19332301083918919869677741)
            ·
              refine ⟨7249612906469594951129153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19332301083918919869677741 7249612906469594951129153)
              ·
                refine ⟨5437209679852196213346865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7249612906469594951129153 5437209679852196213346865)
                ·
                  refine ⟨4077907259889147160010149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5437209679852196213346865 4077907259889147160010149)
                  ·
                    refine ⟨764607611229215092501903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4077907259889147160010149 764607611229215092501903)
                    ·
                      rfl

theorem cell23_4467204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_4467204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467204 prefixEnd_4467204 := by exact prefixLift 4467204
  have htrace : WordTrace (prefixWord ++ tailWord_4467204) baseStart_4467204 baseEnd_4467204 := by
    simpa [prefixWord, tailWord_4467204, baseEnd_4467204] using wordTrace_append hprefix tailTrace_4467204
  have hstable : (prefixWord ++ tailWord_4467204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467204).length < 2 ^ (prefixWord ++ tailWord_4467204).sum := by decide
  have hdescent : baseEnd_4467204 < baseStart_4467204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467211 : List Nat := [1, 1, 1, 1, 7, 1, 2, 4, 1, 2, 2]
def baseStart_4467211 : Nat := 118140960795 + 4467211 * 2 ^ 59
def prefixEnd_4467211 : Nat := 4983230072969 + 3 ^ 40 * 4467211 * 2
def baseEnd_4467211 : Nat := 2293826428052226750118177

theorem tailTrace_4467211 : CollatzResearch.WordTrace tailWord_4467211 prefixEnd_4467211 2293826428052226750118177 := by
  unfold tailWord_4467211
  simp only [CollatzResearch.WordTrace]
  refine ⟨162932570619064960743241487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108621713746043307162160991 162932570619064960743241487)
  ·
    refine ⟨244398855928597441114862231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162932570619064960743241487 244398855928597441114862231)
    ·
      refine ⟨366598283892896161672293347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244398855928597441114862231 366598283892896161672293347)
      ·
        refine ⟨549897425839344242508440021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366598283892896161672293347 549897425839344242508440021)
        ·
          refine ⟨12888220918109630683791563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 549897425839344242508440021 12888220918109630683791563)
          ·
            refine ⟨19332331377164446025687345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12888220918109630683791563 19332331377164446025687345)
            ·
              refine ⟨14499248532873334519265509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19332331377164446025687345 14499248532873334519265509)
              ·
                refine ⟨2718609099913750222362283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14499248532873334519265509 2718609099913750222362283)
                ·
                  refine ⟨4077913649870625333543425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718609099913750222362283 4077913649870625333543425)
                  ·
                    refine ⟨3058435237402969000157569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4077913649870625333543425 3058435237402969000157569)
                    ·
                      refine ⟨2293826428052226750118177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3058435237402969000157569 2293826428052226750118177)
                      ·
                        rfl

theorem cell23_4467211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 1, 2, 2].length) (baseStart_4467211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467211 prefixEnd_4467211 := by exact prefixLift 4467211
  have htrace : WordTrace (prefixWord ++ tailWord_4467211) baseStart_4467211 baseEnd_4467211 := by
    simpa [prefixWord, tailWord_4467211, baseEnd_4467211] using wordTrace_append hprefix tailTrace_4467211
  have hstable : (prefixWord ++ tailWord_4467211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467211).length < 2 ^ (prefixWord ++ tailWord_4467211).sum := by decide
  have hdescent : baseEnd_4467211 < baseStart_4467211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467237 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 3, 3, 2]
def baseStart_4467237 : Nat := 118140960795 + 4467237 * 2 ^ 59
def prefixEnd_4467237 : Nat := 4983230072969 + 3 ^ 40 * 4467237 * 2
def baseEnd_4467237 : Nat := 2293839778549243648393057

theorem tailTrace_4467237 : CollatzResearch.WordTrace tailWord_4467237 prefixEnd_4467237 2293839778549243648393057 := by
  unfold tailWord_4467237
  simp only [CollatzResearch.WordTrace]
  refine ⟨162933518916970767183687965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108622345944647178122458643 162933518916970767183687965)
  ·
    refine ⟨61100069593864037693882987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162933518916970767183687965 61100069593864037693882987)
    ·
      refine ⟨91650104390796056540824481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61100069593864037693882987 91650104390796056540824481)
      ·
        refine ⟨68737578293097042405618361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91650104390796056540824481 68737578293097042405618361)
        ·
          refine ⟨51553183719822781804213771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68737578293097042405618361 51553183719822781804213771)
          ·
            refine ⟨77329775579734172706320657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51553183719822781804213771 77329775579734172706320657)
            ·
              refine ⟨57997331684800629529740493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77329775579734172706320657 57997331684800629529740493)
              ·
                refine ⟨21748999381800236073652685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57997331684800629529740493 21748999381800236073652685)
                ·
                  refine ⟨8155874768175088527619757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21748999381800236073652685 8155874768175088527619757)
                  ·
                    refine ⟨3058453038065658197857409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8155874768175088527619757 3058453038065658197857409)
                    ·
                      refine ⟨2293839778549243648393057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3058453038065658197857409 2293839778549243648393057)
                      ·
                        rfl

theorem cell23_4467237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_4467237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467237 prefixEnd_4467237 := by exact prefixLift 4467237
  have htrace : WordTrace (prefixWord ++ tailWord_4467237) baseStart_4467237 baseEnd_4467237 := by
    simpa [prefixWord, tailWord_4467237, baseEnd_4467237] using wordTrace_append hprefix tailTrace_4467237
  have hstable : (prefixWord ++ tailWord_4467237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467237).length < 2 ^ (prefixWord ++ tailWord_4467237).sum := by decide
  have hdescent : baseEnd_4467237 < baseStart_4467237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467243 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 1, 8]
def baseStart_4467243 : Nat := 118140960795 + 4467243 * 2 ^ 59
def prefixEnd_4467243 : Nat := 4983230072969 + 3 ^ 40 * 4467243 * 2
def baseEnd_4467243 : Nat := 764614286477723541639343

theorem tailTrace_4467243 : CollatzResearch.WordTrace tailWord_4467243 prefixEnd_4467243 764614286477723541639343 := by
  unfold tailWord_4467243
  simp only [CollatzResearch.WordTrace]
  refine ⟨162933737754949030208406383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108622491836632686805604255 162933737754949030208406383)
  ·
    refine ⟨244400606632423545312609575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162933737754949030208406383 244400606632423545312609575)
    ·
      refine ⟨366600909948635317968914363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244400606632423545312609575 366600909948635317968914363)
      ·
        refine ⟨549901364922952976953371545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366600909948635317968914363 549901364922952976953371545)
        ·
          refine ⟨412426023692214732715028659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 549901364922952976953371545 412426023692214732715028659)
          ·
            refine ⟨618639035538322099072542989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412426023692214732715028659 618639035538322099072542989)
            ·
              refine ⟨231989638326870787152203621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 618639035538322099072542989 231989638326870787152203621)
              ·
                refine ⟨43498057186288272591038179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231989638326870787152203621 43498057186288272591038179)
                ·
                  refine ⟨65247085779432408886557269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43498057186288272591038179 65247085779432408886557269)
                  ·
                    refine ⟨764614286477723541639343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65247085779432408886557269 764614286477723541639343)
                    ·
                      rfl

theorem cell23_4467243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 8].length) (baseStart_4467243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467243 prefixEnd_4467243 := by exact prefixLift 4467243
  have htrace : WordTrace (prefixWord ++ tailWord_4467243) baseStart_4467243 baseEnd_4467243 := by
    simpa [prefixWord, tailWord_4467243, baseEnd_4467243] using wordTrace_append hprefix tailTrace_4467243
  have hstable : (prefixWord ++ tailWord_4467243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467243).length < 2 ^ (prefixWord ++ tailWord_4467243).sum := by decide
  have hdescent : baseEnd_4467243 < baseStart_4467243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467262 : List Nat := [4, 2, 1, 4, 1, 1, 3, 2, 1, 2, 2]
def baseStart_4467262 : Nat := 118140960795 + 4467262 * 2 ^ 59
def prefixEnd_4467262 : Nat := 4983230072969 + 3 ^ 40 * 4467262 * 2
def baseEnd_4467262 : Nat := 2293852615565606050580443

theorem tailTrace_4467262 : CollatzResearch.WordTrace tailWord_4467262 prefixEnd_4467262 2293852615565606050580443 := by
  unfold tailWord_4467262
  simp only [CollatzResearch.WordTrace]
  refine ⟨20366803842735024556668505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108622953827920130968898693 20366803842735024556668505)
  ·
    refine ⟨15275102882051268417501379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20366803842735024556668505 15275102882051268417501379)
    ·
      refine ⟨22912654323076902626252069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15275102882051268417501379 22912654323076902626252069)
      ·
        refine ⟨4296122685576919242422263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22912654323076902626252069 4296122685576919242422263)
        ·
          refine ⟨6444184028365378863633395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4296122685576919242422263 6444184028365378863633395)
          ·
            refine ⟨9666276042548068295450093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6444184028365378863633395 9666276042548068295450093)
            ·
              refine ⟨3624853515955525610793785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9666276042548068295450093 3624853515955525610793785)
              ·
                refine ⟨2718640136966644208095339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3624853515955525610793785 2718640136966644208095339)
                ·
                  refine ⟨4077960205449966312143009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718640136966644208095339 4077960205449966312143009)
                  ·
                    refine ⟨3058470154087474734107257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4077960205449966312143009 3058470154087474734107257)
                    ·
                      refine ⟨2293852615565606050580443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3058470154087474734107257 2293852615565606050580443)
                      ·
                        rfl

theorem cell23_4467262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_4467262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467262 prefixEnd_4467262 := by exact prefixLift 4467262
  have htrace : WordTrace (prefixWord ++ tailWord_4467262) baseStart_4467262 baseEnd_4467262 := by
    simpa [prefixWord, tailWord_4467262, baseEnd_4467262] using wordTrace_append hprefix tailTrace_4467262
  have hstable : (prefixWord ++ tailWord_4467262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467262).length < 2 ^ (prefixWord ++ tailWord_4467262).sum := by decide
  have hdescent : baseEnd_4467262 < baseStart_4467262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467324 : List Nat := [2, 2, 2, 1, 1, 2, 6, 2, 5]
def baseStart_4467324 : Nat := 118140960795 + 4467324 * 2 ^ 59
def prefixEnd_4467324 : Nat := 4983230072969 + 3 ^ 40 * 4467324 * 2
def baseEnd_4467324 : Nat := 254876050151798312000573

theorem tailTrace_4467324 : CollatzResearch.WordTrace tailWord_4467324 prefixEnd_4467324 254876050151798312000573 := by
  unfold tailWord_4467324
  simp only [CollatzResearch.WordTrace]
  refine ⟨81468346033827790521052513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108624461378437054028070017 81468346033827790521052513)
  ·
    refine ⟨61101259525370842890789385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81468346033827790521052513 61101259525370842890789385)
    ·
      refine ⟨45825944644028132168092039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61101259525370842890789385 45825944644028132168092039)
      ·
        refine ⟨68738916966042198252138059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45825944644028132168092039 68738916966042198252138059)
        ·
          refine ⟨103108375449063297378207089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68738916966042198252138059 103108375449063297378207089)
          ·
            refine ⟨77331281586797473033655317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103108375449063297378207089 77331281586797473033655317)
            ·
              refine ⟨3624903824381131548452593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77331281586797473033655317 3624903824381131548452593)
              ·
                refine ⟨2718677868285848661339445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3624903824381131548452593 2718677868285848661339445)
                ·
                  refine ⟨254876050151798312000573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2718677868285848661339445 254876050151798312000573)
                  ·
                    rfl

theorem cell23_4467324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 5].length) (baseStart_4467324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467324 prefixEnd_4467324 := by exact prefixLift 4467324
  have htrace : WordTrace (prefixWord ++ tailWord_4467324) baseStart_4467324 baseEnd_4467324 := by
    simpa [prefixWord, tailWord_4467324, baseEnd_4467324] using wordTrace_append hprefix tailTrace_4467324
  have hstable : (prefixWord ++ tailWord_4467324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467324).length < 2 ^ (prefixWord ++ tailWord_4467324).sum := by decide
  have hdescent : baseEnd_4467324 < baseStart_4467324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467354 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 1, 7]
def baseStart_4467354 : Nat := 118140960795 + 4467354 * 2 ^ 59
def prefixEnd_4467354 : Nat := 4983230072969 + 3 ^ 40 * 4467354 * 2
def baseEnd_4467354 : Nat := 764633285261939896876673

theorem tailTrace_4467354 : CollatzResearch.WordTrace tailWord_4467354 prefixEnd_4467354 764633285261939896876673 := by
  unfold tailWord_4467354
  simp only [CollatzResearch.WordTrace]
  refine ⟨40734446564386724041424279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108625190838364597443798077 40734446564386724041424279)
  ·
    refine ⟨61101669846580086062136419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40734446564386724041424279 61101669846580086062136419)
    ·
      refine ⟨91652504769870129093204629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61101669846580086062136419 91652504769870129093204629)
      ·
        refine ⟨4296211161087662301243967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 91652504769870129093204629 4296211161087662301243967)
        ·
          refine ⟨6444316741631493451865951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4296211161087662301243967 6444316741631493451865951)
          ·
            refine ⟨9666475112447240177798927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6444316741631493451865951 9666475112447240177798927)
            ·
              refine ⟨14499712668670860266698391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9666475112447240177798927 14499712668670860266698391)
              ·
                refine ⟨21749569003006290400047587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14499712668670860266698391 21749569003006290400047587)
                ·
                  refine ⟨32624353504509435600071381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21749569003006290400047587 32624353504509435600071381)
                  ·
                    refine ⟨764633285261939896876673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32624353504509435600071381 764633285261939896876673)
                    ·
                      rfl

theorem cell23_4467354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_4467354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467354 prefixEnd_4467354 := by exact prefixLift 4467354
  have htrace : WordTrace (prefixWord ++ tailWord_4467354) baseStart_4467354 baseEnd_4467354 := by
    simpa [prefixWord, tailWord_4467354, baseEnd_4467354] using wordTrace_append hprefix tailTrace_4467354
  have hstable : (prefixWord ++ tailWord_4467354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467354).length < 2 ^ (prefixWord ++ tailWord_4467354).sum := by decide
  have hdescent : baseEnd_4467354 < baseStart_4467354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467447 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 4]
def baseStart_4467447 : Nat := 118140960795 + 4467447 * 2 ^ 59
def prefixEnd_4467447 : Nat := 4983230072969 + 3 ^ 40 * 4467447 * 2
def baseEnd_4467447 : Nat := 2293947609486687826767091

theorem tailTrace_4467447 : CollatzResearch.WordTrace tailWord_4467447 prefixEnd_4467447 2293947609486687826767091 := by
  unfold tailWord_4467447
  simp only [CollatzResearch.WordTrace]
  refine ⟨162941178246209973048832595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108627452164139982032555063 162941178246209973048832595)
  ·
    refine ⟨244411767369314959573248893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162941178246209973048832595 244411767369314959573248893)
    ·
      refine ⟨91654412763493109839968335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244411767369314959573248893 91654412763493109839968335)
      ·
        refine ⟨137481619145239664759952503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91654412763493109839968335 137481619145239664759952503)
        ·
          refine ⟨206222428717859497139928755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137481619145239664759952503 206222428717859497139928755)
          ·
            refine ⟨309333643076789245709893133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206222428717859497139928755 309333643076789245709893133)
            ·
              refine ⟨116000116153795967141209925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 309333643076789245709893133 116000116153795967141209925)
              ·
                refine ⟨21750021778836743838976861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116000116153795967141209925 21750021778836743838976861)
                ·
                  refine ⟨8156258167063778939616323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21750021778836743838976861 8156258167063778939616323)
                  ·
                    refine ⟨12234387250595668409424485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8156258167063778939616323 12234387250595668409424485)
                    ·
                      refine ⟨2293947609486687826767091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12234387250595668409424485 2293947609486687826767091)
                      ·
                        rfl

theorem cell23_4467447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_4467447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467447 prefixEnd_4467447 := by exact prefixLift 4467447
  have htrace : WordTrace (prefixWord ++ tailWord_4467447) baseStart_4467447 baseEnd_4467447 := by
    simpa [prefixWord, tailWord_4467447, baseEnd_4467447] using wordTrace_append hprefix tailTrace_4467447
  have hstable : (prefixWord ++ tailWord_4467447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467447).length < 2 ^ (prefixWord ++ tailWord_4467447).sum := by decide
  have hdescent : baseEnd_4467447 < baseStart_4467447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467457 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 1, 6]
def baseStart_4467457 : Nat := 118140960795 + 4467457 * 2 ^ 59
def prefixEnd_4467457 : Nat := 4983230072969 + 3 ^ 40 * 4467457 * 2
def baseEnd_4467457 : Nat := 764650914764410929214015

theorem tailTrace_4467457 : CollatzResearch.WordTrace tailWord_4467457 prefixEnd_4467457 764650914764410929214015 := by
  unfold tailWord_4467457
  simp only [CollatzResearch.WordTrace]
  refine ⟨162941542976173744756696625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108627695317449163171131083 162941542976173744756696625)
  ·
    refine ⟨122206157232130308567522469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162941542976173744756696625 122206157232130308567522469)
    ·
      refine ⟨22913654481024432856410463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122206157232130308567522469 22913654481024432856410463)
      ·
        refine ⟨34370481721536649284615695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22913654481024432856410463 34370481721536649284615695)
        ·
          refine ⟨51555722582304973926923543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34370481721536649284615695 51555722582304973926923543)
          ·
            refine ⟨77333583873457460890385315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51555722582304973926923543 77333583873457460890385315)
            ·
              refine ⟨116000375810186191335577973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77333583873457460890385315 116000375810186191335577973)
              ·
                refine ⟨10875035232204955437710435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116000375810186191335577973 10875035232204955437710435)
                ·
                  refine ⟨16312552848307433156565653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10875035232204955437710435 16312552848307433156565653)
                  ·
                    refine ⟨764650914764410929214015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16312552848307433156565653 764650914764410929214015)
                    ·
                      rfl

theorem cell23_4467457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_4467457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467457 prefixEnd_4467457 := by exact prefixLift 4467457
  have htrace : WordTrace (prefixWord ++ tailWord_4467457) baseStart_4467457 baseEnd_4467457 := by
    simpa [prefixWord, tailWord_4467457, baseEnd_4467457] using wordTrace_append hprefix tailTrace_4467457
  have hstable : (prefixWord ++ tailWord_4467457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467457).length < 2 ^ (prefixWord ++ tailWord_4467457).sum := by decide
  have hdescent : baseEnd_4467457 < baseStart_4467457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467464 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_4467464 : Nat := 118140960795 + 4467464 * 2 ^ 59
def prefixEnd_4467464 : Nat := 4983230072969 + 3 ^ 40 * 4467464 * 2
def baseEnd_4467464 : Nat := 2293956338657814260254513

theorem tailTrace_4467464 : CollatzResearch.WordTrace tailWord_4467464 prefixEnd_4467464 2293956338657814260254513 := by
  unfold tailWord_4467464
  simp only [CollatzResearch.WordTrace]
  refine ⟨81470899143574192476100723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108627865524765589968134297 81470899143574192476100723)
  ·
    refine ⟨122206348715361288714151085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81470899143574192476100723 122206348715361288714151085)
    ·
      refine ⟨45827380768260483267806657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122206348715361288714151085 45827380768260483267806657)
      ·
        refine ⟨34370535576195362450854993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45827380768260483267806657 34370535576195362450854993)
        ·
          refine ⟨25777901682146521838141245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34370535576195362450854993 25777901682146521838141245)
          ·
            refine ⟨9666713130804945689302967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25777901682146521838141245 9666713130804945689302967)
            ·
              refine ⟨14500069696207418533954451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9666713130804945689302967 14500069696207418533954451)
              ·
                refine ⟨21750104544311127800931677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14500069696207418533954451 21750104544311127800931677)
                ·
                  refine ⟨8156289204116672925349379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21750104544311127800931677 8156289204116672925349379)
                  ·
                    refine ⟨12234433806175009388024069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8156289204116672925349379 12234433806175009388024069)
                    ·
                      refine ⟨2293956338657814260254513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12234433806175009388024069 2293956338657814260254513)
                      ·
                        rfl

theorem cell23_4467464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_4467464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467464 prefixEnd_4467464 := by exact prefixLift 4467464
  have htrace : WordTrace (prefixWord ++ tailWord_4467464) baseStart_4467464 baseEnd_4467464 := by
    simpa [prefixWord, tailWord_4467464, baseEnd_4467464] using wordTrace_append hprefix tailTrace_4467464
  have hstable : (prefixWord ++ tailWord_4467464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467464).length < 2 ^ (prefixWord ++ tailWord_4467464).sum := by decide
  have hdescent : baseEnd_4467464 < baseStart_4467464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467484 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_4467484 : Nat := 118140960795 + 4467484 * 2 ^ 59
def prefixEnd_4467484 : Nat := 4983230072969 + 3 ^ 40 * 4467484 * 2
def baseEnd_4467484 : Nat := 2293966608270904182004421

theorem tailTrace_4467484 : CollatzResearch.WordTrace tailWord_4467484 prefixEnd_4467484 2293966608270904182004421 := by
  unfold tailWord_4467484
  simp only [CollatzResearch.WordTrace]
  refine ⟨81471263873537964183964753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108628351831383952245286337 81471263873537964183964753)
  ·
    refine ⟨61103447905153473137973565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81471263873537964183964753 61103447905153473137973565)
    ·
      refine ⟨22913792964432552426740087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61103447905153473137973565 22913792964432552426740087)
      ·
        refine ⟨34370689446648828640110131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22913792964432552426740087 34370689446648828640110131)
        ·
          refine ⟨51556034169973242960165197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34370689446648828640110131 51556034169973242960165197)
          ·
            refine ⟨19333512813739966110061949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51556034169973242960165197 19333512813739966110061949)
            ·
              refine ⟨7250067305152487291273231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19333512813739966110061949 7250067305152487291273231)
              ·
                refine ⟨10875100957728730936909847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7250067305152487291273231 10875100957728730936909847)
                ·
                  refine ⟨16312651436593096405364771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10875100957728730936909847 16312651436593096405364771)
                  ·
                    refine ⟨24468977154889644608047157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16312651436593096405364771 24468977154889644608047157)
                    ·
                      refine ⟨2293966608270904182004421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24468977154889644608047157 2293966608270904182004421)
                      ·
                        rfl

theorem cell23_4467484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_4467484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467484 prefixEnd_4467484 := by exact prefixLift 4467484
  have htrace : WordTrace (prefixWord ++ tailWord_4467484) baseStart_4467484 baseEnd_4467484 := by
    simpa [prefixWord, tailWord_4467484, baseEnd_4467484] using wordTrace_append hprefix tailTrace_4467484
  have hstable : (prefixWord ++ tailWord_4467484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467484).length < 2 ^ (prefixWord ++ tailWord_4467484).sum := by decide
  have hdescent : baseEnd_4467484 < baseStart_4467484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467492 : List Nat := [2, 3, 1, 3, 3, 2, 2, 2, 1, 1, 3]
def baseStart_4467492 : Nat := 118140960795 + 4467492 * 2 ^ 59
def prefixEnd_4467492 : Nat := 4983230072969 + 3 ^ 40 * 4467492 * 2
def baseEnd_4467492 : Nat := 2293970716116140150704385

theorem tailTrace_4467492 : CollatzResearch.WordTrace tailWord_4467492 prefixEnd_4467492 2293970716116140150704385 := by
  unfold tailWord_4467492
  simp only [CollatzResearch.WordTrace]
  refine ⟨81471409765523472867110365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108628546354031297156147153 81471409765523472867110365)
  ·
    refine ⟨30551778662071302325166387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81471409765523472867110365 30551778662071302325166387)
    ·
      refine ⟨45827667993106953487749581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30551778662071302325166387 45827667993106953487749581)
      ·
        refine ⟨17185375497415107557906093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45827667993106953487749581 17185375497415107557906093)
        ·
          refine ⟨6444515811530665334214785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17185375497415107557906093 6444515811530665334214785)
          ·
            refine ⟨4833386858647999000661089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6444515811530665334214785 4833386858647999000661089)
            ·
              refine ⟨3625040143985999250495817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4833386858647999000661089 3625040143985999250495817)
              ·
                refine ⟨2718780107989499437871863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3625040143985999250495817 2718780107989499437871863)
                ·
                  refine ⟨4078170161984249156807795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2718780107989499437871863 4078170161984249156807795)
                  ·
                    refine ⟨6117255242976373735211693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4078170161984249156807795 6117255242976373735211693)
                    ·
                      refine ⟨2293970716116140150704385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6117255242976373735211693 2293970716116140150704385)
                      ·
                        rfl

theorem cell23_4467492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_4467492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467492 prefixEnd_4467492 := by exact prefixLift 4467492
  have htrace : WordTrace (prefixWord ++ tailWord_4467492) baseStart_4467492 baseEnd_4467492 := by
    simpa [prefixWord, tailWord_4467492, baseEnd_4467492] using wordTrace_append hprefix tailTrace_4467492
  have hstable : (prefixWord ++ tailWord_4467492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467492).length < 2 ^ (prefixWord ++ tailWord_4467492).sum := by decide
  have hdescent : baseEnd_4467492 < baseStart_4467492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467527 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_4467527 : Nat := 118140960795 + 4467527 * 2 ^ 59
def prefixEnd_4467527 : Nat := 4983230072969 + 3 ^ 40 * 4467527 * 2
def baseEnd_4467527 : Nat := 2293988687939047513766723

theorem tailTrace_4467527 : CollatzResearch.WordTrace tailWord_4467527 prefixEnd_4467527 2293988687939047513766723 := by
  unfold tailWord_4467527
  simp only [CollatzResearch.WordTrace]
  refine ⟨162944096085920146711744835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108629397390613431141163223 162944096085920146711744835)
  ·
    refine ⟨244416144128880220067617253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162944096085920146711744835 244416144128880220067617253)
    ·
      refine ⟨45828027024165041262678235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 244416144128880220067617253 45828027024165041262678235)
      ·
        refine ⟨68742040536247561894017353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45828027024165041262678235 68742040536247561894017353)
        ·
          refine ⟨51556530402185671420513015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68742040536247561894017353 51556530402185671420513015)
          ·
            refine ⟨77334795603278507130769523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51556530402185671420513015 77334795603278507130769523)
            ·
              refine ⟨116002193404917760696154285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77334795603278507130769523 116002193404917760696154285)
              ·
                refine ⟨43500822526844160261057857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116002193404917760696154285 43500822526844160261057857)
                ·
                  refine ⟨32625616895133120195793393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43500822526844160261057857 32625616895133120195793393)
                  ·
                    refine ⟨24469212671349840146845045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32625616895133120195793393 24469212671349840146845045)
                    ·
                      refine ⟨2293988687939047513766723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24469212671349840146845045 2293988687939047513766723)
                      ·
                        rfl

theorem cell23_4467527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_4467527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467527 prefixEnd_4467527 := by exact prefixLift 4467527
  have htrace : WordTrace (prefixWord ++ tailWord_4467527) baseStart_4467527 baseEnd_4467527 := by
    simpa [prefixWord, tailWord_4467527, baseEnd_4467527] using wordTrace_append hprefix tailTrace_4467527
  have hstable : (prefixWord ++ tailWord_4467527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467527).length < 2 ^ (prefixWord ++ tailWord_4467527).sum := by decide
  have hdescent : baseEnd_4467527 < baseStart_4467527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467548 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_4467548 : Nat := 118140960795 + 4467548 * 2 ^ 59
def prefixEnd_4467548 : Nat := 4983230072969 + 3 ^ 40 * 4467548 * 2
def baseEnd_4467548 : Nat := 2293999471032791931604127

theorem tailTrace_4467548 : CollatzResearch.WordTrace tailWord_4467548 prefixEnd_4467548 2293999471032791931604127 := by
  unfold tailWord_4467548
  simp only [CollatzResearch.WordTrace]
  refine ⟨81472431009422033649129649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108629908012562711532172865 81472431009422033649129649)
  ·
    refine ⟨61104323257066525236847237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81472431009422033649129649 61104323257066525236847237)
    ·
      refine ⟨11457060610699973481908857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61104323257066525236847237 11457060610699973481908857)
      ·
        refine ⟨8592795458024980111431643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11457060610699973481908857 8592795458024980111431643)
        ·
          refine ⟨12889193187037470167147465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8592795458024980111431643 12889193187037470167147465)
          ·
            refine ⟨9666894890278102625360599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12889193187037470167147465 9666894890278102625360599)
            ·
              refine ⟨14500342335417153938040899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9666894890278102625360599 14500342335417153938040899)
              ·
                refine ⟨21750513503125730907061349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14500342335417153938040899 21750513503125730907061349)
                ·
                  refine ⟨4078221281836074545074003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21750513503125730907061349 4078221281836074545074003)
                  ·
                    refine ⟨6117331922754111817611005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4078221281836074545074003 6117331922754111817611005)
                    ·
                      refine ⟨2293999471032791931604127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6117331922754111817611005 2293999471032791931604127)
                      ·
                        rfl

theorem cell23_4467548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_4467548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467548 prefixEnd_4467548 := by exact prefixLift 4467548
  have htrace : WordTrace (prefixWord ++ tailWord_4467548) baseStart_4467548 baseEnd_4467548 := by
    simpa [prefixWord, tailWord_4467548, baseEnd_4467548] using wordTrace_append hprefix tailTrace_4467548
  have hstable : (prefixWord ++ tailWord_4467548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467548).length < 2 ^ (prefixWord ++ tailWord_4467548).sum := by decide
  have hdescent : baseEnd_4467548 < baseStart_4467548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467571 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 1, 4, 2]
def baseStart_4467571 : Nat := 118140960795 + 4467571 * 2 ^ 59
def prefixEnd_4467571 : Nat := 4983230072969 + 3 ^ 40 * 4467571 * 2
def baseEnd_4467571 : Nat := 2294011281087845341616521

theorem tailTrace_4467571 : CollatzResearch.WordTrace tailWord_4467571 prefixEnd_4467571 2294011281087845341616521 := by
  unfold tailWord_4467571
  simp only [CollatzResearch.WordTrace]
  refine ⟨162945700897760742226346567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108630467265173828150897711 162945700897760742226346567)
  ·
    refine ⟨244418551346641113339519851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162945700897760742226346567 244418551346641113339519851)
    ·
      refine ⟨366627827019961670009279777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244418551346641113339519851 366627827019961670009279777)
      ·
        refine ⟨274970870264971252506959833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366627827019961670009279777 274970870264971252506959833)
        ·
          refine ⟨206228152698728439380219875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274970870264971252506959833 206228152698728439380219875)
          ·
            refine ⟨309342229048092659070329813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206228152698728439380219875 309342229048092659070329813)
            ·
              refine ⟨7250208493314671696960855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 309342229048092659070329813 7250208493314671696960855)
              ·
                refine ⟨10875312739972007545441283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7250208493314671696960855 10875312739972007545441283)
                ·
                  refine ⟨16312969109958011318161925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10875312739972007545441283 16312969109958011318161925)
                  ·
                    refine ⟨3058681708117127122155361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16312969109958011318161925 3058681708117127122155361)
                    ·
                      refine ⟨2294011281087845341616521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3058681708117127122155361 2294011281087845341616521)
                      ·
                        rfl

theorem cell23_4467571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 4, 2].length) (baseStart_4467571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467571 prefixEnd_4467571 := by exact prefixLift 4467571
  have htrace : WordTrace (prefixWord ++ tailWord_4467571) baseStart_4467571 baseEnd_4467571 := by
    simpa [prefixWord, tailWord_4467571, baseEnd_4467571] using wordTrace_append hprefix tailTrace_4467571
  have hstable : (prefixWord ++ tailWord_4467571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467571).length < 2 ^ (prefixWord ++ tailWord_4467571).sum := by decide
  have hdescent : baseEnd_4467571 < baseStart_4467571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467604 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_4467604 : Nat := 118140960795 + 4467604 * 2 ^ 59
def prefixEnd_4467604 : Nat := 4983230072969 + 3 ^ 40 * 4467604 * 2
def baseEnd_4467604 : Nat := 2294028225949443712503869

theorem tailTrace_4467604 : CollatzResearch.WordTrace tailWord_4467604 prefixEnd_4467604 2294028225949443712503869 := by
  unfold tailWord_4467604
  simp only [CollatzResearch.WordTrace]
  refine ⟨81473452253320594431148933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108631269671094125908198577 81473452253320594431148933)
  ·
    refine ⟨15276272297497611455840425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81473452253320594431148933 15276272297497611455840425)
    ·
      refine ⟨11457204223123208591880319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15276272297497611455840425 11457204223123208591880319)
      ·
        refine ⟨17185806334684812887820479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11457204223123208591880319 17185806334684812887820479)
        ·
          refine ⟨25778709502027219331730719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17185806334684812887820479 25778709502027219331730719)
          ·
            refine ⟨38668064253040828997596079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25778709502027219331730719 38668064253040828997596079)
            ·
              refine ⟨58002096379561243496394119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38668064253040828997596079 58002096379561243496394119)
              ·
                refine ⟨87003144569341865244591179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58002096379561243496394119 87003144569341865244591179)
                ·
                  refine ⟨130504716854012797866886769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87003144569341865244591179 130504716854012797866886769)
                  ·
                    refine ⟨97878537640509598400165077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 130504716854012797866886769 97878537640509598400165077)
                    ·
                      refine ⟨2294028225949443712503869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97878537640509598400165077 2294028225949443712503869)
                      ·
                        rfl

theorem cell23_4467604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_4467604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467604 prefixEnd_4467604 := by exact prefixLift 4467604
  have htrace : WordTrace (prefixWord ++ tailWord_4467604) baseStart_4467604 baseEnd_4467604 := by
    simpa [prefixWord, tailWord_4467604, baseEnd_4467604] using wordTrace_append hprefix tailTrace_4467604
  have hstable : (prefixWord ++ tailWord_4467604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467604).length < 2 ^ (prefixWord ++ tailWord_4467604).sum := by decide
  have hdescent : baseEnd_4467604 < baseStart_4467604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467641 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 2, 5]
def baseStart_4467641 : Nat := 118140960795 + 4467641 * 2 ^ 59
def prefixEnd_4467641 : Nat := 4983230072969 + 3 ^ 40 * 4467641 * 2
def baseEnd_4467641 : Nat := 764682408244553355913733

theorem tailTrace_4467641 : CollatzResearch.WordTrace tailWord_4467641 prefixEnd_4467641 764682408244553355913733 := by
  unfold tailWord_4467641
  simp only [CollatzResearch.WordTrace]
  refine ⟨162948254007507144181394777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108632169338338096120929851 162948254007507144181394777)
  ·
    refine ⟨122211190505630358136046083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162948254007507144181394777 122211190505630358136046083)
    ·
      refine ⟨183316785758445537204069125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122211190505630358136046083 183316785758445537204069125)
      ·
        refine ⟨34371897329708538225762961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183316785758445537204069125 34371897329708538225762961)
        ·
          refine ⟨25778922997281403669322221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34371897329708538225762961 25778922997281403669322221)
          ·
            refine ⟨9667096123980526375995833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25778922997281403669322221 9667096123980526375995833)
            ·
              refine ⟨7250322092985394781996875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9667096123980526375995833 7250322092985394781996875)
              ·
                refine ⟨10875483139478092172995313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7250322092985394781996875 10875483139478092172995313)
                ·
                  refine ⟨8156612354608569129746485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10875483139478092172995313 8156612354608569129746485)
                  ·
                    refine ⟨764682408244553355913733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8156612354608569129746485 764682408244553355913733)
                    ·
                      rfl

theorem cell23_4467641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 5].length) (baseStart_4467641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467641 prefixEnd_4467641 := by exact prefixLift 4467641
  have htrace : WordTrace (prefixWord ++ tailWord_4467641) baseStart_4467641 baseEnd_4467641 := by
    simpa [prefixWord, tailWord_4467641, baseEnd_4467641] using wordTrace_append hprefix tailTrace_4467641
  have hstable : (prefixWord ++ tailWord_4467641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467641).length < 2 ^ (prefixWord ++ tailWord_4467641).sum := by decide
  have hdescent : baseEnd_4467641 < baseStart_4467641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467664 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 3]
def baseStart_4467664 : Nat := 118140960795 + 4467664 * 2 ^ 59
def prefixEnd_4467664 : Nat := 4983230072969 + 3 ^ 40 * 4467664 * 2
def baseEnd_4467664 : Nat := 2294059034788713477753593

theorem tailTrace_4467664 : CollatzResearch.WordTrace tailWord_4467664 prefixEnd_4467664 2294059034788713477753593 := by
  unfold tailWord_4467664
  simp only [CollatzResearch.WordTrace]
  refine ⟨81474546443211909554741023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108632728590949212739654697 81474546443211909554741023)
  ·
    refine ⟨122211819664817864332111535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81474546443211909554741023 122211819664817864332111535)
    ·
      refine ⟨183317729497226796498167303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122211819664817864332111535 183317729497226796498167303)
      ·
        refine ⟨274976594245840194747250955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183317729497226796498167303 274976594245840194747250955)
        ·
          refine ⟨412464891368760292120876433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274976594245840194747250955 412464891368760292120876433)
          ·
            refine ⟨309348668526570219090657325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 412464891368760292120876433 309348668526570219090657325)
            ·
              refine ⟨116005750697463832158996497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 309348668526570219090657325 116005750697463832158996497)
              ·
                refine ⟨87004313023097874119247373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116005750697463832158996497 87004313023097874119247373)
                ·
                  refine ⟨32626617383661702794717765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87004313023097874119247373 32626617383661702794717765)
                  ·
                    refine ⟨6117490759436569274009581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32626617383661702794717765 6117490759436569274009581)
                    ·
                      refine ⟨2294059034788713477753593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6117490759436569274009581 2294059034788713477753593)
                      ·
                        rfl

theorem cell23_4467664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 3].length) (baseStart_4467664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467664 prefixEnd_4467664 := by exact prefixLift 4467664
  have htrace : WordTrace (prefixWord ++ tailWord_4467664) baseStart_4467664 baseEnd_4467664 := by
    simpa [prefixWord, tailWord_4467664, baseEnd_4467664] using wordTrace_append hprefix tailTrace_4467664
  have hstable : (prefixWord ++ tailWord_4467664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467664).length < 2 ^ (prefixWord ++ tailWord_4467664).sum := by decide
  have hdescent : baseEnd_4467664 < baseStart_4467664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467748 : List Nat := [2, 3, 1, 4, 1, 1, 1, 4, 1, 5]
def baseStart_4467748 : Nat := 118140960795 + 4467748 * 2 ^ 59
def prefixEnd_4467748 : Nat := 4983230072969 + 3 ^ 40 * 4467748 * 2
def baseEnd_4467748 : Nat := 764700722387897049701069

theorem tailTrace_4467748 : CollatzResearch.WordTrace tailWord_4467748 prefixEnd_4467748 764700722387897049701069 := by
  unfold tailWord_4467748
  simp only [CollatzResearch.WordTrace]
  refine ⟨81476078309059750727769949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108634771078746334303693265 81476078309059750727769949)
  ·
    refine ⟨30553529365897406522913731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81476078309059750727769949 30553529365897406522913731)
    ·
      refine ⟨45830294048846109784370597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30553529365897406522913731 45830294048846109784370597)
      ·
        refine ⟨8593180134158645584569487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45830294048846109784370597 8593180134158645584569487)
        ·
          refine ⟨12889770201237968376854231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8593180134158645584569487 12889770201237968376854231)
          ·
            refine ⟨19334655301856952565281347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12889770201237968376854231 19334655301856952565281347)
            ·
              refine ⟨29001982952785428847922021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19334655301856952565281347 29001982952785428847922021)
              ·
                refine ⟨5437871803647267908985379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29001982952785428847922021 5437871803647267908985379)
                ·
                  refine ⟨8156807705470901863478069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5437871803647267908985379 8156807705470901863478069)
                  ·
                    refine ⟨764700722387897049701069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8156807705470901863478069 764700722387897049701069)
                    ·
                      rfl

theorem cell23_4467748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_4467748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467748 prefixEnd_4467748 := by exact prefixLift 4467748
  have htrace : WordTrace (prefixWord ++ tailWord_4467748) baseStart_4467748 baseEnd_4467748 := by
    simpa [prefixWord, tailWord_4467748, baseEnd_4467748] using wordTrace_append hprefix tailTrace_4467748
  have hstable : (prefixWord ++ tailWord_4467748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467748).length < 2 ^ (prefixWord ++ tailWord_4467748).sum := by decide
  have hdescent : baseEnd_4467748 < baseStart_4467748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467761 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 6, 4]
def baseStart_4467761 : Nat := 118140960795 + 4467761 * 2 ^ 59
def prefixEnd_4467761 : Nat := 4983230072969 + 3 ^ 40 * 4467761 * 2
def baseEnd_4467761 : Nat := 764702947470733199413549

theorem tailTrace_4467761 : CollatzResearch.WordTrace tailWord_4467761 prefixEnd_4467761 764702947470733199413549 := by
  unfold tailWord_4467761
  simp only [CollatzResearch.WordTrace]
  refine ⟨162952630767072404675763137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108635087178048269783842091 162952630767072404675763137)
  ·
    refine ⟨122214473075304303506822353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162952630767072404675763137 122214473075304303506822353)
    ·
      refine ⟨91660854806478227630116765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122214473075304303506822353 91660854806478227630116765)
      ·
        refine ⟨34372820552429335361293787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91660854806478227630116765 34372820552429335361293787)
        ·
          refine ⟨51559230828644003041940681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34372820552429335361293787 51559230828644003041940681)
          ·
            refine ⟨38669423121483002281455511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51559230828644003041940681 38669423121483002281455511)
            ·
              refine ⟨58004134682224503422183267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38669423121483002281455511 58004134682224503422183267)
              ·
                refine ⟨87006202023336755133274901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58004134682224503422183267 87006202023336755133274901)
                ·
                  refine ⟨4078415719843910396872261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87006202023336755133274901 4078415719843910396872261)
                  ·
                    refine ⟨764702947470733199413549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4078415719843910396872261 764702947470733199413549)
                    ·
                      rfl

theorem cell23_4467761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_4467761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467761 prefixEnd_4467761 := by exact prefixLift 4467761
  have htrace : WordTrace (prefixWord ++ tailWord_4467761) baseStart_4467761 baseEnd_4467761 := by
    simpa [prefixWord, tailWord_4467761, baseEnd_4467761] using wordTrace_append hprefix tailTrace_4467761
  have hstable : (prefixWord ++ tailWord_4467761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467761).length < 2 ^ (prefixWord ++ tailWord_4467761).sum := by decide
  have hdescent : baseEnd_4467761 < baseStart_4467761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467768 : List Nat := [2, 1, 2, 1, 5, 1, 2, 3, 1, 1, 4]
def baseStart_4467768 : Nat := 118140960795 + 4467768 * 2 ^ 59
def prefixEnd_4467768 : Nat := 4983230072969 + 3 ^ 40 * 4467768 * 2
def baseEnd_4467768 : Nat := 2294112436776781070853115

theorem tailTrace_4467768 : CollatzResearch.WordTrace tailWord_4467768 prefixEnd_4467768 2294112436776781070853115 := by
  unfold tailWord_4467768
  simp only [CollatzResearch.WordTrace]
  refine ⟨81476443039023522435633979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108635257385364696580845305 81476443039023522435633979)
  ·
    refine ⟨122214664558535283653450969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81476443039023522435633979 122214664558535283653450969)
    ·
      refine ⟨91660998418901462740088227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122214664558535283653450969 91660998418901462740088227)
      ·
        refine ⟨137491497628352194110132341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91660998418901462740088227 137491497628352194110132341)
        ·
          refine ⟨12889827902658018197824907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 137491497628352194110132341 12889827902658018197824907)
          ·
            refine ⟨19334741853987027296737361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12889827902658018197824907 19334741853987027296737361)
            ·
              refine ⟨14501056390490270472553021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19334741853987027296737361 14501056390490270472553021)
              ·
                refine ⟨5437896146433851427207383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14501056390490270472553021 5437896146433851427207383)
                ·
                  refine ⟨8156844219650777140811075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5437896146433851427207383 8156844219650777140811075)
                  ·
                    refine ⟨12235266329476165711216613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8156844219650777140811075 12235266329476165711216613)
                    ·
                      refine ⟨2294112436776781070853115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12235266329476165711216613 2294112436776781070853115)
                      ·
                        rfl

theorem cell23_4467768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_4467768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467768 prefixEnd_4467768 := by exact prefixLift 4467768
  have htrace : WordTrace (prefixWord ++ tailWord_4467768) baseStart_4467768 baseEnd_4467768 := by
    simpa [prefixWord, tailWord_4467768, baseEnd_4467768] using wordTrace_append hprefix tailTrace_4467768
  have hstable : (prefixWord ++ tailWord_4467768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467768).length < 2 ^ (prefixWord ++ tailWord_4467768).sum := by decide
  have hdescent : baseEnd_4467768 < baseStart_4467768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467818 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_4467818 : Nat := 118140960795 + 4467818 * 2 ^ 59
def prefixEnd_4467818 : Nat := 4983230072969 + 3 ^ 40 * 4467818 * 2
def baseEnd_4467818 : Nat := 2294138110809505875227885

theorem tailTrace_4467818 : CollatzResearch.WordTrace tailWord_4467818 prefixEnd_4467818 2294138110809505875227885 := by
  unfold tailWord_4467818
  simp only [CollatzResearch.WordTrace]
  refine ⟨40738677431966475852647027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108636473151910602273725405 40738677431966475852647027)
  ·
    refine ⟨61108016147949713778970541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40738677431966475852647027 61108016147949713778970541)
    ·
      refine ⟨22915506055481142667113953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61108016147949713778970541 22915506055481142667113953)
      ·
        refine ⟨17186629541610857000335465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22915506055481142667113953 17186629541610857000335465)
        ·
          refine ⟨12889972156208142750251599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17186629541610857000335465 12889972156208142750251599)
          ·
            refine ⟨19334958234312214125377399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12889972156208142750251599 19334958234312214125377399)
            ·
              refine ⟨29002437351468321188066099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19334958234312214125377399 29002437351468321188066099)
              ·
                refine ⟨43503656027202481782099149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29002437351468321188066099 43503656027202481782099149)
                ·
                  refine ⟨16313871010200930668287181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43503656027202481782099149 16313871010200930668287181)
                  ·
                    refine ⟨6117701628825349000607693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16313871010200930668287181 6117701628825349000607693)
                    ·
                      refine ⟨2294138110809505875227885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6117701628825349000607693 2294138110809505875227885)
                      ·
                        rfl

theorem cell23_4467818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_4467818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467818 prefixEnd_4467818 := by exact prefixLift 4467818
  have htrace : WordTrace (prefixWord ++ tailWord_4467818) baseStart_4467818 baseEnd_4467818 := by
    simpa [prefixWord, tailWord_4467818, baseEnd_4467818] using wordTrace_append hprefix tailTrace_4467818
  have hstable : (prefixWord ++ tailWord_4467818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467818).length < 2 ^ (prefixWord ++ tailWord_4467818).sum := by decide
  have hdescent : baseEnd_4467818 < baseStart_4467818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467822 : List Nat := [4, 1, 2, 2, 1, 3, 3, 1, 1, 2, 3]
def baseStart_4467822 : Nat := 118140960795 + 4467822 * 2 ^ 59
def prefixEnd_4467822 : Nat := 4983230072969 + 3 ^ 40 * 4467822 * 2
def baseEnd_4467822 : Nat := 2294140164732123859577867

theorem tailTrace_4467822 : CollatzResearch.WordTrace tailWord_4467822 prefixEnd_4467822 2294140164732123859577867 := by
  unfold tailWord_4467822
  simp only [CollatzResearch.WordTrace]
  refine ⟨20369356952481426511716715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108636570413234274729155813 20369356952481426511716715)
  ·
    refine ⟨30554035428722139767575073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20369356952481426511716715 30554035428722139767575073)
    ·
      refine ⟨22915526571541604825681305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30554035428722139767575073 22915526571541604825681305)
      ·
        refine ⟨17186644928656203619260979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22915526571541604825681305 17186644928656203619260979)
        ·
          refine ⟨25779967392984305428891469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17186644928656203619260979 25779967392984305428891469)
          ·
            refine ⟨9667487772369114535834301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25779967392984305428891469 9667487772369114535834301)
            ·
              refine ⟨3625307914638417950937863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9667487772369114535834301 3625307914638417950937863)
              ·
                refine ⟨5437961871957626926406795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3625307914638417950937863 5437961871957626926406795)
                ·
                  refine ⟨8156942807936440389610193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5437961871957626926406795 8156942807936440389610193)
                  ·
                    refine ⟨6117707105952330292207645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8156942807936440389610193 6117707105952330292207645)
                    ·
                      refine ⟨2294140164732123859577867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6117707105952330292207645 2294140164732123859577867)
                      ·
                        rfl

theorem cell23_4467822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_4467822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467822 prefixEnd_4467822 := by exact prefixLift 4467822
  have htrace : WordTrace (prefixWord ++ tailWord_4467822) baseStart_4467822 baseEnd_4467822 := by
    simpa [prefixWord, tailWord_4467822, baseEnd_4467822] using wordTrace_append hprefix tailTrace_4467822
  have hstable : (prefixWord ++ tailWord_4467822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467822).length < 2 ^ (prefixWord ++ tailWord_4467822).sum := by decide
  have hdescent : baseEnd_4467822 < baseStart_4467822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467861 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 2, 1, 5]
def baseStart_4467861 : Nat := 118140960795 + 4467861 * 2 ^ 59
def prefixEnd_4467861 : Nat := 4983230072969 + 3 ^ 40 * 4467861 * 2
def baseEnd_4467861 : Nat := 2294160190477649206990187

theorem tailTrace_4467861 : CollatzResearch.WordTrace tailWord_4467861 prefixEnd_4467861 2294160190477649206990187 := by
  unfold tailWord_4467861
  simp only [CollatzResearch.WordTrace]
  refine ⟨162956278066710121754403437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108637518711140081169602291 162956278066710121754403437)
  ·
    refine ⟨61108604275016295657901289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162956278066710121754403437 61108604275016295657901289)
    ·
      refine ⟨45831453206262221743425967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61108604275016295657901289 45831453206262221743425967)
      ·
        refine ⟨68747179809393332615138951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45831453206262221743425967 68747179809393332615138951)
        ·
          refine ⟨103120769714089998922708427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68747179809393332615138951 103120769714089998922708427)
          ·
            refine ⟨154681154571134998384062641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103120769714089998922708427 154681154571134998384062641)
            ·
              refine ⟨116010865928351248788046981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154681154571134998384062641 116010865928351248788046981)
              ·
                refine ⟨21752037361565859147758809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116010865928351248788046981 21752037361565859147758809)
                ·
                  refine ⟨16314028021174394360819107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21752037361565859147758809 16314028021174394360819107)
                  ·
                    refine ⟨24471042031761591541228661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16314028021174394360819107 24471042031761591541228661)
                    ·
                      refine ⟨2294160190477649206990187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24471042031761591541228661 2294160190477649206990187)
                      ·
                        rfl

theorem cell23_4467861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_4467861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467861 prefixEnd_4467861 := by exact prefixLift 4467861
  have htrace : WordTrace (prefixWord ++ tailWord_4467861) baseStart_4467861 baseEnd_4467861 := by
    simpa [prefixWord, tailWord_4467861, baseEnd_4467861] using wordTrace_append hprefix tailTrace_4467861
  have hstable : (prefixWord ++ tailWord_4467861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467861).length < 2 ^ (prefixWord ++ tailWord_4467861).sum := by decide
  have hdescent : baseEnd_4467861 < baseStart_4467861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467879 : List Nat := [1, 1, 6, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_4467879 : Nat := 118140960795 + 4467879 * 2 ^ 59
def prefixEnd_4467879 : Nat := 4983230072969 + 3 ^ 40 * 4467879 * 2
def baseEnd_4467879 : Nat := 2294169433129430136565105

theorem tailTrace_4467879 : CollatzResearch.WordTrace tailWord_4467879 prefixEnd_4467879 2294169433129430136565105 := by
  unfold tailWord_4467879
  simp only [CollatzResearch.WordTrace]
  refine ⟨162956934580644910828558691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108637956387096607219039127 162956934580644910828558691)
  ·
    refine ⟨244435401870967366242838037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162956934580644910828558691 244435401870967366242838037)
    ·
      refine ⟨11457909462701595292633033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 244435401870967366242838037 11457909462701595292633033)
      ·
        refine ⟨8593432097026196469474775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11457909462701595292633033 8593432097026196469474775)
        ·
          refine ⟨12890148145539294704212163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8593432097026196469474775 12890148145539294704212163)
          ·
            refine ⟨19335222218308942056318245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12890148145539294704212163 19335222218308942056318245)
            ·
              refine ⟨3625354165932926635559671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19335222218308942056318245 3625354165932926635559671)
              ·
                refine ⟨5438031248899389953339507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3625354165932926635559671 5438031248899389953339507)
                ·
                  refine ⟨8157046873349084930009261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5438031248899389953339507 8157046873349084930009261)
                  ·
                    refine ⟨3058892577505906848753473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8157046873349084930009261 3058892577505906848753473)
                    ·
                      refine ⟨2294169433129430136565105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3058892577505906848753473 2294169433129430136565105)
                      ·
                        rfl

theorem cell23_4467879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_4467879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467879 prefixEnd_4467879 := by exact prefixLift 4467879
  have htrace : WordTrace (prefixWord ++ tailWord_4467879) baseStart_4467879 baseEnd_4467879 := by
    simpa [prefixWord, tailWord_4467879, baseEnd_4467879] using wordTrace_append hprefix tailTrace_4467879
  have hstable : (prefixWord ++ tailWord_4467879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467879).length < 2 ^ (prefixWord ++ tailWord_4467879).sum := by decide
  have hdescent : baseEnd_4467879 < baseStart_4467879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467905 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_4467905 : Nat := 118140960795 + 4467905 * 2 ^ 59
def prefixEnd_4467905 : Nat := 4983230072969 + 3 ^ 40 * 4467905 * 2
def baseEnd_4467905 : Nat := 2294182783626447034839985

theorem tailTrace_4467905 : CollatzResearch.WordTrace tailWord_4467905 prefixEnd_4467905 2294182783626447034839985 := by
  unfold tailWord_4467905
  simp only [CollatzResearch.WordTrace]
  refine ⟨162957882878550717269005169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108638588585700478179336779 162957882878550717269005169)
  ·
    refine ⟨122218412158913037951753877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162957882878550717269005169 122218412158913037951753877)
    ·
      refine ⟨5728988069949048653988463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 122218412158913037951753877 5728988069949048653988463)
      ·
        refine ⟨8593482104923572980982695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5728988069949048653988463 8593482104923572980982695)
        ·
          refine ⟨12890223157385359471474043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8593482104923572980982695 12890223157385359471474043)
          ·
            refine ⟨19335334736078039207211065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12890223157385359471474043 19335334736078039207211065)
            ·
              refine ⟨14501501052058529405408299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19335334736078039207211065 14501501052058529405408299)
              ·
                refine ⟨21752251578087794108112449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14501501052058529405408299 21752251578087794108112449)
                ·
                  refine ⟨16314188683565845581084337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21752251578087794108112449 16314188683565845581084337)
                  ·
                    refine ⟨12235641512674384185813253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16314188683565845581084337 12235641512674384185813253)
                    ·
                      refine ⟨2294182783626447034839985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12235641512674384185813253 2294182783626447034839985)
                      ·
                        rfl

theorem cell23_4467905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_4467905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467905 prefixEnd_4467905 := by exact prefixLift 4467905
  have htrace : WordTrace (prefixWord ++ tailWord_4467905) baseStart_4467905 baseEnd_4467905 := by
    simpa [prefixWord, tailWord_4467905, baseEnd_4467905] using wordTrace_append hprefix tailTrace_4467905
  have hstable : (prefixWord ++ tailWord_4467905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467905).length < 2 ^ (prefixWord ++ tailWord_4467905).sum := by decide
  have hdescent : baseEnd_4467905 < baseStart_4467905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467921 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 3, 2, 5]
def baseStart_4467921 : Nat := 118140960795 + 4467921 * 2 ^ 59
def prefixEnd_4467921 : Nat := 4983230072969 + 3 ^ 40 * 4467921 * 2
def baseEnd_4467921 : Nat := 2294190999316918972239911

theorem tailTrace_4467921 : CollatzResearch.WordTrace tailWord_4467921 prefixEnd_4467921 2294190999316918972239911 := by
  unfold tailWord_4467921
  simp only [CollatzResearch.WordTrace]
  refine ⟨162958466446492752001587617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108638977630995168001058411 162958466446492752001587617)
  ·
    refine ⟨122218849834869564001190713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162958466446492752001587617 122218849834869564001190713)
    ·
      refine ⟨91664137376152173000893035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122218849834869564001190713 91664137376152173000893035)
      ·
        refine ⟨137496206064228259501339553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91664137376152173000893035 137496206064228259501339553)
        ·
          refine ⟨103122154548171194626004665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137496206064228259501339553 103122154548171194626004665)
          ·
            refine ⟨77341615911128395969503499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103122154548171194626004665 77341615911128395969503499)
            ·
              refine ⟨116012423866692593954255249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77341615911128395969503499 116012423866692593954255249)
              ·
                refine ⟨87009317900019445465691437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116012423866692593954255249 87009317900019445465691437)
                ·
                  refine ⟨32628494212507292049634289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87009317900019445465691437 32628494212507292049634289)
                  ·
                    refine ⟨24471370659380469037225717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32628494212507292049634289 24471370659380469037225717)
                    ·
                      refine ⟨2294190999316918972239911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24471370659380469037225717 2294190999316918972239911)
                      ·
                        rfl

theorem cell23_4467921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_4467921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467921 prefixEnd_4467921 := by exact prefixLift 4467921
  have htrace : WordTrace (prefixWord ++ tailWord_4467921) baseStart_4467921 baseEnd_4467921 := by
    simpa [prefixWord, tailWord_4467921, baseEnd_4467921] using wordTrace_append hprefix tailTrace_4467921
  have hstable : (prefixWord ++ tailWord_4467921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467921).length < 2 ^ (prefixWord ++ tailWord_4467921).sum := by decide
  have hdescent : baseEnd_4467921 < baseStart_4467921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467931 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 4]
def baseStart_4467931 : Nat := 118140960795 + 4467931 * 2 ^ 59
def prefixEnd_4467931 : Nat := 4983230072969 + 3 ^ 40 * 4467931 * 2
def baseEnd_4467931 : Nat := 2294196134123463933114865

theorem tailTrace_4467931 : CollatzResearch.WordTrace tailWord_4467931 prefixEnd_4467931 2294196134123463933114865 := by
  unfold tailWord_4467931
  simp only [CollatzResearch.WordTrace]
  refine ⟨162958831176456523709451647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108639220784304349139634431 162958831176456523709451647)
  ·
    refine ⟨244438246764684785564177471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162958831176456523709451647 244438246764684785564177471)
    ·
      refine ⟨366657370147027178346266207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244438246764684785564177471 366657370147027178346266207)
      ·
        refine ⟨549986055220540767519399311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366657370147027178346266207 549986055220540767519399311)
        ·
          refine ⟨824979082830811151279098967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549986055220540767519399311 824979082830811151279098967)
          ·
            refine ⟨1237468624246216726918648451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824979082830811151279098967 1237468624246216726918648451)
            ·
              refine ⟨1856202936369325090377972677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1237468624246216726918648451 1856202936369325090377972677)
              ·
                refine ⟨348038050569248454445869877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1856202936369325090377972677 348038050569248454445869877)
                ·
                  refine ⟨32628567240867042604300301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 348038050569248454445869877 32628567240867042604300301)
                  ·
                    refine ⟨12235712715325140976612613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32628567240867042604300301 12235712715325140976612613)
                    ·
                      refine ⟨2294196134123463933114865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12235712715325140976612613 2294196134123463933114865)
                      ·
                        rfl

theorem cell23_4467931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 4].length) (baseStart_4467931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467931 prefixEnd_4467931 := by exact prefixLift 4467931
  have htrace : WordTrace (prefixWord ++ tailWord_4467931) baseStart_4467931 baseEnd_4467931 := by
    simpa [prefixWord, tailWord_4467931, baseEnd_4467931] using wordTrace_append hprefix tailTrace_4467931
  have hstable : (prefixWord ++ tailWord_4467931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467931).length < 2 ^ (prefixWord ++ tailWord_4467931).sum := by decide
  have hdescent : baseEnd_4467931 < baseStart_4467931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467948 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 4]
def baseStart_4467948 : Nat := 118140960795 + 4467948 * 2 ^ 59
def prefixEnd_4467948 : Nat := 4983230072969 + 3 ^ 40 * 4467948 * 2
def baseEnd_4467948 : Nat := 2294204863294590366602287

theorem tailTrace_4467948 : CollatzResearch.WordTrace tailWord_4467948 prefixEnd_4467948 2294204863294590366602287 := by
  unfold tailWord_4467948
  simp only [CollatzResearch.WordTrace]
  refine ⟨81479725608697467806410249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108639634144929957075213665 81479725608697467806410249)
  ·
    refine ⟨61109794206523100854807687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81479725608697467806410249 61109794206523100854807687)
    ·
      refine ⟨91664691309784651282211531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61109794206523100854807687 91664691309784651282211531)
      ·
        refine ⟨137497036964676976923317297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91664691309784651282211531 137497036964676976923317297)
        ·
          refine ⟨103122777723507732692487973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137497036964676976923317297 103122777723507732692487973)
          ·
            refine ⟨19335520823157699879841495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103122777723507732692487973 19335520823157699879841495)
            ·
              refine ⟨29003281234736549819762243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19335520823157699879841495 29003281234736549819762243)
              ·
                refine ⟨43504921852104824729643365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29003281234736549819762243 43504921852104824729643365)
                ·
                  refine ⟨8157172847269654636808131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43504921852104824729643365 8157172847269654636808131)
                  ·
                    refine ⟨12235759270904481955212197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8157172847269654636808131 12235759270904481955212197)
                    ·
                      refine ⟨2294204863294590366602287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12235759270904481955212197 2294204863294590366602287)
                      ·
                        rfl

theorem cell23_4467948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_4467948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467948 prefixEnd_4467948 := by exact prefixLift 4467948
  have htrace : WordTrace (prefixWord ++ tailWord_4467948) baseStart_4467948 baseEnd_4467948 := by
    simpa [prefixWord, tailWord_4467948, baseEnd_4467948] using wordTrace_append hprefix tailTrace_4467948
  have hstable : (prefixWord ++ tailWord_4467948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467948).length < 2 ^ (prefixWord ++ tailWord_4467948).sum := by decide
  have hdescent : baseEnd_4467948 < baseStart_4467948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467968 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 3]
def baseStart_4467968 : Nat := 118140960795 + 4467968 * 2 ^ 59
def prefixEnd_4467968 : Nat := 4983230072969 + 3 ^ 40 * 4467968 * 2
def baseEnd_4467968 : Nat := 2294215132907680288352195

theorem tailTrace_4467968 : CollatzResearch.WordTrace tailWord_4467968 prefixEnd_4467968 2294215132907680288352195 := by
  unfold tailWord_4467968
  simp only [CollatzResearch.WordTrace]
  refine ⟨81480090338661239514274279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108640120451548319352365705 81480090338661239514274279)
  ·
    refine ⟨122220135507991859271411419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81480090338661239514274279 122220135507991859271411419)
    ·
      refine ⟨183330203261987788907117129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122220135507991859271411419 183330203261987788907117129)
      ·
        refine ⟨137497652446490841680337847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183330203261987788907117129 137497652446490841680337847)
        ·
          refine ⟨206246478669736262520506771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137497652446490841680337847 206246478669736262520506771)
          ·
            refine ⟨309369718004604393780760157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206246478669736262520506771 309369718004604393780760157)
            ·
              refine ⟨116013644251726647667785059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 309369718004604393780760157 116013644251726647667785059)
              ·
                refine ⟨174020466377589971501677589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116013644251726647667785059 174020466377589971501677589)
                ·
                  refine ⟨8157209361449529914141137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 174020466377589971501677589 8157209361449529914141137)
                  ·
                    refine ⟨6117907021087147435605853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8157209361449529914141137 6117907021087147435605853)
                    ·
                      refine ⟨2294215132907680288352195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6117907021087147435605853 2294215132907680288352195)
                      ·
                        rfl

theorem cell23_4467968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_4467968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467968 prefixEnd_4467968 := by exact prefixLift 4467968
  have htrace : WordTrace (prefixWord ++ tailWord_4467968) baseStart_4467968 baseEnd_4467968 := by
    simpa [prefixWord, tailWord_4467968, baseEnd_4467968] using wordTrace_append hprefix tailTrace_4467968
  have hstable : (prefixWord ++ tailWord_4467968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467968).length < 2 ^ (prefixWord ++ tailWord_4467968).sum := by decide
  have hdescent : baseEnd_4467968 < baseStart_4467968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4467985 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 3]
def baseStart_4467985 : Nat := 118140960795 + 4467985 * 2 ^ 59
def prefixEnd_4467985 : Nat := 4983230072969 + 3 ^ 40 * 4467985 * 2
def baseEnd_4467985 : Nat := 2294223862078806721839617

theorem tailTrace_4467985 : CollatzResearch.WordTrace tailWord_4467985 prefixEnd_4467985 2294223862078806721839617 := by
  unfold tailWord_4467985
  simp only [CollatzResearch.WordTrace]
  refine ⟨162960800718260890931917409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108640533812173927287944939 162960800718260890931917409)
  ·
    refine ⟨122220600538695668198938057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162960800718260890931917409 122220600538695668198938057)
    ·
      refine ⟨91665450404021751149203543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122220600538695668198938057 91665450404021751149203543)
      ·
        refine ⟨137498175606032626723805315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91665450404021751149203543 137498175606032626723805315)
        ·
          refine ⟨206247263409048940085707973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137498175606032626723805315 206247263409048940085707973)
          ·
            refine ⟨38671361889196676266070245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206247263409048940085707973 38671361889196676266070245)
            ·
              refine ⟨7250880354224376799888171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38671361889196676266070245 7250880354224376799888171)
              ·
                refine ⟨10876320531336565199832257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7250880354224376799888171 10876320531336565199832257)
                ·
                  refine ⟨8157240398502423899874193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10876320531336565199832257 8157240398502423899874193)
                  ·
                    refine ⟨6117930298876817924905645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8157240398502423899874193 6117930298876817924905645)
                    ·
                      refine ⟨2294223862078806721839617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6117930298876817924905645 2294223862078806721839617)
                      ·
                        rfl

theorem cell23_4467985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_4467985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4467985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4467985 prefixEnd_4467985 := by exact prefixLift 4467985
  have htrace : WordTrace (prefixWord ++ tailWord_4467985) baseStart_4467985 baseEnd_4467985 := by
    simpa [prefixWord, tailWord_4467985, baseEnd_4467985] using wordTrace_append hprefix tailTrace_4467985
  have hstable : (prefixWord ++ tailWord_4467985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4467985).length < 2 ^ (prefixWord ++ tailWord_4467985).sum := by decide
  have hdescent : baseEnd_4467985 < baseStart_4467985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4467985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468005 : List Nat := [1, 3, 1, 2, 4, 2, 2, 2, 6]
def baseStart_4468005 : Nat := 118140960795 + 4468005 * 2 ^ 59
def prefixEnd_4468005 : Nat := 4983230072969 + 3 ^ 40 * 4468005 * 2
def baseEnd_4468005 : Nat := 254914903521321849287725

theorem tailTrace_4468005 : CollatzResearch.WordTrace tailWord_4468005 prefixEnd_4468005 254914903521321849287725 := by
  unfold tailWord_4468005
  simp only [CollatzResearch.WordTrace]
  refine ⟨162961530178188434347645469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108641020118792289565096979 162961530178188434347645469)
  ·
    refine ⟨61110573816820662880367051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162961530178188434347645469 61110573816820662880367051)
    ·
      refine ⟨91665860725230994320550577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61110573816820662880367051 91665860725230994320550577)
      ·
        refine ⟨68749395543923245740412933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91665860725230994320550577 68749395543923245740412933)
        ·
          refine ⟨12890511664485608576327425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68749395543923245740412933 12890511664485608576327425)
          ·
            refine ⟨9667883748364206432245569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12890511664485608576327425 9667883748364206432245569)
            ·
              refine ⟨7250912811273154824184177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9667883748364206432245569 7250912811273154824184177)
              ·
                refine ⟨5438184608454866118138133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7250912811273154824184177 5438184608454866118138133)
                ·
                  refine ⟨254914903521321849287725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5438184608454866118138133 254914903521321849287725)
                  ·
                    rfl

theorem cell23_4468005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 6].length) (baseStart_4468005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468005 prefixEnd_4468005 := by exact prefixLift 4468005
  have htrace : WordTrace (prefixWord ++ tailWord_4468005) baseStart_4468005 baseEnd_4468005 := by
    simpa [prefixWord, tailWord_4468005, baseEnd_4468005] using wordTrace_append hprefix tailTrace_4468005
  have hstable : (prefixWord ++ tailWord_4468005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468005).length < 2 ^ (prefixWord ++ tailWord_4468005).sum := by decide
  have hdescent : baseEnd_4468005 < baseStart_4468005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468015 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 3, 1, 3]
def baseStart_4468015 : Nat := 118140960795 + 4468015 * 2 ^ 59
def prefixEnd_4468015 : Nat := 4983230072969 + 3 ^ 40 * 4468015 * 2
def baseEnd_4468015 : Nat := 2294239266498441604464479

theorem tailTrace_4468015 : CollatzResearch.WordTrace tailWord_4468015 prefixEnd_4468015 2294239266498441604464479 := by
  unfold tailWord_4468015
  simp only [CollatzResearch.WordTrace]
  refine ⟨162961894908152206055509499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108641263272101470703672999 162961894908152206055509499)
  ·
    refine ⟨244442842362228309083264249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162961894908152206055509499 244442842362228309083264249)
    ·
      refine ⟨183332131771671231812448187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244442842362228309083264249 183332131771671231812448187)
      ·
        refine ⟨274998197657506847718672281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183332131771671231812448187 274998197657506847718672281)
        ·
          refine ⟨206248648243130135789004211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274998197657506847718672281 206248648243130135789004211)
          ·
            refine ⟨309372972364695203683506317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206248648243130135789004211 309372972364695203683506317)
            ·
              refine ⟨116014864636760701381314869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 309372972364695203683506317 116014864636760701381314869)
              ·
                refine ⟨10876393559696315754498269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116014864636760701381314869 10876393559696315754498269)
                ·
                  refine ⟨4078647584886118407936851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10876393559696315754498269 4078647584886118407936851)
                  ·
                    refine ⟨6117971377329177611905277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4078647584886118407936851 6117971377329177611905277)
                    ·
                      refine ⟨2294239266498441604464479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6117971377329177611905277 2294239266498441604464479)
                      ·
                        rfl

theorem cell23_4468015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 1, 3].length) (baseStart_4468015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468015 prefixEnd_4468015 := by exact prefixLift 4468015
  have htrace : WordTrace (prefixWord ++ tailWord_4468015) baseStart_4468015 baseEnd_4468015 := by
    simpa [prefixWord, tailWord_4468015, baseEnd_4468015] using wordTrace_append hprefix tailTrace_4468015
  have hstable : (prefixWord ++ tailWord_4468015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468015).length < 2 ^ (prefixWord ++ tailWord_4468015).sum := by decide
  have hdescent : baseEnd_4468015 < baseStart_4468015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468048 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 1, 6]
def baseStart_4468048 : Nat := 118140960795 + 4468048 * 2 ^ 59
def prefixEnd_4468048 : Nat := 4983230072969 + 3 ^ 40 * 4468048 * 2
def baseEnd_4468048 : Nat := 764752070453346658450609

theorem tailTrace_4468048 : CollatzResearch.WordTrace tailWord_4468048 prefixEnd_4468048 764752070453346658450609 := by
  unfold tailWord_4468048
  simp only [CollatzResearch.WordTrace]
  refine ⟨81481549258516326345730399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108642065678021768460973865 81481549258516326345730399)
  ·
    refine ⟨122222323887774489518595599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81481549258516326345730399 122222323887774489518595599)
    ·
      refine ⟨183333485831661734277893399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122222323887774489518595599 183333485831661734277893399)
      ·
        refine ⟨275000228747492601416840099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183333485831661734277893399 275000228747492601416840099)
        ·
          refine ⟨412500343121238902125260149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275000228747492601416840099 412500343121238902125260149)
          ·
            refine ⟨38671907167616147074243139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 412500343121238902125260149 38671907167616147074243139)
            ·
              refine ⟨58007860751424220611364709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38671907167616147074243139 58007860751424220611364709)
              ·
                refine ⟨10876473890892041364630883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58007860751424220611364709 10876473890892041364630883)
                ·
                  refine ⟨16314710836338062046946325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10876473890892041364630883 16314710836338062046946325)
                  ·
                    refine ⟨764752070453346658450609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16314710836338062046946325 764752070453346658450609)
                    ·
                      rfl

theorem cell23_4468048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 1, 6].length) (baseStart_4468048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468048 prefixEnd_4468048 := by exact prefixLift 4468048
  have htrace : WordTrace (prefixWord ++ tailWord_4468048) baseStart_4468048 baseEnd_4468048 := by
    simpa [prefixWord, tailWord_4468048, baseEnd_4468048] using wordTrace_append hprefix tailTrace_4468048
  have hstable : (prefixWord ++ tailWord_4468048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468048).length < 2 ^ (prefixWord ++ tailWord_4468048).sum := by decide
  have hdescent : baseEnd_4468048 < baseStart_4468048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468049 : List Nat := [1, 2, 2, 1, 4, 1, 4, 3, 1, 1, 3]
def baseStart_4468049 : Nat := 118140960795 + 4468049 * 2 ^ 59
def prefixEnd_4468049 : Nat := 4983230072969 + 3 ^ 40 * 4468049 * 2
def baseEnd_4468049 : Nat := 2294256724840694471439323

theorem tailTrace_4468049 : CollatzResearch.WordTrace tailWord_4468049 prefixEnd_4468049 2294256724840694471439323 := by
  unfold tailWord_4468049
  simp only [CollatzResearch.WordTrace]
  refine ⟨162963134990029029862247201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108642089993352686574831467 162963134990029029862247201)
  ·
    refine ⟨122222351242521772396685401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162963134990029029862247201 122222351242521772396685401)
    ·
      refine ⟨91666763431891329297514051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122222351242521772396685401 91666763431891329297514051)
      ·
        refine ⟨137500145147836993946271077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91666763431891329297514051 137500145147836993946271077)
        ·
          refine ⟨25781277215219436364925827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137500145147836993946271077 25781277215219436364925827)
          ·
            refine ⟨38671915822829154547388741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25781277215219436364925827 38671915822829154547388741)
            ·
              refine ⟨7250984216780466477635389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38671915822829154547388741 7250984216780466477635389)
              ·
                refine ⟨2719119081292674929113271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7250984216780466477635389 2719119081292674929113271)
                ·
                  refine ⟨4078678621939012393669907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2719119081292674929113271 4078678621939012393669907)
                  ·
                    refine ⟨6118017932908518590504861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4078678621939012393669907 6118017932908518590504861)
                    ·
                      refine ⟨2294256724840694471439323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6118017932908518590504861 2294256724840694471439323)
                      ·
                        rfl

theorem cell23_4468049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 1, 1, 3].length) (baseStart_4468049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468049 prefixEnd_4468049 := by exact prefixLift 4468049
  have htrace : WordTrace (prefixWord ++ tailWord_4468049) baseStart_4468049 baseEnd_4468049 := by
    simpa [prefixWord, tailWord_4468049, baseEnd_4468049] using wordTrace_append hprefix tailTrace_4468049
  have hstable : (prefixWord ++ tailWord_4468049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468049).length < 2 ^ (prefixWord ++ tailWord_4468049).sum := by decide
  have hdescent : baseEnd_4468049 < baseStart_4468049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468092 : List Nat := [2, 2, 2, 1, 1, 1, 6, 2, 1, 2, 3]
def baseStart_4468092 : Nat := 118140960795 + 4468092 * 2 ^ 59
def prefixEnd_4468092 : Nat := 4983230072969 + 3 ^ 40 * 4468092 * 2
def baseEnd_4468092 : Nat := 2294278804508837803201625

theorem tailTrace_4468092 : CollatzResearch.WordTrace tailWord_4468092 prefixEnd_4468092 2294278804508837803201625 := by
  unfold tailWord_4468092
  simp only [CollatzResearch.WordTrace]
  refine ⟨81482351664436624103031265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108643135552582165470708353 81482351664436624103031265)
  ·
    refine ⟨61111763748327468077273449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81482351664436624103031265 61111763748327468077273449)
    ·
      refine ⟨45833822811245601057955087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61111763748327468077273449 45833822811245601057955087)
      ·
        refine ⟨68750734216868401586932631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45833822811245601057955087 68750734216868401586932631)
        ·
          refine ⟨103126101325302602380398947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68750734216868401586932631 103126101325302602380398947)
          ·
            refine ⟨154689151987953903570598421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103126101325302602380398947 154689151987953903570598421)
            ·
              refine ⟨7251053999435339229871801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 154689151987953903570598421 7251053999435339229871801)
              ·
                refine ⟨5438290499576504422403851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7251053999435339229871801 5438290499576504422403851)
                ·
                  refine ⟨8157435749364756633605777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5438290499576504422403851 8157435749364756633605777)
                  ·
                    refine ⟨6118076812023567475204333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8157435749364756633605777 6118076812023567475204333)
                    ·
                      refine ⟨2294278804508837803201625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6118076812023567475204333 2294278804508837803201625)
                      ·
                        rfl

theorem cell23_4468092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_4468092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468092 prefixEnd_4468092 := by exact prefixLift 4468092
  have htrace : WordTrace (prefixWord ++ tailWord_4468092) baseStart_4468092 baseEnd_4468092 := by
    simpa [prefixWord, tailWord_4468092, baseEnd_4468092] using wordTrace_append hprefix tailTrace_4468092
  have hstable : (prefixWord ++ tailWord_4468092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468092).length < 2 ^ (prefixWord ++ tailWord_4468092).sum := by decide
  have hdescent : baseEnd_4468092 < baseStart_4468092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468122 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3]
def baseStart_4468122 : Nat := 118140960795 + 4468122 * 2 ^ 59
def prefixEnd_4468122 : Nat := 4983230072969 + 3 ^ 40 * 4468122 * 2
def baseEnd_4468122 : Nat := 2294294208928472685826487

theorem tailTrace_4468122 : CollatzResearch.WordTrace tailWord_4468122 prefixEnd_4468122 2294294208928472685826487 := by
  unfold tailWord_4468122
  simp only [CollatzResearch.WordTrace]
  refine ⟨40741449379691140832413655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108643865012509708886436413 40741449379691140832413655)
  ·
    refine ⟨61112174069536711248620483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40741449379691140832413655 61112174069536711248620483)
    ·
      refine ⟨91668261104305066872930725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61112174069536711248620483 91668261104305066872930725)
      ·
        refine ⟨17187798957057200038674511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91668261104305066872930725 17187798957057200038674511)
        ·
          refine ⟨25781698435585800058011767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17187798957057200038674511 25781698435585800058011767)
          ·
            refine ⟨38672547653378700087017651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25781698435585800058011767 38672547653378700087017651)
            ·
              refine ⟨58008821480068050130526477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38672547653378700087017651 58008821480068050130526477)
              ·
                refine ⟨21753308055025518798947429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58008821480068050130526477 21753308055025518798947429)
                ·
                  refine ⟨4078745260317284774802643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21753308055025518798947429 4078745260317284774802643)
                  ·
                    refine ⟨6118117890475927162203965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4078745260317284774802643 6118117890475927162203965)
                    ·
                      refine ⟨2294294208928472685826487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6118117890475927162203965 2294294208928472685826487)
                      ·
                        rfl

theorem cell23_4468122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_4468122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468122 prefixEnd_4468122 := by exact prefixLift 4468122
  have htrace : WordTrace (prefixWord ++ tailWord_4468122) baseStart_4468122 baseEnd_4468122 := by
    simpa [prefixWord, tailWord_4468122, baseEnd_4468122] using wordTrace_append hprefix tailTrace_4468122
  have hstable : (prefixWord ++ tailWord_4468122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468122).length < 2 ^ (prefixWord ++ tailWord_4468122).sum := by decide
  have hdescent : baseEnd_4468122 < baseStart_4468122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468132 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 3, 3, 2]
def baseStart_4468132 : Nat := 118140960795 + 4468132 * 2 ^ 59
def prefixEnd_4468132 : Nat := 4983230072969 + 3 ^ 40 * 4468132 * 2
def baseEnd_4468132 : Nat := 2294299343735017646701441

theorem tailTrace_4468132 : CollatzResearch.WordTrace tailWord_4468132 prefixEnd_4468132 2294299343735017646701441 := by
  unfold tailWord_4468132
  simp only [CollatzResearch.WordTrace]
  refine ⟨81483081124364167518759325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108644108165818890025012433 81483081124364167518759325)
  ·
    refine ⟨30556155421636562819534747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81483081124364167518759325 30556155421636562819534747)
    ·
      refine ⟨45834233132454844229302121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30556155421636562819534747 45834233132454844229302121)
      ·
        refine ⟨34375674849341133171976591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45834233132454844229302121 34375674849341133171976591)
        ·
          refine ⟨51563512274011699757964887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34375674849341133171976591 51563512274011699757964887)
          ·
            refine ⟨77345268411017549636947331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51563512274011699757964887 77345268411017549636947331)
            ·
              refine ⟨116017902616526324455420997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77345268411017549636947331 116017902616526324455420997)
              ·
                refine ⟨21753356740598685835391437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116017902616526324455420997 21753356740598685835391437)
                ·
                  refine ⟨8157508777724507188271789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21753356740598685835391437 8157508777724507188271789)
                  ·
                    refine ⟨3059065791646690195601921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8157508777724507188271789 3059065791646690195601921)
                    ·
                      refine ⟨2294299343735017646701441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3059065791646690195601921 2294299343735017646701441)
                      ·
                        rfl

theorem cell23_4468132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_4468132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468132 prefixEnd_4468132 := by exact prefixLift 4468132
  have htrace : WordTrace (prefixWord ++ tailWord_4468132) baseStart_4468132 baseEnd_4468132 := by
    simpa [prefixWord, tailWord_4468132, baseEnd_4468132] using wordTrace_append hprefix tailTrace_4468132
  have hstable : (prefixWord ++ tailWord_4468132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468132).length < 2 ^ (prefixWord ++ tailWord_4468132).sum := by decide
  have hdescent : baseEnd_4468132 < baseStart_4468132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468149 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 3, 3, 2]
def baseStart_4468149 : Nat := 118140960795 + 4468149 * 2 ^ 59
def prefixEnd_4468149 : Nat := 4983230072969 + 3 ^ 40 * 4468149 * 2
def baseEnd_4468149 : Nat := 2294308072906144080188863

theorem tailTrace_4468149 : CollatzResearch.WordTrace tailWord_4468149 prefixEnd_4468149 2294308072906144080188863 := by
  unfold tailWord_4468149
  simp only [CollatzResearch.WordTrace]
  refine ⟨162966782289666746940887501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108644521526444497960591667 162966782289666746940887501)
  ·
    refine ⟨61112543358625030102832813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162966782289666746940887501 61112543358625030102832813)
    ·
      refine ⟨22917203759484386288562305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61112543358625030102832813 22917203759484386288562305)
      ·
        refine ⟨17187902819613289716421729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22917203759484386288562305 17187902819613289716421729)
        ·
          refine ⟨12890927114709967287316297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17187902819613289716421729 12890927114709967287316297)
          ·
            refine ⟨9668195336032475465487223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12890927114709967287316297 9668195336032475465487223)
            ·
              refine ⟨14502293004048713198230835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9668195336032475465487223 14502293004048713198230835)
              ·
                refine ⟨21753439506073069797346253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14502293004048713198230835 21753439506073069797346253)
                ·
                  refine ⟨8157539814777401174004845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21753439506073069797346253 8157539814777401174004845)
                  ·
                    refine ⟨3059077430541525440251817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8157539814777401174004845 3059077430541525440251817)
                    ·
                      refine ⟨2294308072906144080188863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3059077430541525440251817 2294308072906144080188863)
                      ·
                        rfl

theorem cell23_4468149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_4468149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468149 prefixEnd_4468149 := by exact prefixLift 4468149
  have htrace : WordTrace (prefixWord ++ tailWord_4468149) baseStart_4468149 baseEnd_4468149 := by
    simpa [prefixWord, tailWord_4468149, baseEnd_4468149] using wordTrace_append hprefix tailTrace_4468149
  have hstable : (prefixWord ++ tailWord_4468149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468149).length < 2 ^ (prefixWord ++ tailWord_4468149).sum := by decide
  have hdescent : baseEnd_4468149 < baseStart_4468149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468202 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 7]
def baseStart_4468202 : Nat := 118140960795 + 4468202 * 2 ^ 59
def prefixEnd_4468202 : Nat := 4983230072969 + 3 ^ 40 * 4468202 * 2
def baseEnd_4468202 : Nat := 254926143042314708091791

theorem tailTrace_4468202 : CollatzResearch.WordTrace tailWord_4468202 prefixEnd_4468202 254926143042314708091791 := by
  unfold tailWord_4468202
  simp only [CollatzResearch.WordTrace]
  refine ⟨40742178839618684248141715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108645810238983157995044573 40742178839618684248141715)
  ·
    refine ⟨61113268259428026372212573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40742178839618684248141715 61113268259428026372212573)
    ·
      refine ⟨22917475597285509889579715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61113268259428026372212573 22917475597285509889579715)
      ·
        refine ⟨34376213395928264834369573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22917475597285509889579715 34376213395928264834369573)
        ·
          refine ⟨6445540011736549656444295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34376213395928264834369573 6445540011736549656444295)
          ·
            refine ⟨9668310017604824484666443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6445540011736549656444295 9668310017604824484666443)
            ·
              refine ⟨14502465026407236726999665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9668310017604824484666443 14502465026407236726999665)
              ·
                refine ⟨10876848769805427545249749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14502465026407236726999665 10876848769805427545249749)
                ·
                  refine ⟨254926143042314708091791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10876848769805427545249749 254926143042314708091791)
                  ·
                    rfl

theorem cell23_4468202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 7].length) (baseStart_4468202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468202 prefixEnd_4468202 := by exact prefixLift 4468202
  have htrace : WordTrace (prefixWord ++ tailWord_4468202) baseStart_4468202 baseEnd_4468202 := by
    simpa [prefixWord, tailWord_4468202, baseEnd_4468202] using wordTrace_append hprefix tailTrace_4468202
  have hstable : (prefixWord ++ tailWord_4468202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468202).length < 2 ^ (prefixWord ++ tailWord_4468202).sum := by decide
  have hdescent : baseEnd_4468202 < baseStart_4468202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468215 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 2, 5]
def baseStart_4468215 : Nat := 118140960795 + 4468215 * 2 ^ 59
def prefixEnd_4468215 : Nat := 4983230072969 + 3 ^ 40 * 4468215 * 2
def baseEnd_4468215 : Nat := 764780654209780273987853

theorem tailTrace_4468215 : CollatzResearch.WordTrace tailWord_4468215 prefixEnd_4468215 764780654209780273987853 := by
  unfold tailWord_4468215
  simp only [CollatzResearch.WordTrace]
  refine ⟨162969189507427640212790099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108646126338285093475193399 162969189507427640212790099)
  ·
    refine ⟨244453784261141460319185149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162969189507427640212790099 244453784261141460319185149)
    ·
      refine ⟨91670169097928047619694431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244453784261141460319185149 91670169097928047619694431)
      ·
        refine ⟨137505253646892071429541647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91670169097928047619694431 137505253646892071429541647)
        ·
          refine ⟨206257880470338107144312471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137505253646892071429541647 206257880470338107144312471)
          ·
            refine ⟨309386820705507160716468707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206257880470338107144312471 309386820705507160716468707)
            ·
              refine ⟨464080231058260741074703061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309386820705507160716468707 464080231058260741074703061)
              ·
                refine ⟨10876880415427986118938353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 464080231058260741074703061 10876880415427986118938353)
                ·
                  refine ⟨8157660311570989589203765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10876880415427986118938353 8157660311570989589203765)
                  ·
                    refine ⟨764780654209780273987853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8157660311570989589203765 764780654209780273987853)
                    ·
                      rfl

theorem cell23_4468215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_4468215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468215 prefixEnd_4468215 := by exact prefixLift 4468215
  have htrace : WordTrace (prefixWord ++ tailWord_4468215) baseStart_4468215 baseEnd_4468215 := by
    simpa [prefixWord, tailWord_4468215, baseEnd_4468215] using wordTrace_append hprefix tailTrace_4468215
  have hstable : (prefixWord ++ tailWord_4468215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468215).length < 2 ^ (prefixWord ++ tailWord_4468215).sum := by decide
  have hdescent : baseEnd_4468215 < baseStart_4468215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468272 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 3]
def baseStart_4468272 : Nat := 118140960795 + 4468272 * 2 ^ 59
def prefixEnd_4468272 : Nat := 4983230072969 + 3 ^ 40 * 4468272 * 2
def baseEnd_4468272 : Nat := 2294371231026647098950797

theorem tailTrace_4468272 : CollatzResearch.WordTrace tailWord_4468272 prefixEnd_4468272 2294371231026647098950797 := by
  unfold tailWord_4468272
  simp only [CollatzResearch.WordTrace]
  refine ⟨81485634234110569473807535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108647512312147425965076713 81485634234110569473807535)
  ·
    refine ⟨122228451351165854210711303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81485634234110569473807535 122228451351165854210711303)
    ·
      refine ⟨183342677026748781316066955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122228451351165854210711303 183342677026748781316066955)
      ·
        refine ⟨275014015540123171974100433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183342677026748781316066955 275014015540123171974100433)
        ·
          refine ⟨206260511655092378980575325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275014015540123171974100433 206260511655092378980575325)
          ·
            refine ⟨77347691870659642117715747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206260511655092378980575325 77347691870659642117715747)
            ·
              refine ⟨116021537805989463176573621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77347691870659642117715747 116021537805989463176573621)
              ·
                refine ⟨10877019169311512172803777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116021537805989463176573621 10877019169311512172803777)
                ·
                  refine ⟨8157764376983634129602833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10877019169311512172803777 8157764376983634129602833)
                  ·
                    refine ⟨6118323282737725597202125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8157764376983634129602833 6118323282737725597202125)
                    ·
                      refine ⟨2294371231026647098950797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6118323282737725597202125 2294371231026647098950797)
                      ·
                        rfl

theorem cell23_4468272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 3].length) (baseStart_4468272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468272 prefixEnd_4468272 := by exact prefixLift 4468272
  have htrace : WordTrace (prefixWord ++ tailWord_4468272) baseStart_4468272 baseEnd_4468272 := by
    simpa [prefixWord, tailWord_4468272, baseEnd_4468272] using wordTrace_append hprefix tailTrace_4468272
  have hstable : (prefixWord ++ tailWord_4468272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468272).length < 2 ^ (prefixWord ++ tailWord_4468272).sum := by decide
  have hdescent : baseEnd_4468272 < baseStart_4468272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468275 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 8]
def baseStart_4468275 : Nat := 118140960795 + 4468275 * 2 ^ 59
def prefixEnd_4468275 : Nat := 4983230072969 + 3 ^ 40 * 4468275 * 2
def baseEnd_4468275 : Nat := 254930307940956731912587

theorem tailTrace_4468275 : CollatzResearch.WordTrace tailWord_4468275 prefixEnd_4468275 254930307940956731912587 := by
  unfold tailWord_4468275
  simp only [CollatzResearch.WordTrace]
  refine ⟨162971377887210270459974279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108647585258140180306649519 162971377887210270459974279)
  ·
    refine ⟨244457066830815405689961419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162971377887210270459974279 244457066830815405689961419)
    ·
      refine ⟨366685600246223108534942129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244457066830815405689961419 366685600246223108534942129)
      ·
        refine ⟨275014200184667331401206597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366685600246223108534942129 275014200184667331401206597)
        ·
          refine ⟨51565162534625124637726237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 275014200184667331401206597 51565162534625124637726237)
          ·
            refine ⟨19336935950484421739147339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51565162534625124637726237 19336935950484421739147339)
            ·
              refine ⟨29005403925726632608721009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19336935950484421739147339 29005403925726632608721009)
              ·
                refine ⟨21754052944294974456540757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29005403925726632608721009 21754052944294974456540757)
                ·
                  refine ⟨254930307940956731912587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21754052944294974456540757 254930307940956731912587)
                  ·
                    rfl

theorem cell23_4468275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 8].length) (baseStart_4468275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468275 prefixEnd_4468275 := by exact prefixLift 4468275
  have htrace : WordTrace (prefixWord ++ tailWord_4468275) baseStart_4468275 baseEnd_4468275 := by
    simpa [prefixWord, tailWord_4468275, baseEnd_4468275] using wordTrace_append hprefix tailTrace_4468275
  have hstable : (prefixWord ++ tailWord_4468275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468275).length < 2 ^ (prefixWord ++ tailWord_4468275).sum := by decide
  have hdescent : baseEnd_4468275 < baseStart_4468275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468289 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_4468289 : Nat := 118140960795 + 4468289 * 2 ^ 59
def prefixEnd_4468289 : Nat := 4983230072969 + 3 ^ 40 * 4468289 * 2
def baseEnd_4468289 : Nat := 2294379960197773532438219

theorem tailTrace_4468289 : CollatzResearch.WordTrace tailWord_4468289 prefixEnd_4468289 2294379960197773532438219 := by
  unfold tailWord_4468289
  simp only [CollatzResearch.WordTrace]
  refine ⟨162971888509159550850983921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108647925672773033900655947 162971888509159550850983921)
  ·
    refine ⟨122228916381869663138237941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162971888509159550850983921 122228916381869663138237941)
    ·
      refine ⟨11458960910800280919209807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122228916381869663138237941 11458960910800280919209807)
      ·
        refine ⟨17188441366200421378814711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11458960910800280919209807 17188441366200421378814711)
        ·
          refine ⟨25782662049300632068222067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17188441366200421378814711 25782662049300632068222067)
          ·
            refine ⟨38673993073950948102333101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25782662049300632068222067 38673993073950948102333101)
            ·
              refine ⟨14502747402731605538374913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38673993073950948102333101 14502747402731605538374913)
              ·
                refine ⟨10877060552048704153781185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14502747402731605538374913 10877060552048704153781185)
                ·
                  refine ⟨8157795414036528115335889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10877060552048704153781185 8157795414036528115335889)
                  ·
                    refine ⟨6118346560527396086501917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8157795414036528115335889 6118346560527396086501917)
                    ·
                      refine ⟨2294379960197773532438219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6118346560527396086501917 2294379960197773532438219)
                      ·
                        rfl

theorem cell23_4468289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_4468289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468289 prefixEnd_4468289 := by exact prefixLift 4468289
  have htrace : WordTrace (prefixWord ++ tailWord_4468289) baseStart_4468289 baseEnd_4468289 := by
    simpa [prefixWord, tailWord_4468289, baseEnd_4468289] using wordTrace_append hprefix tailTrace_4468289
  have hstable : (prefixWord ++ tailWord_4468289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468289).length < 2 ^ (prefixWord ++ tailWord_4468289).sum := by decide
  have hdescent : baseEnd_4468289 < baseStart_4468289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468329 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 2, 3, 2]
def baseStart_4468329 : Nat := 118140960795 + 4468329 * 2 ^ 59
def prefixEnd_4468329 : Nat := 4983230072969 + 3 ^ 40 * 4468329 * 2
def baseEnd_4468329 : Nat := 2294400499423953375938035

theorem tailTrace_4468329 : CollatzResearch.WordTrace tailWord_4468329 prefixEnd_4468329 2294400499423953375938035 := by
  unfold tailWord_4468329
  simp only [CollatzResearch.WordTrace]
  refine ⟨162973347429014637682440041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108648898286009758454960027 162973347429014637682440041)
  ·
    refine ⟨122230010571760978261830031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162973347429014637682440041 122230010571760978261830031)
    ·
      refine ⟨183345015857641467392745047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122230010571760978261830031 183345015857641467392745047)
      ·
        refine ⟨275017523786462201089117571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183345015857641467392745047 275017523786462201089117571)
        ·
          refine ⟨412526285679693301633676357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275017523786462201089117571 412526285679693301633676357)
          ·
            refine ⟨77348678564942494056314317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 412526285679693301633676357 77348678564942494056314317)
            ·
              refine ⟨29005754461853435271117869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77348678564942494056314317 29005754461853435271117869)
              ·
                refine ⟨10877157923195038226669201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29005754461853435271117869 10877157923195038226669201)
                ·
                  refine ⟨8157868442396278670001901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10877157923195038226669201 8157868442396278670001901)
                  ·
                    refine ⟨3059200665898604501250713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8157868442396278670001901 3059200665898604501250713)
                    ·
                      refine ⟨2294400499423953375938035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3059200665898604501250713 2294400499423953375938035)
                      ·
                        rfl

theorem cell23_4468329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 3, 2].length) (baseStart_4468329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468329 prefixEnd_4468329 := by exact prefixLift 4468329
  have htrace : WordTrace (prefixWord ++ tailWord_4468329) baseStart_4468329 baseEnd_4468329 := by
    simpa [prefixWord, tailWord_4468329, baseEnd_4468329] using wordTrace_append hprefix tailTrace_4468329
  have hstable : (prefixWord ++ tailWord_4468329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468329).length < 2 ^ (prefixWord ++ tailWord_4468329).sum := by decide
  have hdescent : baseEnd_4468329 < baseStart_4468329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468353 : List Nat := [1, 2, 4, 2, 1, 3, 1, 4, 1, 1, 3]
def baseStart_4468353 : Nat := 118140960795 + 4468353 * 2 ^ 59
def prefixEnd_4468353 : Nat := 4983230072969 + 3 ^ 40 * 4468353 * 2
def baseEnd_4468353 : Nat := 2294412822959661282037925

theorem tailTrace_4468353 : CollatzResearch.WordTrace tailWord_4468353 prefixEnd_4468353 2294412822959661282037925 := by
  unfold tailWord_4468353
  simp only [CollatzResearch.WordTrace]
  refine ⟨162974222780927689781313713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108649481853951793187542475 162974222780927689781313713)
  ·
    refine ⟨122230667085695767335985285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162974222780927689781313713 122230667085695767335985285)
    ·
      refine ⟨22918250078567956375497241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122230667085695767335985285 22918250078567956375497241)
      ·
        refine ⟨17188687558925967281622931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22918250078567956375497241 17188687558925967281622931)
        ·
          refine ⟨25783031338388950922434397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17188687558925967281622931 25783031338388950922434397)
          ·
            refine ⟨9668636751895856595912899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25783031338388950922434397 9668636751895856595912899)
            ·
              refine ⟨14502955127843784893869349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9668636751895856595912899 14502955127843784893869349)
              ·
                refine ⟨2719304086470709667600503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14502955127843784893869349 2719304086470709667600503)
                ·
                  refine ⟨4078956129706064501400755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2719304086470709667600503 4078956129706064501400755)
                  ·
                    refine ⟨6118434194559096752101133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4078956129706064501400755 6118434194559096752101133)
                    ·
                      refine ⟨2294412822959661282037925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6118434194559096752101133 2294412822959661282037925)
                      ·
                        rfl

theorem cell23_4468353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_4468353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468353 prefixEnd_4468353 := by exact prefixLift 4468353
  have htrace : WordTrace (prefixWord ++ tailWord_4468353) baseStart_4468353 baseEnd_4468353 := by
    simpa [prefixWord, tailWord_4468353, baseEnd_4468353] using wordTrace_append hprefix tailTrace_4468353
  have hstable : (prefixWord ++ tailWord_4468353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468353).length < 2 ^ (prefixWord ++ tailWord_4468353).sum := by decide
  have hdescent : baseEnd_4468353 < baseStart_4468353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468376 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 5, 2, 2]
def baseStart_4468376 : Nat := 118140960795 + 4468376 * 2 ^ 59
def prefixEnd_4468376 : Nat := 4983230072969 + 3 ^ 40 * 4468376 * 2
def baseEnd_4468376 : Nat := 2294424633014714692050319

theorem tailTrace_4468376 : CollatzResearch.WordTrace tailWord_4468376 prefixEnd_4468376 2294424633014714692050319 := by
  unfold tailWord_4468376
  simp only [CollatzResearch.WordTrace]
  refine ⟨81487530829922182354700491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108650041106562909806267321 81487530829922182354700491)
  ·
    refine ⟨122231296244883273532050737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81487530829922182354700491 122231296244883273532050737)
    ·
      refine ⟨91673472183662455149038053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122231296244883273532050737 91673472183662455149038053)
      ·
        refine ⟨17188776034436710340444635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91673472183662455149038053 17188776034436710340444635)
        ·
          refine ⟨25783164051655065510666953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17188776034436710340444635 25783164051655065510666953)
          ·
            refine ⟨19337373038741299133000215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25783164051655065510666953 19337373038741299133000215)
            ·
              refine ⟨29006059558111948699500323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19337373038741299133000215 29006059558111948699500323)
              ·
                refine ⟨43509089337167923049250485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29006059558111948699500323 43509089337167923049250485)
                ·
                  refine ⟨4078977125359492785867233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43509089337167923049250485 4078977125359492785867233)
                  ·
                    refine ⟨3059232844019619589400425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4078977125359492785867233 3059232844019619589400425)
                    ·
                      refine ⟨2294424633014714692050319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3059232844019619589400425 2294424633014714692050319)
                      ·
                        rfl

theorem cell23_4468376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_4468376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468376 prefixEnd_4468376 := by exact prefixLift 4468376
  have htrace : WordTrace (prefixWord ++ tailWord_4468376) baseStart_4468376 baseEnd_4468376 := by
    simpa [prefixWord, tailWord_4468376, baseEnd_4468376] using wordTrace_append hprefix tailTrace_4468376
  have hstable : (prefixWord ++ tailWord_4468376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468376).length < 2 ^ (prefixWord ++ tailWord_4468376).sum := by decide
  have hdescent : baseEnd_4468376 < baseStart_4468376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468380 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 2, 3, 2]
def baseStart_4468380 : Nat := 118140960795 + 4468380 * 2 ^ 59
def prefixEnd_4468380 : Nat := 4983230072969 + 3 ^ 40 * 4468380 * 2
def baseEnd_4468380 : Nat := 2294426686937332676400301

theorem tailTrace_4468380 : CollatzResearch.WordTrace tailWord_4468380 prefixEnd_4468380 2294426686937332676400301 := by
  unfold tailWord_4468380
  simp only [CollatzResearch.WordTrace]
  refine ⟨81487603775914936696273297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108650138367886582261697729 81487603775914936696273297)
  ·
    refine ⟨61115702831936202522204973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81487603775914936696273297 61115702831936202522204973)
    ·
      refine ⟨22918388561976075945826865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61115702831936202522204973 22918388561976075945826865)
      ·
        refine ⟨17188791421482056959370149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22918388561976075945826865 17188791421482056959370149)
        ·
          refine ⟨3222898391527885679881903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17188791421482056959370149 3222898391527885679881903)
          ·
            refine ⟨4834347587291828519822855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3222898391527885679881903 4834347587291828519822855)
            ·
              refine ⟨7251521380937742779734283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4834347587291828519822855 7251521380937742779734283)
              ·
                refine ⟨10877282071406614169601425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7251521380937742779734283 10877282071406614169601425)
                ·
                  refine ⟨8157961553554960627201069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10877282071406614169601425 8157961553554960627201069)
                  ·
                    refine ⟨3059235582583110235200401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8157961553554960627201069 3059235582583110235200401)
                    ·
                      refine ⟨2294426686937332676400301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3059235582583110235200401 2294426686937332676400301)
                      ·
                        rfl

theorem cell23_4468380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_4468380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468380 prefixEnd_4468380 := by exact prefixLift 4468380
  have htrace : WordTrace (prefixWord ++ tailWord_4468380) baseStart_4468380 baseEnd_4468380 := by
    simpa [prefixWord, tailWord_4468380, baseEnd_4468380] using wordTrace_append hprefix tailTrace_4468380
  have hstable : (prefixWord ++ tailWord_4468380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468380).length < 2 ^ (prefixWord ++ tailWord_4468380).sum := by decide
  have hdescent : baseEnd_4468380 < baseStart_4468380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468444 : List Nat := [2, 2, 5, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_4468444 : Nat := 118140960795 + 4468444 * 2 ^ 59
def prefixEnd_4468444 : Nat := 4983230072969 + 3 ^ 40 * 4468444 * 2
def baseEnd_4468444 : Nat := 2294459549699220426000007

theorem tailTrace_4468444 : CollatzResearch.WordTrace tailWord_4468444 prefixEnd_4468444 2294459549699220426000007 := by
  unfold tailWord_4468444
  simp only [CollatzResearch.WordTrace]
  refine ⟨81488770911799006161438193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108651694549065341548584257 81488770911799006161438193)
  ·
    refine ⟨61116578183849254621078645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81488770911799006161438193 61116578183849254621078645)
    ·
      refine ⟨5729679204735867620726123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61116578183849254621078645 5729679204735867620726123)
      ·
        refine ⟨8594518807103801431089185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5729679204735867620726123 8594518807103801431089185)
        ·
          refine ⟨6445889105327851073316889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8594518807103801431089185 6445889105327851073316889)
          ·
            refine ⟨4834416828995888304987667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6445889105327851073316889 4834416828995888304987667)
            ·
              refine ⟨7251625243493832457481501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4834416828995888304987667 7251625243493832457481501)
              ·
                refine ⟨2719359466310187171555563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7251625243493832457481501 2719359466310187171555563)
                ·
                  refine ⟨4079039199465280757333345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2719359466310187171555563 4079039199465280757333345)
                  ·
                    refine ⟨3059279399598960568000009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4079039199465280757333345 3059279399598960568000009)
                    ·
                      refine ⟨2294459549699220426000007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3059279399598960568000009 2294459549699220426000007)
                      ·
                        rfl

theorem cell23_4468444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_4468444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468444 prefixEnd_4468444 := by exact prefixLift 4468444
  have htrace : WordTrace (prefixWord ++ tailWord_4468444) baseStart_4468444 baseEnd_4468444 := by
    simpa [prefixWord, tailWord_4468444, baseEnd_4468444] using wordTrace_append hprefix tailTrace_4468444
  have hstable : (prefixWord ++ tailWord_4468444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468444).length < 2 ^ (prefixWord ++ tailWord_4468444).sum := by decide
  have hdescent : baseEnd_4468444 < baseStart_4468444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468472 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 7]
def baseStart_4468472 : Nat := 118140960795 + 4468472 * 2 ^ 59
def prefixEnd_4468472 : Nat := 4983230072969 + 3 ^ 40 * 4468472 * 2
def baseEnd_4468472 : Nat := 254941547461949590716653

theorem tailTrace_4468472 : CollatzResearch.WordTrace tailWord_4468472 prefixEnd_4468472 254941547461949590716653 := by
  unfold tailWord_4468472
  simp only [CollatzResearch.WordTrace]
  refine ⟨81489281533748286552447835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108652375378331048736597113 81489281533748286552447835)
  ·
    refine ⟨122233922300622429828671753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81489281533748286552447835 122233922300622429828671753)
    ·
      refine ⟨91675441725466822371503815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122233922300622429828671753 91675441725466822371503815)
      ·
        refine ⟨137513162588200233557255723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91675441725466822371503815 137513162588200233557255723)
        ·
          refine ⟨206269743882300350335883585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137513162588200233557255723 206269743882300350335883585)
          ·
            refine ⟨154702307911725262751912689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206269743882300350335883585 154702307911725262751912689)
            ·
              refine ⟨116026730933793947063934517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154702307911725262751912689 116026730933793947063934517)
              ·
                refine ⟨10877506025043182537243861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116026730933793947063934517 10877506025043182537243861)
                ·
                  refine ⟨254941547461949590716653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10877506025043182537243861 254941547461949590716653)
                  ·
                    rfl

theorem cell23_4468472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 7].length) (baseStart_4468472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468472 prefixEnd_4468472 := by exact prefixLift 4468472
  have htrace : WordTrace (prefixWord ++ tailWord_4468472) baseStart_4468472 baseEnd_4468472 := by
    simpa [prefixWord, tailWord_4468472, baseEnd_4468472] using wordTrace_append hprefix tailTrace_4468472
  have hstable : (prefixWord ++ tailWord_4468472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468472).length < 2 ^ (prefixWord ++ tailWord_4468472).sum := by decide
  have hdescent : baseEnd_4468472 < baseStart_4468472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468487 : List Nat := [1, 1, 4, 4, 3, 1, 1, 2, 1, 3, 2]
def baseStart_4468487 : Nat := 118140960795 + 4468487 * 2 ^ 59
def prefixEnd_4468487 : Nat := 4983230072969 + 3 ^ 40 * 4468487 * 2
def baseEnd_4468487 : Nat := 2294481629367363757762309

theorem tailTrace_4468487 : CollatzResearch.WordTrace tailWord_4468487 prefixEnd_4468487 2294481629367363757762309 := by
  unfold tailWord_4468487
  simp only [CollatzResearch.WordTrace]
  refine ⟨162979110162442230666691715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108652740108294820444461143 162979110162442230666691715)
  ·
    refine ⟨244468665243663346000037573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162979110162442230666691715 244468665243663346000037573)
    ·
      refine ⟨45837874733186877375007045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 244468665243663346000037573 45837874733186877375007045)
      ·
        refine ⟨8594601512472539507813821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45837874733186877375007045 8594601512472539507813821)
        ·
          refine ⟨3222975567177202315430183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8594601512472539507813821 3222975567177202315430183)
          ·
            refine ⟨4834463350765803473145275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3222975567177202315430183 4834463350765803473145275)
            ·
              refine ⟨7251695026148705209717913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4834463350765803473145275 7251695026148705209717913)
              ·
                refine ⟨5438771269611528907288435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7251695026148705209717913 5438771269611528907288435)
                ·
                  refine ⟨8158156904417293360932653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5438771269611528907288435 8158156904417293360932653)
                  ·
                    refine ⟨3059308839156485010349745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8158156904417293360932653 3059308839156485010349745)
                    ·
                      refine ⟨2294481629367363757762309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3059308839156485010349745 2294481629367363757762309)
                      ·
                        rfl

theorem cell23_4468487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_4468487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468487 prefixEnd_4468487 := by exact prefixLift 4468487
  have htrace : WordTrace (prefixWord ++ tailWord_4468487) baseStart_4468487 baseEnd_4468487 := by
    simpa [prefixWord, tailWord_4468487, baseEnd_4468487] using wordTrace_append hprefix tailTrace_4468487
  have hstable : (prefixWord ++ tailWord_4468487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468487).length < 2 ^ (prefixWord ++ tailWord_4468487).sum := by decide
  have hdescent : baseEnd_4468487 < baseStart_4468487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468529 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 1, 2, 5]
def baseStart_4468529 : Nat := 118140960795 + 4468529 * 2 ^ 59
def prefixEnd_4468529 : Nat := 4983230072969 + 3 ^ 40 * 4468529 * 2
def baseEnd_4468529 : Nat := 2294503195554852593437115

theorem tailTrace_4468529 : CollatzResearch.WordTrace tailWord_4468529 prefixEnd_4468529 2294503195554852593437115 := by
  unfold tailWord_4468529
  simp only [CollatzResearch.WordTrace]
  refine ⟨162980642028290071839720641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108653761352193381226480427 162980642028290071839720641)
  ·
    refine ⟨122235481521217553879790481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162980642028290071839720641 122235481521217553879790481)
    ·
      refine ⟨91676611140913165409842861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122235481521217553879790481 91676611140913165409842861)
      ·
        refine ⟨34378729177842437028691073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91676611140913165409842861 34378729177842437028691073)
        ·
          refine ⟨25784046883381827771518305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34378729177842437028691073 25784046883381827771518305)
          ·
            refine ⟨19338035162536370828638729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25784046883381827771518305 19338035162536370828638729)
            ·
              refine ⟨14503526371902278121479047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19338035162536370828638729 14503526371902278121479047)
              ·
                refine ⟨21755289557853417182218571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14503526371902278121479047 21755289557853417182218571)
                ·
                  refine ⟨32632934336780125773327857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21755289557853417182218571 32632934336780125773327857)
                  ·
                    refine ⟨24474700752585094329995893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32632934336780125773327857 24474700752585094329995893)
                    ·
                      refine ⟨2294503195554852593437115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24474700752585094329995893 2294503195554852593437115)
                      ·
                        rfl

theorem cell23_4468529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_4468529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468529 prefixEnd_4468529 := by exact prefixLift 4468529
  have htrace : WordTrace (prefixWord ++ tailWord_4468529) baseStart_4468529 baseEnd_4468529 := by
    simpa [prefixWord, tailWord_4468529, baseEnd_4468529] using wordTrace_append hprefix tailTrace_4468529
  have hstable : (prefixWord ++ tailWord_4468529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468529).length < 2 ^ (prefixWord ++ tailWord_4468529).sum := by decide
  have hdescent : baseEnd_4468529 < baseStart_4468529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468556 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 1, 3, 4]
def baseStart_4468556 : Nat := 118140960795 + 4468556 * 2 ^ 59
def prefixEnd_4468556 : Nat := 4983230072969 + 3 ^ 40 * 4468556 * 2
def baseEnd_4468556 : Nat := 2294517059532523987799491

theorem tailTrace_4468556 : CollatzResearch.WordTrace tailWord_4468556 prefixEnd_4468556 2294517059532523987799491 := by
  unfold tailWord_4468556
  simp only [CollatzResearch.WordTrace]
  refine ⟨81490813399596127725476761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108654417866128170300635681 81490813399596127725476761)
  ·
    refine ⟨61118110049697095794107571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81490813399596127725476761 61118110049697095794107571)
    ·
      refine ⟨91677165074545643691161357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61118110049697095794107571 91677165074545643691161357)
      ·
        refine ⟨34378936902954616384185509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91677165074545643691161357 34378936902954616384185509)
        ·
          refine ⟨6446050669303990572034783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34378936902954616384185509 6446050669303990572034783)
          ·
            refine ⟨9669076003955985858052175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6446050669303990572034783 9669076003955985858052175)
            ·
              refine ⟨14503614005933978787078263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9669076003955985858052175 14503614005933978787078263)
              ·
                refine ⟨21755421008900968180617395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14503614005933978787078263 21755421008900968180617395)
                ·
                  refine ⟨32633131513351452270926093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21755421008900968180617395 32633131513351452270926093)
                  ·
                    refine ⟨12237424317506794601597285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32633131513351452270926093 12237424317506794601597285)
                    ·
                      refine ⟨2294517059532523987799491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12237424317506794601597285 2294517059532523987799491)
                      ·
                        rfl

theorem cell23_4468556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_4468556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468556 prefixEnd_4468556 := by exact prefixLift 4468556
  have htrace : WordTrace (prefixWord ++ tailWord_4468556) baseStart_4468556 baseEnd_4468556 := by
    simpa [prefixWord, tailWord_4468556, baseEnd_4468556] using wordTrace_append hprefix tailTrace_4468556
  have hstable : (prefixWord ++ tailWord_4468556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468556).length < 2 ^ (prefixWord ++ tailWord_4468556).sum := by decide
  have hdescent : baseEnd_4468556 < baseStart_4468556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468583 : List Nat := [1, 1, 5, 1, 2, 1, 1, 6, 1, 4]
def baseStart_4468583 : Nat := 118140960795 + 4468583 * 2 ^ 59
def prefixEnd_4468583 : Nat := 4983230072969 + 3 ^ 40 * 4468583 * 2
def baseEnd_4468583 : Nat := 764843641170065127387289

theorem tailTrace_4468583 : CollatzResearch.WordTrace tailWord_4468583 prefixEnd_4468583 764843641170065127387289 := by
  unfold tailWord_4468583
  simp only [CollatzResearch.WordTrace]
  refine ⟨162982611570094439062186403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108655074380062959374790935 162982611570094439062186403)
  ·
    refine ⟨244473917355141658593279605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162982611570094439062186403 244473917355141658593279605)
    ·
      refine ⟨22919429752044530493119963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 244473917355141658593279605 22919429752044530493119963)
      ·
        refine ⟨34379144628066795739679945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22919429752044530493119963 34379144628066795739679945)
        ·
          refine ⟨25784358471050096804759959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34379144628066795739679945 25784358471050096804759959)
          ·
            refine ⟨38676537706575145207139939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25784358471050096804759959 38676537706575145207139939)
            ·
              refine ⟨58014806559862717810709909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38676537706575145207139939 58014806559862717810709909)
              ·
                refine ⟨2719444057493564897377027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58014806559862717810709909 2719444057493564897377027)
                ·
                  refine ⟨4079166086240347346065541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2719444057493564897377027 4079166086240347346065541)
                  ·
                    refine ⟨764843641170065127387289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4079166086240347346065541 764843641170065127387289)
                    ·
                      rfl

theorem cell23_4468583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_4468583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468583 prefixEnd_4468583 := by exact prefixLift 4468583
  have htrace : WordTrace (prefixWord ++ tailWord_4468583) baseStart_4468583 baseEnd_4468583 := by
    simpa [prefixWord, tailWord_4468583, baseEnd_4468583] using wordTrace_append hprefix tailTrace_4468583
  have hstable : (prefixWord ++ tailWord_4468583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468583).length < 2 ^ (prefixWord ++ tailWord_4468583).sum := by decide
  have hdescent : baseEnd_4468583 < baseStart_4468583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468649 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 3, 1, 5]
def baseStart_4468649 : Nat := 118140960795 + 4468649 * 2 ^ 59
def prefixEnd_4468649 : Nat := 4983230072969 + 3 ^ 40 * 4468649 * 2
def baseEnd_4468649 : Nat := 2294564813233392123936563

theorem tailTrace_4468649 : CollatzResearch.WordTrace tailWord_4468649 prefixEnd_4468649 2294564813233392123936563 := by
  unfold tailWord_4468649
  simp only [CollatzResearch.WordTrace]
  refine ⟨162985018787855332334089001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108656679191903554889392667 162985018787855332334089001)
  ·
    refine ⟨122238764090891499250566751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162985018787855332334089001 122238764090891499250566751)
    ·
      refine ⟨183358146136337248875850127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122238764090891499250566751 183358146136337248875850127)
      ·
        refine ⟨275037219204505873313775191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183358146136337248875850127 275037219204505873313775191)
        ·
          refine ⟨412555828806758809970662787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275037219204505873313775191 412555828806758809970662787)
          ·
            refine ⟨618833743210138214955994181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412555828806758809970662787 618833743210138214955994181)
            ·
              refine ⟨116031326851900915304248909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 618833743210138214955994181 116031326851900915304248909)
              ·
                refine ⟨43511747569462843239093341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116031326851900915304248909 43511747569462843239093341)
                ·
                  refine ⟨16316905338548566214660003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43511747569462843239093341 16316905338548566214660003)
                  ·
                    refine ⟨24475358007822849321990005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16316905338548566214660003 24475358007822849321990005)
                    ·
                      refine ⟨2294564813233392123936563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24475358007822849321990005 2294564813233392123936563)
                      ·
                        rfl

theorem cell23_4468649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_4468649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468649 prefixEnd_4468649 := by exact prefixLift 4468649
  have htrace : WordTrace (prefixWord ++ tailWord_4468649) baseStart_4468649 baseEnd_4468649 := by
    simpa [prefixWord, tailWord_4468649, baseEnd_4468649] using wordTrace_append hprefix tailTrace_4468649
  have hstable : (prefixWord ++ tailWord_4468649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468649).length < 2 ^ (prefixWord ++ tailWord_4468649).sum := by decide
  have hdescent : baseEnd_4468649 < baseStart_4468649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468659 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 6]
def baseStart_4468659 : Nat := 118140960795 + 4468659 * 2 ^ 59
def prefixEnd_4468659 : Nat := 4983230072969 + 3 ^ 40 * 4468659 * 2
def baseEnd_4468659 : Nat := 2294569948039937084811517

theorem tailTrace_4468659 : CollatzResearch.WordTrace tailWord_4468659 prefixEnd_4468659 2294569948039937084811517 := by
  unfold tailWord_4468659
  simp only [CollatzResearch.WordTrace]
  refine ⟨162985383517819104041953031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108656922345212736027968687 162985383517819104041953031)
  ·
    refine ⟨244478075276728656062929547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162985383517819104041953031 244478075276728656062929547)
    ·
      refine ⟨366717112915092984094394321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244478075276728656062929547 366717112915092984094394321)
      ·
        refine ⟨275037834686319738070795741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366717112915092984094394321 275037834686319738070795741)
        ·
          refine ⟨103139188007369901776548403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275037834686319738070795741 103139188007369901776548403)
          ·
            refine ⟨154708782011054852664822605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103139188007369901776548403 154708782011054852664822605)
            ·
              refine ⟨58015793254145569749308477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154708782011054852664822605 58015793254145569749308477)
              ·
                refine ⟨21755922470304588655990679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58015793254145569749308477 21755922470304588655990679)
                ·
                  refine ⟨32633883705456882983986019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21755922470304588655990679 32633883705456882983986019)
                  ·
                    refine ⟨48950825558185324475979029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32633883705456882983986019 48950825558185324475979029)
                    ·
                      refine ⟨2294569948039937084811517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48950825558185324475979029 2294569948039937084811517)
                      ·
                        rfl

theorem cell23_4468659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_4468659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468659 prefixEnd_4468659 := by exact prefixLift 4468659
  have htrace : WordTrace (prefixWord ++ tailWord_4468659) baseStart_4468659 baseEnd_4468659 := by
    simpa [prefixWord, tailWord_4468659, baseEnd_4468659] using wordTrace_append hprefix tailTrace_4468659
  have hstable : (prefixWord ++ tailWord_4468659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468659).length < 2 ^ (prefixWord ++ tailWord_4468659).sum := by decide
  have hdescent : baseEnd_4468659 < baseStart_4468659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468660 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_4468660 : Nat := 118140960795 + 4468660 * 2 ^ 59
def prefixEnd_4468660 : Nat := 4983230072969 + 3 ^ 40 * 4468660 * 2
def baseEnd_4468660 : Nat := 764856820506863860299671

theorem tailTrace_4468660 : CollatzResearch.WordTrace tailWord_4468660 prefixEnd_4468660 764856820506863860299671 := by
  unfold tailWord_4468660
  simp only [CollatzResearch.WordTrace]
  refine ⟨81492709995407740606369717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108656946660543654141826289 81492709995407740606369717)
  ·
    refine ⟨7639941562069475681847161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81492709995407740606369717 7639941562069475681847161)
    ·
      refine ⟨5729956171552106761385371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7639941562069475681847161 5729956171552106761385371)
      ·
        refine ⟨8594934257328160142078057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5729956171552106761385371 8594934257328160142078057)
        ·
          refine ⟨6446200692996120106558543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8594934257328160142078057 6446200692996120106558543)
          ·
            refine ⟨9669301039494180159837815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6446200692996120106558543 9669301039494180159837815)
            ·
              refine ⟨14503951559241270239756723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9669301039494180159837815 14503951559241270239756723)
              ·
                refine ⟨21755927338861905359635085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14503951559241270239756723 21755927338861905359635085)
                ·
                  refine ⟨8158472752073214509863157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21755927338861905359635085 8158472752073214509863157)
                  ·
                    refine ⟨764856820506863860299671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8158472752073214509863157 764856820506863860299671)
                    ·
                      rfl

theorem cell23_4468660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_4468660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468660 prefixEnd_4468660 := by exact prefixLift 4468660
  have htrace : WordTrace (prefixWord ++ tailWord_4468660) baseStart_4468660 baseEnd_4468660 := by
    simpa [prefixWord, tailWord_4468660, baseEnd_4468660] using wordTrace_append hprefix tailTrace_4468660
  have hstable : (prefixWord ++ tailWord_4468660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468660).length < 2 ^ (prefixWord ++ tailWord_4468660).sum := by decide
  have hdescent : baseEnd_4468660 < baseStart_4468660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468663 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 5, 2, 2]
def baseStart_4468663 : Nat := 118140960795 + 4468663 * 2 ^ 59
def prefixEnd_4468663 : Nat := 4983230072969 + 3 ^ 40 * 4468663 * 2
def baseEnd_4468663 : Nat := 2294572001962555069161499

theorem tailTrace_4468663 : CollatzResearch.WordTrace tailWord_4468663 prefixEnd_4468663 2294572001962555069161499 := by
  unfold tailWord_4468663
  simp only [CollatzResearch.WordTrace]
  refine ⟨162985529409804612725098643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108657019606536408483399095 162985529409804612725098643)
  ·
    refine ⟨244478294114706919087647965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162985529409804612725098643 244478294114706919087647965)
    ·
      refine ⟨91679360293015094657867987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244478294114706919087647965 91679360293015094657867987)
      ·
        refine ⟨137519040439522641986801981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91679360293015094657867987 137519040439522641986801981)
        ·
          refine ⟨51569640164820990745050743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137519040439522641986801981 51569640164820990745050743)
          ·
            refine ⟨77354460247231486117576115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51569640164820990745050743 77354460247231486117576115)
            ·
              refine ⟨116031690370847229176364173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77354460247231486117576115 116031690370847229176364173)
              ·
                refine ⟨43511883889067710941136565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116031690370847229176364173 43511883889067710941136565)
                ·
                  refine ⟨4079239114600097900731553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43511883889067710941136565 4079239114600097900731553)
                  ·
                    refine ⟨3059429335950073425548665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4079239114600097900731553 3059429335950073425548665)
                    ·
                      refine ⟨2294572001962555069161499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3059429335950073425548665 2294572001962555069161499)
                      ·
                        rfl

theorem cell23_4468663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 2, 2].length) (baseStart_4468663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468663 prefixEnd_4468663 := by exact prefixLift 4468663
  have htrace : WordTrace (prefixWord ++ tailWord_4468663) baseStart_4468663 baseEnd_4468663 := by
    simpa [prefixWord, tailWord_4468663, baseEnd_4468663] using wordTrace_append hprefix tailTrace_4468663
  have hstable : (prefixWord ++ tailWord_4468663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468663).length < 2 ^ (prefixWord ++ tailWord_4468663).sum := by decide
  have hdescent : baseEnd_4468663 < baseStart_4468663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468680 : List Nat := [2, 1, 3, 1, 4, 2, 3, 1, 1, 1, 4]
def baseStart_4468680 : Nat := 118140960795 + 4468680 * 2 ^ 59
def prefixEnd_4468680 : Nat := 4983230072969 + 3 ^ 40 * 4468680 * 2
def baseEnd_4468680 : Nat := 2294580731133681502648921

theorem tailTrace_4468680 : CollatzResearch.WordTrace tailWord_4468680 prefixEnd_4468680 2294580731133681502648921 := by
  unfold tailWord_4468680
  simp only [CollatzResearch.WordTrace]
  refine ⟨81493074725371512314233747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108657432967162016418978329 81493074725371512314233747)
  ·
    refine ⟨122239612088057268471350621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81493074725371512314233747 122239612088057268471350621)
    ·
      refine ⟨45839854533021475676756483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122239612088057268471350621 45839854533021475676756483)
      ·
        refine ⟨68759781799532213515134725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45839854533021475676756483 68759781799532213515134725)
        ·
          refine ⟨12892459087412290034087761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68759781799532213515134725 12892459087412290034087761)
          ·
            refine ⟨9669344315559217525565821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12892459087412290034087761 9669344315559217525565821)
            ·
              refine ⟨3626004118334706572087183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9669344315559217525565821 3626004118334706572087183)
              ·
                refine ⟨5439006177502059858130775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3626004118334706572087183 5439006177502059858130775)
                ·
                  refine ⟨8158509266253089787196163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5439006177502059858130775 8158509266253089787196163)
                  ·
                    refine ⟨12237763899379634680794245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8158509266253089787196163 12237763899379634680794245)
                    ·
                      refine ⟨2294580731133681502648921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12237763899379634680794245 2294580731133681502648921)
                      ·
                        rfl

theorem cell23_4468680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_4468680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468680 prefixEnd_4468680 := by exact prefixLift 4468680
  have htrace : WordTrace (prefixWord ++ tailWord_4468680) baseStart_4468680 baseEnd_4468680 := by
    simpa [prefixWord, tailWord_4468680, baseEnd_4468680] using wordTrace_append hprefix tailTrace_4468680
  have hstable : (prefixWord ++ tailWord_4468680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468680).length < 2 ^ (prefixWord ++ tailWord_4468680).sum := by decide
  have hdescent : baseEnd_4468680 < baseStart_4468680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468689 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 6]
def baseStart_4468689 : Nat := 118140960795 + 4468689 * 2 ^ 59
def prefixEnd_4468689 : Nat := 4983230072969 + 3 ^ 40 * 4468689 * 2
def baseEnd_4468689 : Nat := 2294585352459571967436379

theorem tailTrace_4468689 : CollatzResearch.WordTrace tailWord_4468689 prefixEnd_4468689 2294585352459571967436379 := by
  unfold tailWord_4468689
  simp only [CollatzResearch.WordTrace]
  refine ⟨162986477707710419165545121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108657651805140279443696747 162986477707710419165545121)
  ·
    refine ⟨122239858280782814374158841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162986477707710419165545121 122239858280782814374158841)
    ·
      refine ⟨91679893710587110780619131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122239858280782814374158841 91679893710587110780619131)
      ·
        refine ⟨137519840565880666170928697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91679893710587110780619131 137519840565880666170928697)
        ·
          refine ⟨103139880424410499628196523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137519840565880666170928697 103139880424410499628196523)
          ·
            refine ⟨154709820636615749442294785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103139880424410499628196523 154709820636615749442294785)
            ·
              refine ⟨116032365477461812081721089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154709820636615749442294785 116032365477461812081721089)
              ·
                refine ⟨87024274108096359061290817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116032365477461812081721089 87024274108096359061290817)
                ·
                  refine ⟨65268205581072269295968113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87024274108096359061290817 65268205581072269295968113)
                  ·
                    refine ⟨48951154185804201971976085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65268205581072269295968113 48951154185804201971976085)
                    ·
                      refine ⟨2294585352459571967436379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48951154185804201971976085 2294585352459571967436379)
                      ·
                        rfl

theorem cell23_4468689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_4468689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468689 prefixEnd_4468689 := by exact prefixLift 4468689
  have htrace : WordTrace (prefixWord ++ tailWord_4468689) baseStart_4468689 baseEnd_4468689 := by
    simpa [prefixWord, tailWord_4468689, baseEnd_4468689] using wordTrace_append hprefix tailTrace_4468689
  have hstable : (prefixWord ++ tailWord_4468689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468689).length < 2 ^ (prefixWord ++ tailWord_4468689).sum := by decide
  have hdescent : baseEnd_4468689 < baseStart_4468689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468696 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 3, 3, 3]
def baseStart_4468696 : Nat := 118140960795 + 4468696 * 2 ^ 59
def prefixEnd_4468696 : Nat := 4983230072969 + 3 ^ 40 * 4468696 * 2
def baseEnd_4468696 : Nat := 2294588946824153440048847

theorem tailTrace_4468696 : CollatzResearch.WordTrace tailWord_4468696 prefixEnd_4468696 2294588946824153440048847 := by
  unfold tailWord_4468696
  simp only [CollatzResearch.WordTrace]
  refine ⟨81493366509342529680524971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108657822012456706240699961 81493366509342529680524971)
  ·
    refine ⟨122240049764013794520787457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81493366509342529680524971 122240049764013794520787457)
    ·
      refine ⟨91680037323010345890590593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122240049764013794520787457 91680037323010345890590593)
      ·
        refine ⟨68760027992257759417942945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91680037323010345890590593 68760027992257759417942945)
        ·
          refine ⟨51570020994193319563457209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68760027992257759417942945 51570020994193319563457209)
          ·
            refine ⟨38677515745644989672592907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51570020994193319563457209 38677515745644989672592907)
            ·
              refine ⟨58016273618467484508889361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38677515745644989672592907 58016273618467484508889361)
              ·
                refine ⟨43512205213850613381667021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58016273618467484508889361 43512205213850613381667021)
                ·
                  refine ⟨16317076955193980018125133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43512205213850613381667021 16317076955193980018125133)
                  ·
                    refine ⟨6118903858197742506796925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16317076955193980018125133 6118903858197742506796925)
                    ·
                      refine ⟨2294588946824153440048847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6118903858197742506796925 2294588946824153440048847)
                      ·
                        rfl

theorem cell23_4468696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_4468696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468696 prefixEnd_4468696 := by exact prefixLift 4468696
  have htrace : WordTrace (prefixWord ++ tailWord_4468696) baseStart_4468696 baseEnd_4468696 := by
    simpa [prefixWord, tailWord_4468696, baseEnd_4468696] using wordTrace_append hprefix tailTrace_4468696
  have hstable : (prefixWord ++ tailWord_4468696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468696).length < 2 ^ (prefixWord ++ tailWord_4468696).sum := by decide
  have hdescent : baseEnd_4468696 < baseStart_4468696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468734 : List Nat := [4, 2, 2, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_4468734 : Nat := 118140960795 + 4468734 * 2 ^ 59
def prefixEnd_4468734 : Nat := 4983230072969 + 3 ^ 40 * 4468734 * 2
def baseEnd_4468734 : Nat := 2294608459089024291373673

theorem tailTrace_4468734 : CollatzResearch.WordTrace tailWord_4468734 prefixEnd_4468734 2294608459089024291373673 := by
  unfold tailWord_4468734
  simp only [CollatzResearch.WordTrace]
  refine ⟨20373514874068423981366657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108658745995031594567288837 20373514874068423981366657)
  ·
    refine ⟨15280136155551317986024993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20373514874068423981366657 15280136155551317986024993)
    ·
      refine ⟨11460102116663488489518745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15280136155551317986024993 11460102116663488489518745)
      ·
        refine ⟨8595076587497616367139059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11460102116663488489518745 8595076587497616367139059)
        ·
          refine ⟨12892614881246424550708589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8595076587497616367139059 12892614881246424550708589)
          ·
            refine ⟨4834730580467409206515721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12892614881246424550708589 4834730580467409206515721)
            ·
              refine ⟨3626047935350556904886791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4834730580467409206515721 3626047935350556904886791)
              ·
                refine ⟨5439071903025835357330187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3626047935350556904886791 5439071903025835357330187)
                ·
                  refine ⟨8158607854538753035995281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5439071903025835357330187 8158607854538753035995281)
                  ·
                    refine ⟨6118955890904064776996461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8158607854538753035995281 6118955890904064776996461)
                    ·
                      refine ⟨2294608459089024291373673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6118955890904064776996461 2294608459089024291373673)
                      ·
                        rfl

theorem cell23_4468734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_4468734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468734 prefixEnd_4468734 := by exact prefixLift 4468734
  have htrace : WordTrace (prefixWord ++ tailWord_4468734) baseStart_4468734 baseEnd_4468734 := by
    simpa [prefixWord, tailWord_4468734, baseEnd_4468734] using wordTrace_append hprefix tailTrace_4468734
  have hstable : (prefixWord ++ tailWord_4468734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468734).length < 2 ^ (prefixWord ++ tailWord_4468734).sum := by decide
  have hdescent : baseEnd_4468734 < baseStart_4468734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468836 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 2, 8]
def baseStart_4468836 : Nat := 118140960795 + 4468836 * 2 ^ 59
def prefixEnd_4468836 : Nat := 4983230072969 + 3 ^ 40 * 4468836 * 2
def baseEnd_4468836 : Nat := 764886944705260964099401

theorem tailTrace_4468836 : CollatzResearch.WordTrace tailWord_4468836 prefixEnd_4468836 764886944705260964099401 := by
  unfold tailWord_4468836
  simp only [CollatzResearch.WordTrace]
  refine ⟨81495919619088931635573181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108661226158785242180764241 81495919619088931635573181)
  ·
    refine ⟨30560969857158349363339943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81495919619088931635573181 30560969857158349363339943)
    ·
      refine ⟨45841454785737524045009915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30560969857158349363339943 45841454785737524045009915)
      ·
        refine ⟨68762182178606286067514873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45841454785737524045009915 68762182178606286067514873)
        ·
          refine ⟨51571636633954714550636155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68762182178606286067514873 51571636633954714550636155)
          ·
            refine ⟨77357454950932071825954233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51571636633954714550636155 77357454950932071825954233)
            ·
              refine ⟨58018091213199053869465675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77357454950932071825954233 58018091213199053869465675)
              ·
                refine ⟨87027136819798580804198513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58018091213199053869465675 87027136819798580804198513)
                ·
                  refine ⟨65270352614848935603148885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87027136819798580804198513 65270352614848935603148885)
                  ·
                    refine ⟨764886944705260964099401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65270352614848935603148885 764886944705260964099401)
                    ·
                      rfl

theorem cell23_4468836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_4468836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468836 prefixEnd_4468836 := by exact prefixLift 4468836
  have htrace : WordTrace (prefixWord ++ tailWord_4468836) baseStart_4468836 baseEnd_4468836 := by
    simpa [prefixWord, tailWord_4468836, baseEnd_4468836] using wordTrace_append hprefix tailTrace_4468836
  have hstable : (prefixWord ++ tailWord_4468836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468836).length < 2 ^ (prefixWord ++ tailWord_4468836).sum := by decide
  have hdescent : baseEnd_4468836 < baseStart_4468836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468856 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 2, 1, 6]
def baseStart_4468856 : Nat := 118140960795 + 4468856 * 2 ^ 59
def prefixEnd_4468856 : Nat := 4983230072969 + 3 ^ 40 * 4468856 * 2
def baseEnd_4468856 : Nat := 2294671103728872814048111

theorem tailTrace_4468856 : CollatzResearch.WordTrace tailWord_4468856 prefixEnd_4468856 2294671103728872814048111 := by
  unfold tailWord_4468856
  simp only [CollatzResearch.WordTrace]
  refine ⟨81496284349052703343437211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108661712465403604457916281 81496284349052703343437211)
  ·
    refine ⟨122244426523579055015155817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81496284349052703343437211 122244426523579055015155817)
    ·
      refine ⟨91683319892684291261366863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122244426523579055015155817 91683319892684291261366863)
      ·
        refine ⟨137524979839026436892050295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91683319892684291261366863 137524979839026436892050295)
        ·
          refine ⟨206287469758539655338075443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137524979839026436892050295 206287469758539655338075443)
          ·
            refine ⟨309431204637809483007113165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206287469758539655338075443 309431204637809483007113165)
            ·
              refine ⟨116036701739178556127667437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 309431204637809483007113165 116036701739178556127667437)
              ·
                refine ⟨43513763152191958547875289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116036701739178556127667437 43513763152191958547875289)
                ·
                  refine ⟨32635322364143968910906467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43513763152191958547875289 32635322364143968910906467)
                  ·
                    refine ⟨48952983546215953366359701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32635322364143968910906467 48952983546215953366359701)
                    ·
                      refine ⟨2294671103728872814048111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48952983546215953366359701 2294671103728872814048111)
                      ·
                        rfl

theorem cell23_4468856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_4468856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468856 prefixEnd_4468856 := by exact prefixLift 4468856
  have htrace : WordTrace (prefixWord ++ tailWord_4468856) baseStart_4468856 baseEnd_4468856 := by
    simpa [prefixWord, tailWord_4468856, baseEnd_4468856] using wordTrace_append hprefix tailTrace_4468856
  have hstable : (prefixWord ++ tailWord_4468856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468856).length < 2 ^ (prefixWord ++ tailWord_4468856).sum := by decide
  have hdescent : baseEnd_4468856 < baseStart_4468856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468894 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_4468894 : Nat := 118140960795 + 4468894 * 2 ^ 59
def prefixEnd_4468894 : Nat := 4983230072969 + 3 ^ 40 * 4468894 * 2
def baseEnd_4468894 : Nat := 2294690615993743665372937

theorem tailTrace_4468894 : CollatzResearch.WordTrace tailWord_4468894 prefixEnd_4468894 2294690615993743665372937 := by
  unfold tailWord_4468894
  simp only [CollatzResearch.WordTrace]
  refine ⟨20374244333995967397094717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108662636447978492784505157 20374244333995967397094717)
  ·
    refine ⟨7640341625248487773910519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20374244333995967397094717 7640341625248487773910519)
    ·
      refine ⟨11460512437872731660865779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7640341625248487773910519 11460512437872731660865779)
      ·
        refine ⟨17190768656809097491298669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11460512437872731660865779 17190768656809097491298669)
        ·
          refine ⟨6446538246303411559237001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17190768656809097491298669 6446538246303411559237001)
          ·
            refine ⟨4834903684727558669427751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6446538246303411559237001 4834903684727558669427751)
            ·
              refine ⟨7252355527091338004141627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4834903684727558669427751 7252355527091338004141627)
              ·
                refine ⟨10878533290637007006212441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7252355527091338004141627 10878533290637007006212441)
                ·
                  refine ⟨8158899967977755254659331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10878533290637007006212441 8158899967977755254659331)
                  ·
                    refine ⟨12238349951966632881988997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8158899967977755254659331 12238349951966632881988997)
                    ·
                      refine ⟨2294690615993743665372937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12238349951966632881988997 2294690615993743665372937)
                      ·
                        rfl

theorem cell23_4468894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_4468894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468894 prefixEnd_4468894 := by exact prefixLift 4468894
  have htrace : WordTrace (prefixWord ++ tailWord_4468894) baseStart_4468894 baseEnd_4468894 := by
    simpa [prefixWord, tailWord_4468894, baseEnd_4468894] using wordTrace_append hprefix tailTrace_4468894
  have hstable : (prefixWord ++ tailWord_4468894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468894).length < 2 ^ (prefixWord ++ tailWord_4468894).sum := by decide
  have hdescent : baseEnd_4468894 < baseStart_4468894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468897 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 2, 2, 3]
def baseStart_4468897 : Nat := 118140960795 + 4468897 * 2 ^ 59
def prefixEnd_4468897 : Nat := 4983230072969 + 3 ^ 40 * 4468897 * 2
def baseEnd_4468897 : Nat := 2294692156435707153635423

theorem tailTrace_4468897 : CollatzResearch.WordTrace tailWord_4468897 prefixEnd_4468897 2294692156435707153635423 := by
  unfold tailWord_4468897
  simp only [CollatzResearch.WordTrace]
  refine ⟨162994064090956870689116945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108662709393971247126077963 162994064090956870689116945)
  ·
    refine ⟨122245548068217653016837709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162994064090956870689116945 122245548068217653016837709)
    ·
      refine ⟨45842080525581619881314141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122245548068217653016837709 45842080525581619881314141)
      ·
        refine ⟨17190780197093107455492803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45842080525581619881314141 17190780197093107455492803)
        ·
          refine ⟨25786170295639661183239205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17190780197093107455492803 25786170295639661183239205)
          ·
            refine ⟨4834906930432436471857351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25786170295639661183239205 4834906930432436471857351)
            ·
              refine ⟨7252360395648654707786027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4834906930432436471857351 7252360395648654707786027)
              ·
                refine ⟨10878540593472982061679041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7252360395648654707786027 10878540593472982061679041)
                ·
                  refine ⟨8158905445104736546259281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10878540593472982061679041 8158905445104736546259281)
                  ·
                    refine ⟨6119179083828552409694461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8158905445104736546259281 6119179083828552409694461)
                    ·
                      refine ⟨2294692156435707153635423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6119179083828552409694461 2294692156435707153635423)
                      ·
                        rfl

theorem cell23_4468897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_4468897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468897 prefixEnd_4468897 := by exact prefixLift 4468897
  have htrace : WordTrace (prefixWord ++ tailWord_4468897) baseStart_4468897 baseEnd_4468897 := by
    simpa [prefixWord, tailWord_4468897, baseEnd_4468897] using wordTrace_append hprefix tailTrace_4468897
  have hstable : (prefixWord ++ tailWord_4468897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468897).length < 2 ^ (prefixWord ++ tailWord_4468897).sum := by decide
  have hdescent : baseEnd_4468897 < baseStart_4468897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468920 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 4, 3, 2]
def baseStart_4468920 : Nat := 118140960795 + 4468920 * 2 ^ 59
def prefixEnd_4468920 : Nat := 4983230072969 + 3 ^ 40 * 4468920 * 2
def baseEnd_4468920 : Nat := 2294703966490760563647817

theorem tailTrace_4468920 : CollatzResearch.WordTrace tailWord_4468920 prefixEnd_4468920 2294703966490760563647817 := by
  unfold tailWord_4468920
  simp only [CollatzResearch.WordTrace]
  refine ⟨81497451484936772808602107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108663268646582363744802809 81497451484936772808602107)
  ·
    refine ⟨122246177227405159212903161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81497451484936772808602107 122246177227405159212903161)
    ·
      refine ⟨91684632920553869409677371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122246177227405159212903161 91684632920553869409677371)
      ·
        refine ⟨137526949380830804114516057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91684632920553869409677371 137526949380830804114516057)
        ·
          refine ⟨103145212035623103085887043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137526949380830804114516057 103145212035623103085887043)
          ·
            refine ⟨154717818053434654628830565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103145212035623103085887043 154717818053434654628830565)
            ·
              refine ⟨29009590885018997742905731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154717818053434654628830565 29009590885018997742905731)
              ·
                refine ⟨43514386327528496614358597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29009590885018997742905731 43514386327528496614358597)
                ·
                  refine ⟨8158947436411593115192237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43514386327528496614358597 8158947436411593115192237)
                  ·
                    refine ⟨3059605288654347418197089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8158947436411593115192237 3059605288654347418197089)
                    ·
                      refine ⟨2294703966490760563647817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3059605288654347418197089 2294703966490760563647817)
                      ·
                        rfl

theorem cell23_4468920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 4, 3, 2].length) (baseStart_4468920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468920 prefixEnd_4468920 := by exact prefixLift 4468920
  have htrace : WordTrace (prefixWord ++ tailWord_4468920) baseStart_4468920 baseEnd_4468920 := by
    simpa [prefixWord, tailWord_4468920, baseEnd_4468920] using wordTrace_append hprefix tailTrace_4468920
  have hstable : (prefixWord ++ tailWord_4468920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468920).length < 2 ^ (prefixWord ++ tailWord_4468920).sum := by decide
  have hdescent : baseEnd_4468920 < baseStart_4468920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468933 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 5, 1, 4]
def baseStart_4468933 : Nat := 118140960795 + 4468933 * 2 ^ 59
def prefixEnd_4468933 : Nat := 4983230072969 + 3 ^ 40 * 4468933 * 2
def baseEnd_4468933 : Nat := 2294710641739269012785257

theorem tailTrace_4468933 : CollatzResearch.WordTrace tailWord_4468933 prefixEnd_4468933 2294710641739269012785257 := by
  unfold tailWord_4468933
  simp only [CollatzResearch.WordTrace]
  refine ⟨162995377118826448837427453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108663584745884299224951635 162995377118826448837427453)
  ·
    refine ⟨61123266419559918314035295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162995377118826448837427453 61123266419559918314035295)
    ·
      refine ⟨91684899629339877471052943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61123266419559918314035295 91684899629339877471052943)
      ·
        refine ⟨137527349444009816206579415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91684899629339877471052943 137527349444009816206579415)
        ·
          refine ⟨206291024166014724309869123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137527349444009816206579415 206291024166014724309869123)
          ·
            refine ⟨309436536249022086464803685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206291024166014724309869123 309436536249022086464803685)
            ·
              refine ⟨58019350546691641212150691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 309436536249022086464803685 58019350546691641212150691)
              ·
                refine ⟨87029025820037461818226037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58019350546691641212150691 87029025820037461818226037)
                ·
                  refine ⟨8158971170628512045458691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87029025820037461818226037 8158971170628512045458691)
                  ·
                    refine ⟨12238456755942768068188037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8158971170628512045458691 12238456755942768068188037)
                    ·
                      refine ⟨2294710641739269012785257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12238456755942768068188037 2294710641739269012785257)
                      ·
                        rfl

theorem cell23_4468933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_4468933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468933 prefixEnd_4468933 := by exact prefixLift 4468933
  have htrace : WordTrace (prefixWord ++ tailWord_4468933) baseStart_4468933 baseEnd_4468933 := by
    simpa [prefixWord, tailWord_4468933, baseEnd_4468933] using wordTrace_append hprefix tailTrace_4468933
  have hstable : (prefixWord ++ tailWord_4468933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468933).length < 2 ^ (prefixWord ++ tailWord_4468933).sum := by decide
  have hdescent : baseEnd_4468933 < baseStart_4468933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468967 : List Nat := [1, 1, 5, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_4468967 : Nat := 118140960795 + 4468967 * 2 ^ 59
def prefixEnd_4468967 : Nat := 4983230072969 + 3 ^ 40 * 4468967 * 2
def baseEnd_4468967 : Nat := 2294728100081521879760101

theorem tailTrace_4468967 : CollatzResearch.WordTrace tailWord_4468967 prefixEnd_4468967 2294728100081521879760101 := by
  unfold tailWord_4468967
  simp only [CollatzResearch.WordTrace]
  refine ⟨162996617200703272644165155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108664411467135515096110103 162996617200703272644165155)
  ·
    refine ⟨244494925801054908966247733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162996617200703272644165155 244494925801054908966247733)
    ·
      refine ⟨22921399293848897715585725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 244494925801054908966247733 22921399293848897715585725)
      ·
        refine ⟨8595524735193336643344647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22921399293848897715585725 8595524735193336643344647)
        ·
          refine ⟨12893287102790004965016971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8595524735193336643344647 12893287102790004965016971)
          ·
            refine ⟨19339930654185007447525457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12893287102790004965016971 19339930654185007447525457)
            ·
              refine ⟨14504947990638755585644093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19339930654185007447525457 14504947990638755585644093)
              ·
                refine ⟨5439355496489533344616535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14504947990638755585644093 5439355496489533344616535)
                ·
                  refine ⟨8159033244734300016924803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5439355496489533344616535 8159033244734300016924803)
                  ·
                    refine ⟨12238549867101450025387205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8159033244734300016924803 12238549867101450025387205)
                    ·
                      refine ⟨2294728100081521879760101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12238549867101450025387205 2294728100081521879760101)
                      ·
                        rfl

theorem cell23_4468967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_4468967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468967 prefixEnd_4468967 := by exact prefixLift 4468967
  have htrace : WordTrace (prefixWord ++ tailWord_4468967) baseStart_4468967 baseEnd_4468967 := by
    simpa [prefixWord, tailWord_4468967, baseEnd_4468967] using wordTrace_append hprefix tailTrace_4468967
  have hstable : (prefixWord ++ tailWord_4468967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468967).length < 2 ^ (prefixWord ++ tailWord_4468967).sum := by decide
  have hdescent : baseEnd_4468967 < baseStart_4468967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468970 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_4468970 : Nat := 118140960795 + 4468970 * 2 ^ 59
def prefixEnd_4468970 : Nat := 4983230072969 + 3 ^ 40 * 4468970 * 2
def baseEnd_4468970 : Nat := 2294729640523485368022587

theorem tailTrace_4468970 : CollatzResearch.WordTrace tailWord_4468970 prefixEnd_4468970 2294729640523485368022587 := by
  unfold tailWord_4468970
  simp only [CollatzResearch.WordTrace]
  refine ⟨40749181654923101039131091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108664484413128269437682909 40749181654923101039131091)
  ·
    refine ⟨61123772482384651558696637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40749181654923101039131091 61123772482384651558696637)
    ·
      refine ⟨22921414680894244334511239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61123772482384651558696637 22921414680894244334511239)
      ·
        refine ⟨34382122021341366501766859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22921414680894244334511239 34382122021341366501766859)
        ·
          refine ⟨51573183032012049752650289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34382122021341366501766859 51573183032012049752650289)
          ·
            refine ⟨38679887274009037314487717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51573183032012049752650289 38679887274009037314487717)
            ·
              refine ⟨7252478863876694496466447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38679887274009037314487717 7252478863876694496466447)
              ·
                refine ⟨10878718295815041744699671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7252478863876694496466447 10878718295815041744699671)
                ·
                  refine ⟨16318077443722562617049507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10878718295815041744699671 16318077443722562617049507)
                  ·
                    refine ⟨24477116165583843925574261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16318077443722562617049507 24477116165583843925574261)
                    ·
                      refine ⟨2294729640523485368022587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24477116165583843925574261 2294729640523485368022587)
                      ·
                        rfl

theorem cell23_4468970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_4468970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468970 prefixEnd_4468970 := by exact prefixLift 4468970
  have htrace : WordTrace (prefixWord ++ tailWord_4468970) baseStart_4468970 baseEnd_4468970 := by
    simpa [prefixWord, tailWord_4468970, baseEnd_4468970] using wordTrace_append hprefix tailTrace_4468970
  have hstable : (prefixWord ++ tailWord_4468970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468970).length < 2 ^ (prefixWord ++ tailWord_4468970).sum := by decide
  have hdescent : baseEnd_4468970 < baseStart_4468970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468983 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 3]
def baseStart_4468983 : Nat := 118140960795 + 4468983 * 2 ^ 59
def prefixEnd_4468983 : Nat := 4983230072969 + 3 ^ 40 * 4468983 * 2
def baseEnd_4468983 : Nat := 2294736315771993817160027

theorem tailTrace_4468983 : CollatzResearch.WordTrace tailWord_4468983 prefixEnd_4468983 2294736315771993817160027 := by
  unfold tailWord_4468983
  simp only [CollatzResearch.WordTrace]
  refine ⟨162997200768645307376747603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108664800512430204917831735 162997200768645307376747603)
  ·
    refine ⟨244495801152967961065121405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162997200768645307376747603 244495801152967961065121405)
    ·
      refine ⟨91685925432362985399420527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244495801152967961065121405 91685925432362985399420527)
      ·
        refine ⟨137528888148544478099130791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91685925432362985399420527 137528888148544478099130791)
        ·
          refine ⟨206293332222816717148696187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137528888148544478099130791 206293332222816717148696187)
          ·
            refine ⟨309439998334225075723044281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206293332222816717148696187 309439998334225075723044281)
            ·
              refine ⟨232079998750668806792283211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309439998334225075723044281 232079998750668806792283211)
              ·
                refine ⟨348119998126003210188424817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232079998750668806792283211 348119998126003210188424817)
                ·
                  refine ⟨261089998594502407641318613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348119998126003210188424817 261089998594502407641318613)
                  ·
                    refine ⟨6119296842058650179093405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 261089998594502407641318613 6119296842058650179093405)
                    ·
                      refine ⟨2294736315771993817160027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6119296842058650179093405 2294736315771993817160027)
                      ·
                        rfl

theorem cell23_4468983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_4468983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468983 prefixEnd_4468983 := by exact prefixLift 4468983
  have htrace : WordTrace (prefixWord ++ tailWord_4468983) baseStart_4468983 baseEnd_4468983 := by
    simpa [prefixWord, tailWord_4468983, baseEnd_4468983] using wordTrace_append hprefix tailTrace_4468983
  have hstable : (prefixWord ++ tailWord_4468983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468983).length < 2 ^ (prefixWord ++ tailWord_4468983).sum := by decide
  have hdescent : baseEnd_4468983 < baseStart_4468983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468984 : List Nat := [2, 1, 2, 1, 1, 2, 1, 8, 1, 2, 2]
def baseStart_4468984 : Nat := 118140960795 + 4468984 * 2 ^ 59
def prefixEnd_4468984 : Nat := 4983230072969 + 3 ^ 40 * 4468984 * 2
def baseEnd_4468984 : Nat := 2294736829252648313247523

theorem tailTrace_4468984 : CollatzResearch.WordTrace tailWord_4468984 prefixEnd_4468984 2294736829252648313247523 := by
  unfold tailWord_4468984
  simp only [CollatzResearch.WordTrace]
  refine ⟨81498618620820842273767003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108664824827761123031689337 81498618620820842273767003)
  ·
    refine ⟨122247927931231263410650505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81498618620820842273767003 122247927931231263410650505)
    ·
      refine ⟨91685945948423447557987879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122247927931231263410650505 91685945948423447557987879)
      ·
        refine ⟨137528918922635171336981819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91685945948423447557987879 137528918922635171336981819)
        ·
          refine ⟨206293378383952757005472729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137528918922635171336981819 206293378383952757005472729)
          ·
            refine ⟨154720033787964567754104547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206293378383952757005472729 154720033787964567754104547)
            ·
              refine ⟨232080050681946851631156821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154720033787964567754104547 232080050681946851631156821)
              ·
                refine ⟨2719688093929064667552619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 232080050681946851631156821 2719688093929064667552619)
                ·
                  refine ⟨4079532140893597001328929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2719688093929064667552619 4079532140893597001328929)
                  ·
                    refine ⟨3059649105670197750996697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4079532140893597001328929 3059649105670197750996697)
                    ·
                      refine ⟨2294736829252648313247523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3059649105670197750996697 2294736829252648313247523)
                      ·
                        rfl

theorem cell23_4468984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 1, 2, 2].length) (baseStart_4468984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468984 prefixEnd_4468984 := by exact prefixLift 4468984
  have htrace : WordTrace (prefixWord ++ tailWord_4468984) baseStart_4468984 baseEnd_4468984 := by
    simpa [prefixWord, tailWord_4468984, baseEnd_4468984] using wordTrace_append hprefix tailTrace_4468984
  have hstable : (prefixWord ++ tailWord_4468984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468984).length < 2 ^ (prefixWord ++ tailWord_4468984).sum := by decide
  have hdescent : baseEnd_4468984 < baseStart_4468984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468990 : List Nat := [4, 2, 2, 1, 1, 1, 4, 8]
def baseStart_4468990 : Nat := 118140960795 + 4468990 * 2 ^ 59
def prefixEnd_4468990 : Nat := 4983230072969 + 3 ^ 40 * 4468990 * 2
def baseEnd_4468990 : Nat := 84990367042095381102685

theorem tailTrace_4468990 : CollatzResearch.WordTrace tailWord_4468990 prefixEnd_4468990 84990367042095381102685 := by
  unfold tailWord_4468990
  simp only [CollatzResearch.WordTrace]
  refine ⟨20374682009952493446531553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108664970719746631714834949 20374682009952493446531553)
  ·
    refine ⟨15281011507464370084898665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20374682009952493446531553 15281011507464370084898665)
    ·
      refine ⟨11460758630598277563673999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15281011507464370084898665 11460758630598277563673999)
      ·
        refine ⟨17191137945897416345510999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11460758630598277563673999 17191137945897416345510999)
        ·
          refine ⟨25786706918846124518266499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17191137945897416345510999 25786706918846124518266499)
          ·
            refine ⟨38680060378269186777399749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25786706918846124518266499 38680060378269186777399749)
            ·
              refine ⟨7252511320925472520762453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38680060378269186777399749 7252511320925472520762453)
              ·
                refine ⟨84990367042095381102685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7252511320925472520762453 84990367042095381102685)
                ·
                  rfl

theorem cell23_4468990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 8].length) (baseStart_4468990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468990 prefixEnd_4468990 := by exact prefixLift 4468990
  have htrace : WordTrace (prefixWord ++ tailWord_4468990) baseStart_4468990 baseEnd_4468990 := by
    simpa [prefixWord, tailWord_4468990, baseEnd_4468990] using wordTrace_append hprefix tailTrace_4468990
  have hstable : (prefixWord ++ tailWord_4468990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468990).length < 2 ^ (prefixWord ++ tailWord_4468990).sum := by decide
  have hdescent : baseEnd_4468990 < baseStart_4468990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468993 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_4468993 : Nat := 118140960795 + 4468993 * 2 ^ 59
def prefixEnd_4468993 : Nat := 4983230072969 + 3 ^ 40 * 4468993 * 2
def baseEnd_4468993 : Nat := 2294741450578538778034981

theorem tailTrace_4468993 : CollatzResearch.WordTrace tailWord_4468993 prefixEnd_4468993 2294741450578538778034981 := by
  unfold tailWord_4468993
  simp only [CollatzResearch.WordTrace]
  refine ⟨162997565498609079084611633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108665043665739386056407755 162997565498609079084611633)
  ·
    refine ⟨122248174123956809313458725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162997565498609079084611633 122248174123956809313458725)
    ·
      refine ⟨22921532648241901746273511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122248174123956809313458725 22921532648241901746273511)
      ·
        refine ⟨34382298972362852619410267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22921532648241901746273511 34382298972362852619410267)
        ·
          refine ⟨51573448458544278929115401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34382298972362852619410267 51573448458544278929115401)
          ·
            refine ⟨38680086343908209196836551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51573448458544278929115401 38680086343908209196836551)
            ·
              refine ⟨58020129515862313795254827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38680086343908209196836551 58020129515862313795254827)
              ·
                refine ⟨87030194273793470692882241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58020129515862313795254827 87030194273793470692882241)
                ·
                  refine ⟨65272645705345103019661681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87030194273793470692882241 65272645705345103019661681)
                  ·
                    refine ⟨48954484279008827264746261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65272645705345103019661681 48954484279008827264746261)
                    ·
                      refine ⟨2294741450578538778034981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48954484279008827264746261 2294741450578538778034981)
                      ·
                        rfl

theorem cell23_4468993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_4468993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468993 prefixEnd_4468993 := by exact prefixLift 4468993
  have htrace : WordTrace (prefixWord ++ tailWord_4468993) baseStart_4468993 baseEnd_4468993 := by
    simpa [prefixWord, tailWord_4468993, baseEnd_4468993] using wordTrace_append hprefix tailTrace_4468993
  have hstable : (prefixWord ++ tailWord_4468993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468993).length < 2 ^ (prefixWord ++ tailWord_4468993).sum := by decide
  have hdescent : baseEnd_4468993 < baseStart_4468993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4468994 : List Nat := [3, 4, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_4468994 : Nat := 118140960795 + 4468994 * 2 ^ 59
def prefixEnd_4468994 : Nat := 4983230072969 + 3 ^ 40 * 4468994 * 2
def baseEnd_4468994 : Nat := 764913988019731091374159

theorem tailTrace_4468994 : CollatzResearch.WordTrace tailWord_4468994 prefixEnd_4468994 764913988019731091374159 := by
  unfold tailWord_4468994
  simp only [CollatzResearch.WordTrace]
  refine ⟨40749400492901364063849509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108665067981070304170265357 40749400492901364063849509)
  ·
    refine ⟨7640512592419005761971783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40749400492901364063849509 7640512592419005761971783)
    ·
      refine ⟨11460768888628508642957675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7640512592419005761971783 11460768888628508642957675)
      ·
        refine ⟨17191153332942762964436513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11460768888628508642957675 17191153332942762964436513)
        ·
          refine ⟨12893364999707072223327385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17191153332942762964436513 12893364999707072223327385)
          ·
            refine ⟨9670023749780304167495539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12893364999707072223327385 9670023749780304167495539)
            ·
              refine ⟨14505035624670456251243309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9670023749780304167495539 14505035624670456251243309)
              ·
                refine ⟨5439388359251421094216241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14505035624670456251243309 5439388359251421094216241)
                ·
                  refine ⟨4079541269438565820662181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5439388359251421094216241 4079541269438565820662181)
                  ·
                    refine ⟨764913988019731091374159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4079541269438565820662181 764913988019731091374159)
                    ·
                      rfl

theorem cell23_4468994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_4468994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4468994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4468994 prefixEnd_4468994 := by exact prefixLift 4468994
  have htrace : WordTrace (prefixWord ++ tailWord_4468994) baseStart_4468994 baseEnd_4468994 := by
    simpa [prefixWord, tailWord_4468994, baseEnd_4468994] using wordTrace_append hprefix tailTrace_4468994
  have hstable : (prefixWord ++ tailWord_4468994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4468994).length < 2 ^ (prefixWord ++ tailWord_4468994).sum := by decide
  have hdescent : baseEnd_4468994 < baseStart_4468994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4468994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469013 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_4469013 : Nat := 118140960795 + 4469013 * 2 ^ 59
def prefixEnd_4469013 : Nat := 4983230072969 + 3 ^ 40 * 4469013 * 2
def baseEnd_4469013 : Nat := 2294751720191628699784889

theorem tailTrace_4469013 : CollatzResearch.WordTrace tailWord_4469013 prefixEnd_4469013 2294751720191628699784889 := by
  unfold tailWord_4469013
  simp only [CollatzResearch.WordTrace]
  refine ⟨162998294958536622500339693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108665529972357748333559795 162998294958536622500339693)
  ·
    refine ⟨61124360609451233437627385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 162998294958536622500339693 61124360609451233437627385)
    ·
      refine ⟨45843270457088425078220539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61124360609451233437627385 45843270457088425078220539)
      ·
        refine ⟨68764905685632637617330809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45843270457088425078220539 68764905685632637617330809)
        ·
          refine ⟨51573679264224478212998107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68764905685632637617330809 51573679264224478212998107)
          ·
            refine ⟨77360518896336717319497161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51573679264224478212998107 77360518896336717319497161)
            ·
              refine ⟨58020389172252537989622871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77360518896336717319497161 58020389172252537989622871)
              ·
                refine ⟨87030583758378806984434307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58020389172252537989622871 87030583758378806984434307)
                ·
                  refine ⟨130545875637568210476651461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87030583758378806984434307 130545875637568210476651461)
                  ·
                    refine ⟨24477351682044039464372149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 130545875637568210476651461 24477351682044039464372149)
                    ·
                      refine ⟨2294751720191628699784889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24477351682044039464372149 2294751720191628699784889)
                      ·
                        rfl

theorem cell23_4469013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_4469013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469013 prefixEnd_4469013 := by exact prefixLift 4469013
  have htrace : WordTrace (prefixWord ++ tailWord_4469013) baseStart_4469013 baseEnd_4469013 := by
    simpa [prefixWord, tailWord_4469013, baseEnd_4469013] using wordTrace_append hprefix tailTrace_4469013
  have hstable : (prefixWord ++ tailWord_4469013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469013).length < 2 ^ (prefixWord ++ tailWord_4469013).sum := by decide
  have hdescent : baseEnd_4469013 < baseStart_4469013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469021 : List Nat := [1, 4, 2, 3, 2, 1, 3, 1, 1, 2, 3]
def baseStart_4469021 : Nat := 118140960795 + 4469021 * 2 ^ 59
def prefixEnd_4469021 : Nat := 4983230072969 + 3 ^ 40 * 4469021 * 2
def baseEnd_4469021 : Nat := 2294755828036864668484853

theorem tailTrace_4469021 : CollatzResearch.WordTrace tailWord_4469021 prefixEnd_4469021 2294755828036864668484853 := by
  unfold tailWord_4469021
  simp only [CollatzResearch.WordTrace]
  refine ⟨162998586742507639866630917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108665724495005093244420611 162998586742507639866630917)
  ·
    refine ⟨30562235014220182474993297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 162998586742507639866630917 30562235014220182474993297)
    ·
      refine ⟨22921676260665136856244973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30562235014220182474993297 22921676260665136856244973)
      ·
        refine ⟨8595628597749426321091865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22921676260665136856244973 8595628597749426321091865)
        ·
          refine ⟨6446721448312069740818899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8595628597749426321091865 6446721448312069740818899)
          ·
            refine ⟨9670082172468104611228349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6446721448312069740818899 9670082172468104611228349)
            ·
              refine ⟨3626280814675539229210631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9670082172468104611228349 3626280814675539229210631)
              ·
                refine ⟨5439421222013308843815947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3626280814675539229210631 5439421222013308843815947)
                ·
                  refine ⟨8159131833019963265723921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5439421222013308843815947 8159131833019963265723921)
                  ·
                    refine ⟨6119348874764972449292941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8159131833019963265723921 6119348874764972449292941)
                    ·
                      refine ⟨2294755828036864668484853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6119348874764972449292941 2294755828036864668484853)
                      ·
                        rfl

theorem cell23_4469021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_4469021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469021 prefixEnd_4469021 := by exact prefixLift 4469021
  have htrace : WordTrace (prefixWord ++ tailWord_4469021) baseStart_4469021 baseEnd_4469021 := by
    simpa [prefixWord, tailWord_4469021, baseEnd_4469021] using wordTrace_append hprefix tailTrace_4469021
  have hstable : (prefixWord ++ tailWord_4469021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469021).length < 2 ^ (prefixWord ++ tailWord_4469021).sum := by decide
  have hdescent : baseEnd_4469021 < baseStart_4469021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469044 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_4469044 : Nat := 118140960795 + 4469044 * 2 ^ 59
def prefixEnd_4469044 : Nat := 4983230072969 + 3 ^ 40 * 4469044 * 2
def baseEnd_4469044 : Nat := 2294767638091918078497247

theorem tailTrace_4469044 : CollatzResearch.WordTrace tailWord_4469044 prefixEnd_4469044 2294767638091918078497247 := by
  unfold tailWord_4469044
  simp only [CollatzResearch.WordTrace]
  refine ⟨81499712810712157397359093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108666283747616209863145457 81499712810712157397359093)
  ·
    refine ⟨7640598076004264756002415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81499712810712157397359093 7640598076004264756002415)
    ·
      refine ⟨11460897114006397134003623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7640598076004264756002415 11460897114006397134003623)
      ·
        refine ⟨17191345671009595701005435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11460897114006397134003623 17191345671009595701005435)
        ·
          refine ⟨25787018506514393551508153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17191345671009595701005435 25787018506514393551508153)
          ·
            refine ⟨19340263879885795163631115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25787018506514393551508153 19340263879885795163631115)
            ·
              refine ⟨29010395819828692745446673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19340263879885795163631115 29010395819828692745446673)
              ·
                refine ⟨21757796864871519559085005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29010395819828692745446673 21757796864871519559085005)
                ·
                  refine ⟨8159173824326819834656877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21757796864871519559085005 8159173824326819834656877)
                  ·
                    refine ⟨3059690184122557437996329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8159173824326819834656877 3059690184122557437996329)
                    ·
                      refine ⟨2294767638091918078497247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3059690184122557437996329 2294767638091918078497247)
                      ·
                        rfl

theorem cell23_4469044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_4469044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469044 prefixEnd_4469044 := by exact prefixLift 4469044
  have htrace : WordTrace (prefixWord ++ tailWord_4469044) baseStart_4469044 baseEnd_4469044 := by
    simpa [prefixWord, tailWord_4469044, baseEnd_4469044] using wordTrace_append hprefix tailTrace_4469044
  have hstable : (prefixWord ++ tailWord_4469044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469044).length < 2 ^ (prefixWord ++ tailWord_4469044).sum := by decide
  have hdescent : baseEnd_4469044 < baseStart_4469044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469050 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 2, 6]
def baseStart_4469050 : Nat := 118140960795 + 4469050 * 2 ^ 59
def prefixEnd_4469050 : Nat := 4983230072969 + 3 ^ 40 * 4469050 * 2
def baseEnd_4469050 : Nat := 764923572991948351674073

theorem tailTrace_4469050 : CollatzResearch.WordTrace tailWord_4469050 prefixEnd_4469050 764923572991948351674073 := by
  unfold tailWord_4469050
  simp only [CollatzResearch.WordTrace]
  refine ⟨40749911114850644454859151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108666429639601718546291069 40749911114850644454859151)
  ·
    refine ⟨61124866672275966682288727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40749911114850644454859151 61124866672275966682288727)
    ·
      refine ⟨91687300008413950023433091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61124866672275966682288727 91687300008413950023433091)
      ·
        refine ⟨137530950012620925035149637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91687300008413950023433091 137530950012620925035149637)
        ·
          refine ⟨25787053127366423444090557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137530950012620925035149637 25787053127366423444090557)
          ·
            refine ⟨9670144922762408791533959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25787053127366423444090557 9670144922762408791533959)
            ·
              refine ⟨14505217384143613187300939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9670144922762408791533959 14505217384143613187300939)
              ·
                refine ⟨21757826076215419780951409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14505217384143613187300939 21757826076215419780951409)
                ·
                  refine ⟨16318369557161564835713557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21757826076215419780951409 16318369557161564835713557)
                  ·
                    refine ⟨764923572991948351674073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16318369557161564835713557 764923572991948351674073)
                    ·
                      rfl

theorem cell23_4469050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_4469050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469050 prefixEnd_4469050 := by exact prefixLift 4469050
  have htrace : WordTrace (prefixWord ++ tailWord_4469050) baseStart_4469050 baseEnd_4469050 := by
    simpa [prefixWord, tailWord_4469050, baseEnd_4469050] using wordTrace_append hprefix tailTrace_4469050
  have hstable : (prefixWord ++ tailWord_4469050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469050).length < 2 ^ (prefixWord ++ tailWord_4469050).sum := by decide
  have hdescent : baseEnd_4469050 < baseStart_4469050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469200 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 7, 5]
def baseStart_4469200 : Nat := 118140960795 + 4469200 * 2 ^ 59
def prefixEnd_4469200 : Nat := 4983230072969 + 3 ^ 40 * 4469200 * 2
def baseEnd_4469200 : Nat := 764949247024673156048843

theorem tailTrace_4469200 : CollatzResearch.WordTrace tailWord_4469200 prefixEnd_4469200 764949247024673156048843 := by
  unfold tailWord_4469200
  simp only [CollatzResearch.WordTrace]
  refine ⟨81502557704429576718698527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108670076939239435624931369 81502557704429576718698527)
  ·
    refine ⟨122253836556644365078047791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81502557704429576718698527 122253836556644365078047791)
    ·
      refine ⟨183380754834966547617071687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122253836556644365078047791 183380754834966547617071687)
      ·
        refine ⟨275071132252449821425607531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183380754834966547617071687 275071132252449821425607531)
        ·
          refine ⟨412606698378674732138411297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275071132252449821425607531 412606698378674732138411297)
          ·
            refine ⟨309455023784006049103808473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 412606698378674732138411297 309455023784006049103808473)
            ·
              refine ⟨232091267838004536827856355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309455023784006049103808473 232091267838004536827856355)
              ·
                refine ⟨348136901757006805241784533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232091267838004536827856355 348136901757006805241784533)
                ·
                  refine ⟨8159458634929846997854325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 348136901757006805241784533 8159458634929846997854325)
                  ·
                    refine ⟨764949247024673156048843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8159458634929846997854325 764949247024673156048843)
                    ·
                      rfl

theorem cell23_4469200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 7, 5].length) (baseStart_4469200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469200 prefixEnd_4469200 := by exact prefixLift 4469200
  have htrace : WordTrace (prefixWord ++ tailWord_4469200) baseStart_4469200 baseEnd_4469200 := by
    simpa [prefixWord, tailWord_4469200, baseEnd_4469200] using wordTrace_append hprefix tailTrace_4469200
  have hstable : (prefixWord ++ tailWord_4469200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469200).length < 2 ^ (prefixWord ++ tailWord_4469200).sum := by decide
  have hdescent : baseEnd_4469200 < baseStart_4469200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469204 : List Nat := [2, 4, 1, 2, 2, 2, 2, 2, 6]
def baseStart_4469204 : Nat := 118140960795 + 4469204 * 2 ^ 59
def prefixEnd_4469204 : Nat := 4983230072969 + 3 ^ 40 * 4469204 * 2
def baseEnd_4469204 : Nat := 254983310555181939166279

theorem tailTrace_4469204 : CollatzResearch.WordTrace tailWord_4469204 prefixEnd_4469204 254983310555181939166279 := by
  unfold tailWord_4469204
  simp only [CollatzResearch.WordTrace]
  refine ⟨81502630650422331060271333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108670174200563108080361777 81502630650422331060271333)
  ·
    refine ⟨15281743246954187073800875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81502630650422331060271333 15281743246954187073800875)
    ·
      refine ⟨22922614870431280610701313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15281743246954187073800875 22922614870431280610701313)
      ·
        refine ⟨17191961152823460458025985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22922614870431280610701313 17191961152823460458025985)
        ·
          refine ⟨12893970864617595343519489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17191961152823460458025985 12893970864617595343519489)
          ·
            refine ⟨9670478148463196507639617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12893970864617595343519489 9670478148463196507639617)
            ·
              refine ⟨7252858611347397380729713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9670478148463196507639617 7252858611347397380729713)
              ·
                refine ⟨5439643958510548035547285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7252858611347397380729713 5439643958510548035547285)
                ·
                  refine ⟨254983310555181939166279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5439643958510548035547285 254983310555181939166279)
                  ·
                    rfl

theorem cell23_4469204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_4469204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469204 prefixEnd_4469204 := by exact prefixLift 4469204
  have htrace : WordTrace (prefixWord ++ tailWord_4469204) baseStart_4469204 baseEnd_4469204 := by
    simpa [prefixWord, tailWord_4469204, baseEnd_4469204] using wordTrace_append hprefix tailTrace_4469204
  have hstable : (prefixWord ++ tailWord_4469204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469204).length < 2 ^ (prefixWord ++ tailWord_4469204).sum := by decide
  have hdescent : baseEnd_4469204 < baseStart_4469204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469207 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 5, 5, 2]
def baseStart_4469207 : Nat := 118140960795 + 4469207 * 2 ^ 59
def prefixEnd_4469207 : Nat := 4983230072969 + 3 ^ 40 * 4469207 * 2
def baseEnd_4469207 : Nat := 2294851335438600940758997

theorem tailTrace_4469207 : CollatzResearch.WordTrace tailWord_4469207 prefixEnd_4469207 2294851335438600940758997 := by
  unfold tailWord_4469207
  simp only [CollatzResearch.WordTrace]
  refine ⟨163005370719833793632901875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108670247146555862421934583 163005370719833793632901875)
  ·
    refine ⟨244508056079750690449352813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163005370719833793632901875 244508056079750690449352813)
    ·
      refine ⟨91690521029906508918507305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244508056079750690449352813 91690521029906508918507305)
      ·
        refine ⟨68767890772429881688880479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91690521029906508918507305 68767890772429881688880479)
        ·
          refine ⟨103151836158644822533320719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68767890772429881688880479 103151836158644822533320719)
          ·
            refine ⟨154727754237967233799981079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103151836158644822533320719 154727754237967233799981079)
            ·
              refine ⟨232091631356950850699971619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154727754237967233799981079 232091631356950850699971619)
              ·
                refine ⟨348137447035426276049957429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232091631356950850699971619 348137447035426276049957429)
                ·
                  refine ⟨32637885659571213379683509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 348137447035426276049957429 32637885659571213379683509)
                  ·
                    refine ⟨3059801780584801254345329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32637885659571213379683509 3059801780584801254345329)
                    ·
                      refine ⟨2294851335438600940758997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3059801780584801254345329 2294851335438600940758997)
                      ·
                        rfl

theorem cell23_4469207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_4469207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469207 prefixEnd_4469207 := by exact prefixLift 4469207
  have htrace : WordTrace (prefixWord ++ tailWord_4469207) baseStart_4469207 baseEnd_4469207 := by
    simpa [prefixWord, tailWord_4469207, baseEnd_4469207] using wordTrace_append hprefix tailTrace_4469207
  have hstable : (prefixWord ++ tailWord_4469207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469207).length < 2 ^ (prefixWord ++ tailWord_4469207).sum := by decide
  have hdescent : baseEnd_4469207 < baseStart_4469207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469247 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 4, 4]
def baseStart_4469247 : Nat := 118140960795 + 4469247 * 2 ^ 59
def prefixEnd_4469247 : Nat := 4983230072969 + 3 ^ 40 * 4469247 * 2
def baseEnd_4469247 : Nat := 764957291554926928086271

theorem tailTrace_4469247 : CollatzResearch.WordTrace tailWord_4469247 prefixEnd_4469247 764957291554926928086271 := by
  unfold tailWord_4469247
  simp only [CollatzResearch.WordTrace]
  refine ⟨163006829639688880464357995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108671219759792586976238663 163006829639688880464357995)
  ·
    refine ⟨244510244459533320696536993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163006829639688880464357995 244510244459533320696536993)
    ·
      refine ⟨183382683344649990522402745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244510244459533320696536993 183382683344649990522402745)
      ·
        refine ⟨137537012508487492891802059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183382683344649990522402745 137537012508487492891802059)
        ·
          refine ⟨206305518762731239337703089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137537012508487492891802059 206305518762731239337703089)
          ·
            refine ⟨154729139072048429503277317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206305518762731239337703089 154729139072048429503277317)
            ·
              refine ⟨29011713576009080531864497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154729139072048429503277317 29011713576009080531864497)
              ·
                refine ⟨21758785182006810398898373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29011713576009080531864497 21758785182006810398898373)
                ·
                  refine ⟨4079772221626276949793445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21758785182006810398898373 4079772221626276949793445)
                  ·
                    refine ⟨764957291554926928086271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4079772221626276949793445 764957291554926928086271)
                    ·
                      rfl

theorem cell23_4469247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 4].length) (baseStart_4469247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469247 prefixEnd_4469247 := by exact prefixLift 4469247
  have htrace : WordTrace (prefixWord ++ tailWord_4469247) baseStart_4469247 baseEnd_4469247 := by
    simpa [prefixWord, tailWord_4469247, baseEnd_4469247] using wordTrace_append hprefix tailTrace_4469247
  have hstable : (prefixWord ++ tailWord_4469247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469247).length < 2 ^ (prefixWord ++ tailWord_4469247).sum := by decide
  have hdescent : baseEnd_4469247 < baseStart_4469247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469257 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 5, 2, 3]
def baseStart_4469257 : Nat := 118140960795 + 4469257 * 2 ^ 59
def prefixEnd_4469257 : Nat := 4983230072969 + 3 ^ 40 * 4469257 * 2
def baseEnd_4469257 : Nat := 2294877009471325745133767

theorem tailTrace_4469257 : CollatzResearch.WordTrace tailWord_4469257 prefixEnd_4469257 2294877009471325745133767 := by
  unfold tailWord_4469257
  simp only [CollatzResearch.WordTrace]
  refine ⟨163007194369652652172222025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108671462913101768114814683 163007194369652652172222025)
  ·
    refine ⟨122255395777239489129166519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163007194369652652172222025 122255395777239489129166519)
    ·
      refine ⟨183383093665859233693749779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122255395777239489129166519 183383093665859233693749779)
      ·
        refine ⟨275074640498788850540624669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183383093665859233693749779 275074640498788850540624669)
        ·
          refine ⟨103152990187045818952734251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275074640498788850540624669 103152990187045818952734251)
          ·
            refine ⟨154729485280568728429101377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103152990187045818952734251 154729485280568728429101377)
            ·
              refine ⟨116047113960426546321826033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154729485280568728429101377 116047113960426546321826033)
              ·
                refine ⟨87035335470319909741369525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116047113960426546321826033 87035335470319909741369525)
                ·
                  refine ⟨8159562700342491538253393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87035335470319909741369525 8159562700342491538253393)
                  ·
                    refine ⟨6119672025256868653690045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8159562700342491538253393 6119672025256868653690045)
                    ·
                      refine ⟨2294877009471325745133767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6119672025256868653690045 2294877009471325745133767)
                      ·
                        rfl

theorem cell23_4469257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 2, 3].length) (baseStart_4469257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469257 prefixEnd_4469257 := by exact prefixLift 4469257
  have htrace : WordTrace (prefixWord ++ tailWord_4469257) baseStart_4469257 baseEnd_4469257 := by
    simpa [prefixWord, tailWord_4469257, baseEnd_4469257] using wordTrace_append hprefix tailTrace_4469257
  have hstable : (prefixWord ++ tailWord_4469257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469257).length < 2 ^ (prefixWord ++ tailWord_4469257).sum := by decide
  have hdescent : baseEnd_4469257 < baseStart_4469257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469281 : List Nat := [1, 2, 3, 2, 2, 1, 5, 1, 2, 4]
def baseStart_4469281 : Nat := 118140960795 + 4469281 * 2 ^ 59
def prefixEnd_4469281 : Nat := 4983230072969 + 3 ^ 40 * 4469281 * 2
def baseEnd_4469281 : Nat := 764963111002344550411219

theorem tailTrace_4469281 : CollatzResearch.WordTrace tailWord_4469281 prefixEnd_4469281 764963111002344550411219 := by
  unfold tailWord_4469281
  simp only [CollatzResearch.WordTrace]
  refine ⟨163008069721565704271095697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108672046481043802847397131 163008069721565704271095697)
  ·
    refine ⟨122256052291174278203321773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163008069721565704271095697 122256052291174278203321773)
    ·
      refine ⟨45846019609190354326245665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122256052291174278203321773 45846019609190354326245665)
      ·
        refine ⟨34384514706892765744684249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45846019609190354326245665 34384514706892765744684249)
        ·
          refine ⟨25788386030169574308513187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34384514706892765744684249 25788386030169574308513187)
          ·
            refine ⟨38682579045254361462769781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25788386030169574308513187 38682579045254361462769781)
            ·
              refine ⟨3626491785492596387134667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38682579045254361462769781 3626491785492596387134667)
              ·
                refine ⟨5439737678238894580702001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3626491785492596387134667 5439737678238894580702001)
                ·
                  refine ⟨4079803258679170935526501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5439737678238894580702001 4079803258679170935526501)
                  ·
                    refine ⟨764963111002344550411219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4079803258679170935526501 764963111002344550411219)
                    ·
                      rfl

theorem cell23_4469281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_4469281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469281 prefixEnd_4469281 := by exact prefixLift 4469281
  have htrace : WordTrace (prefixWord ++ tailWord_4469281) baseStart_4469281 baseEnd_4469281 := by
    simpa [prefixWord, tailWord_4469281, baseEnd_4469281] using wordTrace_append hprefix tailTrace_4469281
  have hstable : (prefixWord ++ tailWord_4469281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469281).length < 2 ^ (prefixWord ++ tailWord_4469281).sum := by decide
  have hdescent : baseEnd_4469281 < baseStart_4469281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469288 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_4469288 : Nat := 118140960795 + 4469288 * 2 ^ 59
def prefixEnd_4469288 : Nat := 4983230072969 + 3 ^ 40 * 4469288 * 2
def baseEnd_4469288 : Nat := 2294892927371615123846125

theorem tailTrace_4469288 : CollatzResearch.WordTrace tailWord_4469288 prefixEnd_4469288 2294892927371615123846125 := by
  unfold tailWord_4469288
  simp only [CollatzResearch.WordTrace]
  refine ⟨81504162516270172233300259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108672216688360229644400345 81504162516270172233300259)
  ·
    refine ⟨122256243774405258349950389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81504162516270172233300259 122256243774405258349950389)
    ·
      refine ⟨11461522853850492970307849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122256243774405258349950389 11461522853850492970307849)
      ·
        refine ⟨8596142140387869727730887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11461522853850492970307849 8596142140387869727730887)
        ·
          refine ⟨12894213210581804591596331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8596142140387869727730887 12894213210581804591596331)
          ·
            refine ⟨19341319815872706887394497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12894213210581804591596331 19341319815872706887394497)
            ·
              refine ⟨14505989861904530165545873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19341319815872706887394497 14505989861904530165545873)
              ·
                refine ⟨10879492396428397624159405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14505989861904530165545873 10879492396428397624159405)
                ·
                  refine ⟨4079809648660649109059777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10879492396428397624159405 4079809648660649109059777)
                  ·
                    refine ⟨3059857236495486831794833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4079809648660649109059777 3059857236495486831794833)
                    ·
                      refine ⟨2294892927371615123846125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3059857236495486831794833 2294892927371615123846125)
                      ·
                        rfl

theorem cell23_4469288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_4469288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469288 prefixEnd_4469288 := by exact prefixLift 4469288
  have htrace : WordTrace (prefixWord ++ tailWord_4469288) baseStart_4469288 baseEnd_4469288 := by
    simpa [prefixWord, tailWord_4469288, baseEnd_4469288] using wordTrace_append hprefix tailTrace_4469288
  have hstable : (prefixWord ++ tailWord_4469288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469288).length < 2 ^ (prefixWord ++ tailWord_4469288).sum := by decide
  have hdescent : baseEnd_4469288 < baseStart_4469288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469294 : List Nat := [4, 1, 3, 1, 3, 1, 1, 9]
def baseStart_4469294 : Nat := 118140960795 + 4469294 * 2 ^ 59
def prefixEnd_4469294 : Nat := 4983230072969 + 3 ^ 40 * 4469294 * 2
def baseEnd_4469294 : Nat := 84996148453908966680411

theorem tailTrace_4469294 : CollatzResearch.WordTrace tailWord_4469294 prefixEnd_4469294 84996148453908966680411 := by
  unfold tailWord_4469294
  simp only [CollatzResearch.WordTrace]
  refine ⟨20376067983814825936414867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108672362580345738327545957 20376067983814825936414867)
  ·
    refine ⟨30564101975722238904622301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20376067983814825936414867 30564101975722238904622301)
    ·
      refine ⟨11461538240895839589233363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30564101975722238904622301 11461538240895839589233363)
      ·
        refine ⟨17192307361343759383850045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11461538240895839589233363 17192307361343759383850045)
        ·
          refine ⟨6447115260503909768943767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17192307361343759383850045 6447115260503909768943767)
          ·
            refine ⟨9670672890755864653415651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6447115260503909768943767 9670672890755864653415651)
            ·
              refine ⟨14506009336133796980123477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9670672890755864653415651 14506009336133796980123477)
              ·
                refine ⟨84996148453908966680411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14506009336133796980123477 84996148453908966680411)
                ·
                  rfl

theorem cell23_4469294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 9].length) (baseStart_4469294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469294 prefixEnd_4469294 := by exact prefixLift 4469294
  have htrace : WordTrace (prefixWord ++ tailWord_4469294) baseStart_4469294 baseEnd_4469294 := by
    simpa [prefixWord, tailWord_4469294, baseEnd_4469294] using wordTrace_append hprefix tailTrace_4469294
  have hstable : (prefixWord ++ tailWord_4469294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469294).length < 2 ^ (prefixWord ++ tailWord_4469294).sum := by decide
  have hdescent : baseEnd_4469294 < baseStart_4469294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469304 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 6, 1, 3]
def baseStart_4469304 : Nat := 118140960795 + 4469304 * 2 ^ 59
def prefixEnd_4469304 : Nat := 4983230072969 + 3 ^ 40 * 4469304 * 2
def baseEnd_4469304 : Nat := 2294901143062087061246051

theorem tailTrace_4469304 : CollatzResearch.WordTrace tailWord_4469304 prefixEnd_4469304 2294901143062087061246051 := by
  unfold tailWord_4469304
  simp only [CollatzResearch.WordTrace]
  refine ⟨81504454300241189599591483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108672605733654919466121977 81504454300241189599591483)
  ·
    refine ⟨122256681450361784399387225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81504454300241189599591483 122256681450361784399387225)
    ·
      refine ⟨91692511087771338299540419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122256681450361784399387225 91692511087771338299540419)
      ·
        refine ⟨137538766631657007449310629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91692511087771338299540419 137538766631657007449310629)
        ·
          refine ⟨25788518743435688896745743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137538766631657007449310629 25788518743435688896745743)
          ·
            refine ⟨38682778115153533345118615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25788518743435688896745743 38682778115153533345118615)
            ·
              refine ⟨58024167172730300017677923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38682778115153533345118615 58024167172730300017677923)
              ·
                refine ⟨87036250759095450026516885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58024167172730300017677923 87036250759095450026516885)
                ·
                  refine ⟨4079824254332599219992979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87036250759095450026516885 4079824254332599219992979)
                  ·
                    refine ⟨6119736381498898829989469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4079824254332599219992979 6119736381498898829989469)
                    ·
                      refine ⟨2294901143062087061246051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6119736381498898829989469 2294901143062087061246051)
                      ·
                        rfl

theorem cell23_4469304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 6, 1, 3].length) (baseStart_4469304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469304 prefixEnd_4469304 := by exact prefixLift 4469304
  have htrace : WordTrace (prefixWord ++ tailWord_4469304) baseStart_4469304 baseEnd_4469304 := by
    simpa [prefixWord, tailWord_4469304, baseEnd_4469304] using wordTrace_append hprefix tailTrace_4469304
  have hstable : (prefixWord ++ tailWord_4469304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469304).length < 2 ^ (prefixWord ++ tailWord_4469304).sum := by decide
  have hdescent : baseEnd_4469304 < baseStart_4469304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469347 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 5]
def baseStart_4469347 : Nat := 118140960795 + 4469347 * 2 ^ 59
def prefixEnd_4469347 : Nat := 4983230072969 + 3 ^ 40 * 4469347 * 2
def baseEnd_4469347 : Nat := 2294923222730230393008353

theorem tailTrace_4469347 : CollatzResearch.WordTrace tailWord_4469347 prefixEnd_4469347 2294923222730230393008353 := by
  unfold tailWord_4469347
  simp only [CollatzResearch.WordTrace]
  refine ⟨163010476939326597542998295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108673651292884398361998863 163010476939326597542998295)
  ·
    refine ⟨244515715408989896314497443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163010476939326597542998295 244515715408989896314497443)
    ·
      refine ⟨366773573113484844471746165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244515715408989896314497443 366773573113484844471746165)
      ·
        refine ⟨34385022479389204169226203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 366773573113484844471746165 34385022479389204169226203)
        ·
          refine ⟨51577533719083806253839305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34385022479389204169226203 51577533719083806253839305)
          ·
            refine ⟨38683150289312854690379479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51577533719083806253839305 38683150289312854690379479)
            ·
              refine ⟨58024725433969282035569219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38683150289312854690379479 58024725433969282035569219)
              ·
                refine ⟨87037088150953923053353829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58024725433969282035569219 87037088150953923053353829)
                ·
                  refine ⟨16319454028303860572503843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87037088150953923053353829 16319454028303860572503843)
                  ·
                    refine ⟨24479181042455790858755765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16319454028303860572503843 24479181042455790858755765)
                    ·
                      refine ⟨2294923222730230393008353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24479181042455790858755765 2294923222730230393008353)
                      ·
                        rfl

theorem cell23_4469347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_4469347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469347 prefixEnd_4469347 := by exact prefixLift 4469347
  have htrace : WordTrace (prefixWord ++ tailWord_4469347) baseStart_4469347 baseEnd_4469347 := by
    simpa [prefixWord, tailWord_4469347, baseEnd_4469347] using wordTrace_append hprefix tailTrace_4469347
  have hstable : (prefixWord ++ tailWord_4469347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469347).length < 2 ^ (prefixWord ++ tailWord_4469347).sum := by decide
  have hdescent : baseEnd_4469347 < baseStart_4469347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469434 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4]
def baseStart_4469434 : Nat := 118140960795 + 4469434 * 2 ^ 59
def prefixEnd_4469434 : Nat := 4983230072969 + 3 ^ 40 * 4469434 * 2
def baseEnd_4469434 : Nat := 2294967895547171552620453

theorem tailTrace_4469434 : CollatzResearch.WordTrace tailWord_4469434 prefixEnd_4469434 2294967895547171552620453 := by
  unfold tailWord_4469434
  simp only [CollatzResearch.WordTrace]
  refine ⟨40753412522502852850353839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108675766726674274267610237 40753412522502852850353839)
  ·
    refine ⟨61130118783754279275530759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40753412522502852850353839 61130118783754279275530759)
    ·
      refine ⟨91695178175631418913296139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61130118783754279275530759 91695178175631418913296139)
      ·
        refine ⟨137542767263447128369944209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91695178175631418913296139 137542767263447128369944209)
        ·
          refine ⟨103157075447585346277458157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137542767263447128369944209 103157075447585346277458157)
          ·
            refine ⟨38683903292844504854046809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103157075447585346277458157 38683903292844504854046809)
            ·
              refine ⟨29012927469633378640535107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38683903292844504854046809 29012927469633378640535107)
              ·
                refine ⟨43519391204450067960802661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29012927469633378640535107 43519391204450067960802661)
                ·
                  refine ⟨8159885850834387742650499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43519391204450067960802661 8159885850834387742650499)
                  ·
                    refine ⟨12239828776251581613975749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8159885850834387742650499 12239828776251581613975749)
                    ·
                      refine ⟨2294967895547171552620453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12239828776251581613975749 2294967895547171552620453)
                      ·
                        rfl

theorem cell23_4469434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_4469434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469434 prefixEnd_4469434 := by exact prefixLift 4469434
  have htrace : WordTrace (prefixWord ++ tailWord_4469434) baseStart_4469434 baseEnd_4469434 := by
    simpa [prefixWord, tailWord_4469434, baseEnd_4469434] using wordTrace_append hprefix tailTrace_4469434
  have hstable : (prefixWord ++ tailWord_4469434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469434).length < 2 ^ (prefixWord ++ tailWord_4469434).sum := by decide
  have hdescent : baseEnd_4469434 < baseStart_4469434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469446 : List Nat := [6, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_4469446 : Nat := 118140960795 + 4469446 * 2 ^ 59
def prefixEnd_4469446 : Nat := 4983230072969 + 3 ^ 40 * 4469446 * 2
def baseEnd_4469446 : Nat := 2294974057315025505670399

theorem tailTrace_4469446 : CollatzResearch.WordTrace tailWord_4469446 prefixEnd_4469446 2294974057315025505670399 := by
  unfold tailWord_4469446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5094190242686498045339131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 108676058510645291633901461 5094190242686498045339131)
  ·
    refine ⟨7641285364029747068008697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5094190242686498045339131 7641285364029747068008697)
    ·
      refine ⟨5730964023022310301006523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7641285364029747068008697 5730964023022310301006523)
      ·
        refine ⟨8596446034533465451509785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5730964023022310301006523 8596446034533465451509785)
        ·
          refine ⟨6447334525900099088632339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8596446034533465451509785 6447334525900099088632339)
          ·
            refine ⟨9671001788850148632948509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6447334525900099088632339 9671001788850148632948509)
            ·
              refine ⟨3626625670818805737355691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9671001788850148632948509 3626625670818805737355691)
              ·
                refine ⟨5439938506228208606033537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3626625670818805737355691 5439938506228208606033537)
                ·
                  refine ⟨4079953879671156454525153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5439938506228208606033537 4079953879671156454525153)
                  ·
                    refine ⟨3059965409753367340893865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4079953879671156454525153 3059965409753367340893865)
                    ·
                      refine ⟨2294974057315025505670399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3059965409753367340893865 2294974057315025505670399)
                      ·
                        rfl

theorem cell23_4469446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_4469446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469446 prefixEnd_4469446 := by exact prefixLift 4469446
  have htrace : WordTrace (prefixWord ++ tailWord_4469446) baseStart_4469446 baseEnd_4469446 := by
    simpa [prefixWord, tailWord_4469446, baseEnd_4469446] using wordTrace_append hprefix tailTrace_4469446
  have hstable : (prefixWord ++ tailWord_4469446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469446).length < 2 ^ (prefixWord ++ tailWord_4469446).sum := by decide
  have hdescent : baseEnd_4469446 < baseStart_4469446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469521 : List Nat := [1, 2, 2, 1, 1, 3, 5, 2, 1, 5]
def baseStart_4469521 : Nat := 118140960795 + 4469521 * 2 ^ 59
def prefixEnd_4469521 : Nat := 4983230072969 + 3 ^ 40 * 4469521 * 2
def baseEnd_4469521 : Nat := 765004189454704237410851

theorem tailTrace_4469521 : CollatzResearch.WordTrace tailWord_4469521 prefixEnd_4469521 765004189454704237410851 := by
  unfold tailWord_4469521
  simp only [CollatzResearch.WordTrace]
  refine ⟨163016823240696225259832417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108677882160464150173221611 163016823240696225259832417)
  ·
    refine ⟨122262617430522168944874313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163016823240696225259832417 122262617430522168944874313)
    ·
      refine ⟨91696963072891626708655735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122262617430522168944874313 91696963072891626708655735)
      ·
        refine ⟨137545444609337440062983603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91696963072891626708655735 137545444609337440062983603)
        ·
          refine ⟨206318166914006160094475405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137545444609337440062983603 206318166914006160094475405)
          ·
            refine ⟨77369312592752310035428277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206318166914006160094475405 77369312592752310035428277)
            ·
              refine ⟨7253373055570529065821401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77369312592752310035428277 7253373055570529065821401)
              ·
                refine ⟨5440029791677896799366051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7253373055570529065821401 5440029791677896799366051)
                ·
                  refine ⟨8160044687516845199049077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5440029791677896799366051 8160044687516845199049077)
                  ·
                    refine ⟨765004189454704237410851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8160044687516845199049077 765004189454704237410851)
                    ·
                      rfl

theorem cell23_4469521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_4469521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469521 prefixEnd_4469521 := by exact prefixLift 4469521
  have htrace : WordTrace (prefixWord ++ tailWord_4469521) baseStart_4469521 baseEnd_4469521 := by
    simpa [prefixWord, tailWord_4469521, baseEnd_4469521] using wordTrace_append hprefix tailTrace_4469521
  have hstable : (prefixWord ++ tailWord_4469521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469521).length < 2 ^ (prefixWord ++ tailWord_4469521).sum := by decide
  have hdescent : baseEnd_4469521 < baseStart_4469521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469546 : List Nat := [3, 1, 4, 3, 2, 1, 2, 2, 1, 4]
def baseStart_4469546 : Nat := 118140960795 + 4469546 * 2 ^ 59
def prefixEnd_4469546 : Nat := 4983230072969 + 3 ^ 40 * 4469546 * 2
def baseEnd_4469546 : Nat := 765008468460158371473313

theorem tailTrace_4469546 : CollatzResearch.WordTrace tailWord_4469546 prefixEnd_4469546 765008468460158371473313 := by
  unfold tailWord_4469546
  simp only [CollatzResearch.WordTrace]
  refine ⟨40754433766401413632373123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108678490043737103019661661 40754433766401413632373123)
  ·
    refine ⟨61131650649602120448559685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40754433766401413632373123 61131650649602120448559685)
    ·
      refine ⟨11462184496800397584104941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61131650649602120448559685 11462184496800397584104941)
      ·
        refine ⟨4298319186300149094039353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11462184496800397584104941 4298319186300149094039353)
        ·
          refine ⟨3223739389725111820529515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4298319186300149094039353 3223739389725111820529515)
          ·
            refine ⟨4835609084587667730794273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3223739389725111820529515 4835609084587667730794273)
            ·
              refine ⟨3626706813440750798095705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4835609084587667730794273 3626706813440750798095705)
              ·
                refine ⟨2720030110080563098571779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3626706813440750798095705 2720030110080563098571779)
                ·
                  refine ⟨4080045165120844647857669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2720030110080563098571779 4080045165120844647857669)
                  ·
                    refine ⟨765008468460158371473313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4080045165120844647857669 765008468460158371473313)
                    ·
                      rfl

theorem cell23_4469546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_4469546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469546 prefixEnd_4469546 := by exact prefixLift 4469546
  have htrace : WordTrace (prefixWord ++ tailWord_4469546) baseStart_4469546 baseEnd_4469546 := by
    simpa [prefixWord, tailWord_4469546, baseEnd_4469546] using wordTrace_append hprefix tailTrace_4469546
  have hstable : (prefixWord ++ tailWord_4469546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469546).length < 2 ^ (prefixWord ++ tailWord_4469546).sum := by decide
  have hdescent : baseEnd_4469546 < baseStart_4469546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469571 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 4]
def baseStart_4469571 : Nat := 118140960795 + 4469571 * 2 ^ 59
def prefixEnd_4469571 : Nat := 4983230072969 + 3 ^ 40 * 4469571 * 2
def baseEnd_4469571 : Nat := 2295038242396837516607323

theorem tailTrace_4469571 : CollatzResearch.WordTrace tailWord_4469571 prefixEnd_4469571 2295038242396837516607323 := by
  unfold tailWord_4469571
  simp only [CollatzResearch.WordTrace]
  refine ⟨163018646890515083799152567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108679097927010055866101711 163018646890515083799152567)
  ·
    refine ⟨244527970335772625698728851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163018646890515083799152567 244527970335772625698728851)
    ·
      refine ⟨366791955503658938548093277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244527970335772625698728851 366791955503658938548093277)
      ·
        refine ⟨137546983313872101955534979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 366791955503658938548093277 137546983313872101955534979)
        ·
          refine ⟨206320474970808152933302469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137546983313872101955534979 206320474970808152933302469)
          ·
            refine ⟨38685089057026528674994213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206320474970808152933302469 38685089057026528674994213)
            ·
              refine ⟨7253454198192474126561415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38685089057026528674994213 7253454198192474126561415)
              ·
                refine ⟨10880181297288711189842123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7253454198192474126561415 10880181297288711189842123)
                ·
                  refine ⟨16320271945933066784763185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10880181297288711189842123 16320271945933066784763185)
                  ·
                    refine ⟨12240203959449800088572389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16320271945933066784763185 12240203959449800088572389)
                    ·
                      refine ⟨2295038242396837516607323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12240203959449800088572389 2295038242396837516607323)
                      ·
                        rfl

theorem cell23_4469571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_4469571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469571 prefixEnd_4469571 := by exact prefixLift 4469571
  have htrace : WordTrace (prefixWord ++ tailWord_4469571) baseStart_4469571 baseEnd_4469571 := by
    simpa [prefixWord, tailWord_4469571, baseEnd_4469571] using wordTrace_append hprefix tailTrace_4469571
  have hstable : (prefixWord ++ tailWord_4469571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469571).length < 2 ^ (prefixWord ++ tailWord_4469571).sum := by decide
  have hdescent : baseEnd_4469571 < baseStart_4469571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469602 : List Nat := [3, 3, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_4469602 : Nat := 118140960795 + 4469602 * 2 ^ 59
def prefixEnd_4469602 : Nat := 4983230072969 + 3 ^ 40 * 4469602 * 2
def baseEnd_4469602 : Nat := 765018053432375631773227

theorem tailTrace_4469602 : CollatzResearch.WordTrace tailWord_4469602 prefixEnd_4469602 765018053432375631773227 := by
  unfold tailWord_4469602
  simp only [CollatzResearch.WordTrace]
  refine ⟨40754944388350694023382765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108679851702268517395687373 40754944388350694023382765)
  ·
    refine ⟨15283104145631510258768537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40754944388350694023382765 15283104145631510258768537)
    ·
      refine ⟨11462328109223632694076403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15283104145631510258768537 11462328109223632694076403)
      ·
        refine ⟨17193492163835449041114605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11462328109223632694076403 17193492163835449041114605)
        ·
          refine ⟨6447559561438293390417977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17193492163835449041114605 6447559561438293390417977)
          ·
            refine ⟨4835669671078720042813483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6447559561438293390417977 4835669671078720042813483)
            ·
              refine ⟨7253504506618080064220225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4835669671078720042813483 7253504506618080064220225)
              ·
                refine ⟨5440128379963560048165169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7253504506618080064220225 5440128379963560048165169)
                ·
                  refine ⟨4080096284972670036123877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5440128379963560048165169 4080096284972670036123877)
                  ·
                    refine ⟨765018053432375631773227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4080096284972670036123877 765018053432375631773227)
                    ·
                      rfl

theorem cell23_4469602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_4469602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469602 prefixEnd_4469602 := by exact prefixLift 4469602
  have htrace : WordTrace (prefixWord ++ tailWord_4469602) baseStart_4469602 baseEnd_4469602 := by
    simpa [prefixWord, tailWord_4469602, baseEnd_4469602] using wordTrace_append hprefix tailTrace_4469602
  have hstable : (prefixWord ++ tailWord_4469602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469602).length < 2 ^ (prefixWord ++ tailWord_4469602).sum := by decide
  have hdescent : baseEnd_4469602 < baseStart_4469602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469618 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 5, 3, 2]
def baseStart_4469618 : Nat := 118140960795 + 4469618 * 2 ^ 59
def prefixEnd_4469618 : Nat := 4983230072969 + 3 ^ 40 * 4469618 * 2
def baseEnd_4469618 : Nat := 2295062375987598832719607

theorem tailTrace_4469618 : CollatzResearch.WordTrace tailWord_4469618 prefixEnd_4469618 2295062375987598832719607 := by
  unfold tailWord_4469618
  simp only [CollatzResearch.WordTrace]
  refine ⟨40755090280336202706528377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108680240747563207217409005 40755090280336202706528377)
  ·
    refine ⟨30566317710252152029896283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40755090280336202706528377 30566317710252152029896283)
    ·
      refine ⟨45849476565378228044844425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30566317710252152029896283 45849476565378228044844425)
      ·
        refine ⟨34387107424033671033633319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45849476565378228044844425 34387107424033671033633319)
        ·
          refine ⟨51580661136050506550449979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34387107424033671033633319 51580661136050506550449979)
          ·
            refine ⟨77370991704075759825674969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51580661136050506550449979 77370991704075759825674969)
            ·
              refine ⟨58028243778056819869256227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77370991704075759825674969 58028243778056819869256227)
              ·
                refine ⟨87042365667085229803884341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58028243778056819869256227 87042365667085229803884341)
                ·
                  refine ⟨8160221781289240294114157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87042365667085229803884341 8160221781289240294114157)
                  ·
                    refine ⟨3060083167983465110292809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8160221781289240294114157 3060083167983465110292809)
                    ·
                      refine ⟨2295062375987598832719607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3060083167983465110292809 2295062375987598832719607)
                      ·
                        rfl

theorem cell23_4469618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_4469618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469618 prefixEnd_4469618 := by exact prefixLift 4469618
  have htrace : WordTrace (prefixWord ++ tailWord_4469618) baseStart_4469618 baseEnd_4469618 := by
    simpa [prefixWord, tailWord_4469618, baseEnd_4469618] using wordTrace_append hprefix tailTrace_4469618
  have hstable : (prefixWord ++ tailWord_4469618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469618).length < 2 ^ (prefixWord ++ tailWord_4469618).sum := by decide
  have hdescent : baseEnd_4469618 < baseStart_4469618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469624 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 1, 8]
def baseStart_4469624 : Nat := 118140960795 + 4469624 * 2 ^ 59
def prefixEnd_4469624 : Nat := 4983230072969 + 3 ^ 40 * 4469624 * 2
def baseEnd_4469624 : Nat := 765021818957175269748193

theorem tailTrace_4469624 : CollatzResearch.WordTrace tailWord_4469624 prefixEnd_4469624 765021818957175269748193 := by
  unfold tailWord_4469624
  simp only [CollatzResearch.WordTrace]
  refine ⟨81510289979661536925415963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108680386639548715900554617 81510289979661536925415963)
  ·
    refine ⟨122265434969492305388123945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81510289979661536925415963 122265434969492305388123945)
    ·
      refine ⟨91699076227119229041092959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122265434969492305388123945 91699076227119229041092959)
      ·
        refine ⟨137548614340678843561639439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91699076227119229041092959 137548614340678843561639439)
        ·
          refine ⟨206322921511018265342459159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137548614340678843561639439 206322921511018265342459159)
          ·
            refine ⟨309484382266527398013688739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206322921511018265342459159 309484382266527398013688739)
            ·
              refine ⟨464226573399791097020533109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309484382266527398013688739 464226573399791097020533109)
              ·
                refine ⟨43521241256230415345674979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 464226573399791097020533109 43521241256230415345674979)
                ·
                  refine ⟨65281861884345623018512469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43521241256230415345674979 65281861884345623018512469)
                  ·
                    refine ⟨765021818957175269748193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 65281861884345623018512469 765021818957175269748193)
                    ·
                      rfl

theorem cell23_4469624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_4469624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469624 prefixEnd_4469624 := by exact prefixLift 4469624
  have htrace : WordTrace (prefixWord ++ tailWord_4469624) baseStart_4469624 baseEnd_4469624 := by
    simpa [prefixWord, tailWord_4469624, baseEnd_4469624] using wordTrace_append hprefix tailTrace_4469624
  have hstable : (prefixWord ++ tailWord_4469624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469624).length < 2 ^ (prefixWord ++ tailWord_4469624).sum := by decide
  have hdescent : baseEnd_4469624 < baseStart_4469624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469635 : List Nat := [1, 1, 1, 3, 4, 1, 4, 2, 1, 3, 2]
def baseStart_4469635 : Nat := 118140960795 + 4469635 * 2 ^ 59
def prefixEnd_4469635 : Nat := 4983230072969 + 3 ^ 40 * 4469635 * 2
def baseEnd_4469635 : Nat := 2295071105158725266207029

theorem tailTrace_4469635 : CollatzResearch.WordTrace tailWord_4469635 prefixEnd_4469635 2295071105158725266207029 := by
  unfold tailWord_4469635
  simp only [CollatzResearch.WordTrace]
  refine ⟨163020981162283222729482359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108680654108188815152988239 163020981162283222729482359)
  ·
    refine ⟨244531471743424834094223539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163020981162283222729482359 244531471743424834094223539)
    ·
      refine ⟨366797207615137251141335309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244531471743424834094223539 366797207615137251141335309)
      ·
        refine ⟨137548952855676469178000741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 366797207615137251141335309 137548952855676469178000741)
        ·
          refine ⟨25790428660439337970875139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137548952855676469178000741 25790428660439337970875139)
          ·
            refine ⟨38685642990659006956312709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25790428660439337970875139 38685642990659006956312709)
            ·
              refine ⟨7253558060748563804308633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38685642990659006956312709 7253558060748563804308633)
              ·
                refine ⟨5440168545561422853231475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7253558060748563804308633 5440168545561422853231475)
                ·
                  refine ⟨8160252818342134279847213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5440168545561422853231475 8160252818342134279847213)
                  ·
                    refine ⟨3060094806878300354942705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8160252818342134279847213 3060094806878300354942705)
                    ·
                      refine ⟨2295071105158725266207029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3060094806878300354942705 2295071105158725266207029)
                      ·
                        rfl

theorem cell23_4469635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 3, 2].length) (baseStart_4469635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469635 prefixEnd_4469635 := by exact prefixLift 4469635
  have htrace : WordTrace (prefixWord ++ tailWord_4469635) baseStart_4469635 baseEnd_4469635 := by
    simpa [prefixWord, tailWord_4469635, baseEnd_4469635] using wordTrace_append hprefix tailTrace_4469635
  have hstable : (prefixWord ++ tailWord_4469635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469635).length < 2 ^ (prefixWord ++ tailWord_4469635).sum := by decide
  have hdescent : baseEnd_4469635 < baseStart_4469635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469686 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_4469686 : Nat := 118140960795 + 4469686 * 2 ^ 59
def prefixEnd_4469686 : Nat := 4983230072969 + 3 ^ 40 * 4469686 * 2
def baseEnd_4469686 : Nat := 2295097292672104566669295

theorem tailTrace_4469686 : CollatzResearch.WordTrace tailWord_4469686 prefixEnd_4469686 2295097292672104566669295 := by
  unfold tailWord_4469686
  simp only [CollatzResearch.WordTrace]
  refine ⟨10188927580318653652474307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108681894190065638959725941 10188927580318653652474307)
  ·
    refine ⟨15283391370477980478711461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10188927580318653652474307 15283391370477980478711461)
    ·
      refine ⟨2865635881964621339758399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15283391370477980478711461 2865635881964621339758399)
      ·
        refine ⟨4298453822946932009637599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2865635881964621339758399 4298453822946932009637599)
        ·
          refine ⟨6447680734420398014456399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4298453822946932009637599 6447680734420398014456399)
          ·
            refine ⟨9671521101630597021684599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6447680734420398014456399 9671521101630597021684599)
            ·
              refine ⟨14507281652445895532526899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9671521101630597021684599 14507281652445895532526899)
              ·
                refine ⟨21760922478668843298790349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14507281652445895532526899 21760922478668843298790349)
                ·
                  refine ⟨8160345929500816237046381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21760922478668843298790349 8160345929500816237046381)
                  ·
                    refine ⟨3060129723562806088892393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8160345929500816237046381 3060129723562806088892393)
                    ·
                      refine ⟨2295097292672104566669295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3060129723562806088892393 2295097292672104566669295)
                      ·
                        rfl

theorem cell23_4469686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_4469686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469686 prefixEnd_4469686 := by exact prefixLift 4469686
  have htrace : WordTrace (prefixWord ++ tailWord_4469686) baseStart_4469686 baseEnd_4469686 := by
    simpa [prefixWord, tailWord_4469686, baseEnd_4469686] using wordTrace_append hprefix tailTrace_4469686
  have hstable : (prefixWord ++ tailWord_4469686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469686).length < 2 ^ (prefixWord ++ tailWord_4469686).sum := by decide
  have hdescent : baseEnd_4469686 < baseStart_4469686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469711 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 5]
def baseStart_4469711 : Nat := 118140960795 + 4469711 * 2 ^ 59
def prefixEnd_4469711 : Nat := 4983230072969 + 3 ^ 40 * 4469711 * 2
def baseEnd_4469711 : Nat := 2295110129688466968856679

theorem tailTrace_4469711 : CollatzResearch.WordTrace tailWord_4469711 prefixEnd_4469711 2295110129688466968856679 := by
  unfold tailWord_4469711
  simp only [CollatzResearch.WordTrace]
  refine ⟨163023753110007887709248987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108682502073338591806165991 163023753110007887709248987)
  ·
    refine ⟨244535629665011831563873481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163023753110007887709248987 244535629665011831563873481)
    ·
      refine ⟨183401722248758873672905111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244535629665011831563873481 183401722248758873672905111)
      ·
        refine ⟨275102583373138310509357667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183401722248758873672905111 275102583373138310509357667)
        ·
          refine ⟨412653875059707465764036501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275102583373138310509357667 412653875059707465764036501)
          ·
            refine ⟨19343150393423787457689211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 412653875059707465764036501 19343150393423787457689211)
            ·
              refine ⟨29014725590135681186533817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19343150393423787457689211 29014725590135681186533817)
              ·
                refine ⟨21761044192601760889900363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29014725590135681186533817 21761044192601760889900363)
                ·
                  refine ⟨32641566288902641334850545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21761044192601760889900363 32641566288902641334850545)
                  ·
                    refine ⟨24481174716676981001137909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32641566288902641334850545 24481174716676981001137909)
                    ·
                      refine ⟨2295110129688466968856679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24481174716676981001137909 2295110129688466968856679)
                      ·
                        rfl

theorem cell23_4469711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_4469711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469711 prefixEnd_4469711 := by exact prefixLift 4469711
  have htrace : WordTrace (prefixWord ++ tailWord_4469711) baseStart_4469711 baseEnd_4469711 := by
    simpa [prefixWord, tailWord_4469711, baseEnd_4469711] using wordTrace_append hprefix tailTrace_4469711
  have hstable : (prefixWord ++ tailWord_4469711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469711).length < 2 ^ (prefixWord ++ tailWord_4469711).sum := by decide
  have hdescent : baseEnd_4469711 < baseStart_4469711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469722 : List Nat := [3, 1, 1, 2, 4, 3, 2, 2, 5]
def baseStart_4469722 : Nat := 118140960795 + 4469722 * 2 ^ 59
def prefixEnd_4469722 : Nat := 4983230072969 + 3 ^ 40 * 4469722 * 2
def baseEnd_4469722 : Nat := 255012864219518491757681

theorem tailTrace_4469722 : CollatzResearch.WordTrace tailWord_4469722 prefixEnd_4469722 255012864219518491757681 := by
  unfold tailWord_4469722
  simp only [CollatzResearch.WordTrace]
  refine ⟨40756038578242009146974855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108682769541978691058599613 40756038578242009146974855)
  ·
    refine ⟨61134057867363013720462283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40756038578242009146974855 61134057867363013720462283)
    ·
      refine ⟨91701086801044520580693425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61134057867363013720462283 91701086801044520580693425)
      ·
        refine ⟨68775815100783390435520069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91701086801044520580693425 68775815100783390435520069)
        ·
          refine ⟨12895465331396885706660013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68775815100783390435520069 12895465331396885706660013)
          ·
            refine ⟨4835799499273832139997505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12895465331396885706660013 4835799499273832139997505)
            ·
              refine ⟨3626849624455374104998129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4835799499273832139997505 3626849624455374104998129)
              ·
                refine ⟨2720137218341530578748597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3626849624455374104998129 2720137218341530578748597)
                ·
                  refine ⟨255012864219518491757681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2720137218341530578748597 255012864219518491757681)
                  ·
                    rfl

theorem cell23_4469722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 5].length) (baseStart_4469722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469722 prefixEnd_4469722 := by exact prefixLift 4469722
  have htrace : WordTrace (prefixWord ++ tailWord_4469722) baseStart_4469722 baseEnd_4469722 := by
    simpa [prefixWord, tailWord_4469722, baseEnd_4469722] using wordTrace_append hprefix tailTrace_4469722
  have hstable : (prefixWord ++ tailWord_4469722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469722).length < 2 ^ (prefixWord ++ tailWord_4469722).sum := by decide
  have hdescent : baseEnd_4469722 < baseStart_4469722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469725 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_4469725 : Nat := 118140960795 + 4469725 * 2 ^ 59
def prefixEnd_4469725 : Nat := 4983230072969 + 3 ^ 40 * 4469725 * 2
def baseEnd_4469725 : Nat := 2295117318417629914081615

theorem tailTrace_4469725 : CollatzResearch.WordTrace tailWord_4469725 prefixEnd_4469725 2295117318417629914081615 := by
  unfold tailWord_4469725
  simp only [CollatzResearch.WordTrace]
  refine ⟨163024263731957168100258629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108682842487971445400172419 163024263731957168100258629)
  ·
    refine ⟨30567049449741969018798493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163024263731957168100258629 30567049449741969018798493)
    ·
      refine ⟨11462643543653238382049435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30567049449741969018798493 11462643543653238382049435)
      ·
        refine ⟨17193965315479857573074153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11462643543653238382049435 17193965315479857573074153)
        ·
          refine ⟨12895473986609893179805615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17193965315479857573074153 12895473986609893179805615)
          ·
            refine ⟨19343210979914839769708423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12895473986609893179805615 19343210979914839769708423)
            ·
              refine ⟨29014816469872259654562635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19343210979914839769708423 29014816469872259654562635)
              ·
                refine ⟨43522224704808389481843953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29014816469872259654562635 43522224704808389481843953)
                ·
                  refine ⟨32641668528606292111382965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43522224704808389481843953 32641668528606292111382965)
                  ·
                    refine ⟨3060156424556839885442153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32641668528606292111382965 3060156424556839885442153)
                    ·
                      refine ⟨2295117318417629914081615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3060156424556839885442153 2295117318417629914081615)
                      ·
                        rfl

theorem cell23_4469725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_4469725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469725 prefixEnd_4469725 := by exact prefixLift 4469725
  have htrace : WordTrace (prefixWord ++ tailWord_4469725) baseStart_4469725 baseEnd_4469725 := by
    simpa [prefixWord, tailWord_4469725, baseEnd_4469725] using wordTrace_append hprefix tailTrace_4469725
  have hstable : (prefixWord ++ tailWord_4469725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469725).length < 2 ^ (prefixWord ++ tailWord_4469725).sum := by decide
  have hdescent : baseEnd_4469725 < baseStart_4469725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469795 : List Nat := [1, 1, 1, 4, 3, 3, 3, 1, 6]
def baseStart_4469795 : Nat := 118140960795 + 4469795 * 2 ^ 59
def prefixEnd_4469795 : Nat := 4983230072969 + 3 ^ 40 * 4469795 * 2
def baseEnd_4469795 : Nat := 255017029118160515578477

theorem tailTrace_4469795 : CollatzResearch.WordTrace tailWord_4469795 prefixEnd_4469795 255017029118160515578477 := by
  unfold tailWord_4469795
  simp only [CollatzResearch.WordTrace]
  refine ⟨163026816841703570055306839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108684544561135713370204559 163026816841703570055306839)
  ·
    refine ⟨244540225262555355082960259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163026816841703570055306839 244540225262555355082960259)
    ·
      refine ⟨366810337893833032624440389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244540225262555355082960259 366810337893833032624440389)
      ·
        refine ⟨68776938355093693617082573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 366810337893833032624440389 68776938355093693617082573)
        ·
          refine ⟨25791351883160135106405965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68776938355093693617082573 25791351883160135106405965)
          ·
            refine ⟨9671756956185050664902237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25791351883160135106405965 9671756956185050664902237)
            ·
              refine ⟨3626908858569393999338339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9671756956185050664902237 3626908858569393999338339)
              ·
                refine ⟨5440363287854090999007509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3626908858569393999338339 5440363287854090999007509)
                ·
                  refine ⟨255017029118160515578477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5440363287854090999007509 255017029118160515578477)
                  ·
                    rfl

theorem cell23_4469795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 6].length) (baseStart_4469795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469795 prefixEnd_4469795 := by exact prefixLift 4469795
  have htrace : WordTrace (prefixWord ++ tailWord_4469795) baseStart_4469795 baseEnd_4469795 := by
    simpa [prefixWord, tailWord_4469795, baseEnd_4469795] using wordTrace_append hprefix tailTrace_4469795
  have hstable : (prefixWord ++ tailWord_4469795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469795).length < 2 ^ (prefixWord ++ tailWord_4469795).sum := by decide
  have hdescent : baseEnd_4469795 < baseStart_4469795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469815 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 2, 3, 2]
def baseStart_4469815 : Nat := 118140960795 + 4469815 * 2 ^ 59
def prefixEnd_4469815 : Nat := 4983230072969 + 3 ^ 40 * 4469815 * 2
def baseEnd_4469815 : Nat := 2295163531676534561956201

theorem tailTrace_4469815 : CollatzResearch.WordTrace tailWord_4469815 prefixEnd_4469815 2295163531676534561956201 := by
  unfold tailWord_4469815
  simp only [CollatzResearch.WordTrace]
  refine ⟨163027546301631113471034899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108685030867754075647356599 163027546301631113471034899)
  ·
    refine ⟨244541319452446670206552349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163027546301631113471034899 244541319452446670206552349)
    ·
      refine ⟨91702994794667501327457131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244541319452446670206552349 91702994794667501327457131)
      ·
        refine ⟨137554492192001251991185697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91702994794667501327457131 137554492192001251991185697)
        ·
          refine ⟨103165869144000938993389273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137554492192001251991185697 103165869144000938993389273)
          ·
            refine ⟨77374401858000704245041955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103165869144000938993389273 77374401858000704245041955)
            ·
              refine ⟨116061602787001056367562933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77374401858000704245041955 116061602787001056367562933)
              ·
                refine ⟨10880775261281349034459025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116061602787001056367562933 10880775261281349034459025)
                ·
                  refine ⟨8160581445961011775844269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10880775261281349034459025 8160581445961011775844269)
                  ·
                    refine ⟨3060218042235379415941601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8160581445961011775844269 3060218042235379415941601)
                    ·
                      refine ⟨2295163531676534561956201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3060218042235379415941601 2295163531676534561956201)
                      ·
                        rfl

theorem cell23_4469815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 3, 2].length) (baseStart_4469815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469815 prefixEnd_4469815 := by exact prefixLift 4469815
  have htrace : WordTrace (prefixWord ++ tailWord_4469815) baseStart_4469815 baseEnd_4469815 := by
    simpa [prefixWord, tailWord_4469815, baseEnd_4469815] using wordTrace_append hprefix tailTrace_4469815
  have hstable : (prefixWord ++ tailWord_4469815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469815).length < 2 ^ (prefixWord ++ tailWord_4469815).sum := by decide
  have hdescent : baseEnd_4469815 < baseStart_4469815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469846 : List Nat := [5, 2, 2, 1, 2, 2, 2, 1, 6]
def baseStart_4469846 : Nat := 118140960795 + 4469846 * 2 ^ 59
def prefixEnd_4469846 : Nat := 4983230072969 + 3 ^ 40 * 4469846 * 2
def baseEnd_4469846 : Nat := 255019938841869326740951

theorem tailTrace_4469846 : CollatzResearch.WordTrace tailWord_4469846 prefixEnd_4469846 255019938841869326740951 := by
  unfold tailWord_4469846
  simp only [CollatzResearch.WordTrace]
  refine ⟨10189292310282425360338337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108685784643012537176942261 10189292310282425360338337)
  ·
    refine ⟨7641969232711819020253753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10189292310282425360338337 7641969232711819020253753)
    ·
      refine ⟨5731476924533864265190315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7641969232711819020253753 5731476924533864265190315)
      ·
        refine ⟨8597215386800796397785473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5731476924533864265190315 8597215386800796397785473)
        ·
          refine ⟨6447911540100597298339105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8597215386800796397785473 6447911540100597298339105)
          ·
            refine ⟨4835933655075447973754329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6447911540100597298339105 4835933655075447973754329)
            ·
              refine ⟨3626950241306585980315747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4835933655075447973754329 3626950241306585980315747)
              ·
                refine ⟨5440425361959878970473621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3626950241306585980315747 5440425361959878970473621)
                ·
                  refine ⟨255019938841869326740951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5440425361959878970473621 255019938841869326740951)
                  ·
                    rfl

theorem cell23_4469846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_4469846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469846 prefixEnd_4469846 := by exact prefixLift 4469846
  have htrace : WordTrace (prefixWord ++ tailWord_4469846) baseStart_4469846 baseEnd_4469846 := by
    simpa [prefixWord, tailWord_4469846, baseEnd_4469846] using wordTrace_append hprefix tailTrace_4469846
  have hstable : (prefixWord ++ tailWord_4469846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469846).length < 2 ^ (prefixWord ++ tailWord_4469846).sum := by decide
  have hdescent : baseEnd_4469846 < baseStart_4469846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469848 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 1, 1, 5]
def baseStart_4469848 : Nat := 118140960795 + 4469848 * 2 ^ 59
def prefixEnd_4469848 : Nat := 4983230072969 + 3 ^ 40 * 4469848 * 2
def baseEnd_4469848 : Nat := 2295180476538132932843549

theorem tailTrace_4469848 : CollatzResearch.WordTrace tailWord_4469848 prefixEnd_4469848 2295180476538132932843549 := by
  unfold tailWord_4469848
  simp only [CollatzResearch.WordTrace]
  refine ⟨81514374955255780053493099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108685833273674373404657465 81514374955255780053493099)
  ·
    refine ⟨122271562432883670080239649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81514374955255780053493099 122271562432883670080239649)
    ·
      refine ⟨91703671824662752560179737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122271562432883670080239649 91703671824662752560179737)
      ·
        refine ⟨68777753868497064420134803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91703671824662752560179737 68777753868497064420134803)
        ·
          refine ⟨103166630802745596630202205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68777753868497064420134803 103166630802745596630202205)
          ·
            refine ⟨38687486551029598736325827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103166630802745596630202205 38687486551029598736325827)
            ·
              refine ⟨58031229826544398104488741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38687486551029598736325827 58031229826544398104488741)
              ·
                refine ⟨10880855592477074644591639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58031229826544398104488741 10880855592477074644591639)
                ·
                  refine ⟨16321283388715611966887459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10880855592477074644591639 16321283388715611966887459)
                  ·
                    refine ⟨24481925083073417950331189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16321283388715611966887459 24481925083073417950331189)
                    ·
                      refine ⟨2295180476538132932843549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24481925083073417950331189 2295180476538132932843549)
                      ·
                        rfl

theorem cell23_4469848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_4469848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469848 prefixEnd_4469848 := by exact prefixLift 4469848
  have htrace : WordTrace (prefixWord ++ tailWord_4469848) baseStart_4469848 baseEnd_4469848 := by
    simpa [prefixWord, tailWord_4469848, baseEnd_4469848] using wordTrace_append hprefix tailTrace_4469848
  have hstable : (prefixWord ++ tailWord_4469848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469848).length < 2 ^ (prefixWord ++ tailWord_4469848).sum := by decide
  have hdescent : baseEnd_4469848 < baseStart_4469848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469855 : List Nat := [1, 1, 2, 3, 1, 1, 5, 3, 2, 4]
def baseStart_4469855 : Nat := 118140960795 + 4469855 * 2 ^ 59
def prefixEnd_4469855 : Nat := 4983230072969 + 3 ^ 40 * 4469855 * 2
def baseEnd_4469855 : Nat := 765061356967571468485339

theorem tailTrace_4469855 : CollatzResearch.WordTrace tailWord_4469855 prefixEnd_4469855 765061356967571468485339 := by
  unfold tailWord_4469855
  simp only [CollatzResearch.WordTrace]
  refine ⟨163029005221486200302491019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108686003480990800201660679 163029005221486200302491019)
  ·
    refine ⟨244543507832229300453736529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163029005221486200302491019 244543507832229300453736529)
    ·
      refine ⟨183407630874171975340302397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244543507832229300453736529 183407630874171975340302397)
      ·
        refine ⟨68777861577814490752613399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183407630874171975340302397 68777861577814490752613399)
        ·
          refine ⟨103166792366721736128920099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68777861577814490752613399 103166792366721736128920099)
          ·
            refine ⟨154750188550082604193380149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103166792366721736128920099 154750188550082604193380149)
            ·
              refine ⟨14507830176570244143129389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154750188550082604193380149 14507830176570244143129389)
              ·
                refine ⟨5440436316213841553673521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14507830176570244143129389 5440436316213841553673521)
                ·
                  refine ⟨4080327237160381165255141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5440436316213841553673521 4080327237160381165255141)
                  ·
                    refine ⟨765061356967571468485339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4080327237160381165255141 765061356967571468485339)
                    ·
                      rfl

theorem cell23_4469855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 4].length) (baseStart_4469855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469855 prefixEnd_4469855 := by exact prefixLift 4469855
  have htrace : WordTrace (prefixWord ++ tailWord_4469855) baseStart_4469855 baseEnd_4469855 := by
    simpa [prefixWord, tailWord_4469855, baseEnd_4469855] using wordTrace_append hprefix tailTrace_4469855
  have hstable : (prefixWord ++ tailWord_4469855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469855).length < 2 ^ (prefixWord ++ tailWord_4469855).sum := by decide
  have hdescent : baseEnd_4469855 < baseStart_4469855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469865 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 3, 2, 3]
def baseStart_4469865 : Nat := 118140960795 + 4469865 * 2 ^ 59
def prefixEnd_4469865 : Nat := 4983230072969 + 3 ^ 40 * 4469865 * 2
def baseEnd_4469865 : Nat := 2295189205709259366330971

theorem tailTrace_4469865 : CollatzResearch.WordTrace tailWord_4469865 prefixEnd_4469865 2295189205709259366330971 := by
  unfold tailWord_4469865
  simp only [CollatzResearch.WordTrace]
  refine ⟨163029369951449972010355049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108686246634299981340236699 163029369951449972010355049)
  ·
    refine ⟨122272027463587479007766287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163029369951449972010355049 122272027463587479007766287)
    ·
      refine ⟨183408041195381218511649431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122272027463587479007766287 183408041195381218511649431)
      ·
        refine ⟨275112061793071827767474147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183408041195381218511649431 275112061793071827767474147)
        ·
          refine ⟨412668092689607741651211221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275112061793071827767474147 412668092689607741651211221)
          ·
            refine ⟨9671908422412681444950263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 412668092689607741651211221 9671908422412681444950263)
            ·
              refine ⟨14507862633619022167425395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9671908422412681444950263 14507862633619022167425395)
              ·
                refine ⟨21761793950428533251138093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14507862633619022167425395 21761793950428533251138093)
                ·
                  refine ⟨8160672731410699969176785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21761793950428533251138093 8160672731410699969176785)
                  ·
                    refine ⟨6120504548558024976882589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8160672731410699969176785 6120504548558024976882589)
                    ·
                      refine ⟨2295189205709259366330971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6120504548558024976882589 2295189205709259366330971)
                      ·
                        rfl

theorem cell23_4469865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 2, 3].length) (baseStart_4469865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469865 prefixEnd_4469865 := by exact prefixLift 4469865
  have htrace : WordTrace (prefixWord ++ tailWord_4469865) baseStart_4469865 baseEnd_4469865 := by
    simpa [prefixWord, tailWord_4469865, baseEnd_4469865] using wordTrace_append hprefix tailTrace_4469865
  have hstable : (prefixWord ++ tailWord_4469865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469865).length < 2 ^ (prefixWord ++ tailWord_4469865).sum := by decide
  have hdescent : baseEnd_4469865 < baseStart_4469865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469879 : List Nat := [1, 1, 3, 1, 1, 4, 2, 5, 1, 2, 2]
def baseStart_4469879 : Nat := 118140960795 + 4469879 * 2 ^ 59
def prefixEnd_4469879 : Nat := 4983230072969 + 3 ^ 40 * 4469879 * 2
def baseEnd_4469879 : Nat := 2295196394438422311555907

theorem tailTrace_4469879 : CollatzResearch.WordTrace tailWord_4469879 prefixEnd_4469879 2295196394438422311555907 := by
  unfold tailWord_4469879
  simp only [CollatzResearch.WordTrace]
  refine ⟨163029880573399252401364691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108686587048932834934243127 163029880573399252401364691)
  ·
    refine ⟨244544820860098878602047037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163029880573399252401364691 244544820860098878602047037)
    ·
      refine ⟨91704307822537079475767639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244544820860098878602047037 91704307822537079475767639)
      ·
        refine ⟨137556461733805619213651459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91704307822537079475767639 137556461733805619213651459)
        ·
          refine ⟨206334692600708428820477189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137556461733805619213651459 206334692600708428820477189)
          ·
            refine ⟨38687754862632830403839473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206334692600708428820477189 38687754862632830403839473)
            ·
              refine ⟨29015816146974622802879605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38687754862632830403839473 29015816146974622802879605)
              ·
                refine ⟨2720232763778870887769963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29015816146974622802879605 2720232763778870887769963)
                ·
                  refine ⟨4080349145668306331654945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2720232763778870887769963 4080349145668306331654945)
                  ·
                    refine ⟨3060261859251229748741209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4080349145668306331654945 3060261859251229748741209)
                    ·
                      refine ⟨2295196394438422311555907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3060261859251229748741209 2295196394438422311555907)
                      ·
                        rfl

theorem cell23_4469879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 1, 2, 2].length) (baseStart_4469879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469879 prefixEnd_4469879 := by exact prefixLift 4469879
  have htrace : WordTrace (prefixWord ++ tailWord_4469879) baseStart_4469879 baseEnd_4469879 := by
    simpa [prefixWord, tailWord_4469879, baseEnd_4469879] using wordTrace_append hprefix tailTrace_4469879
  have hstable : (prefixWord ++ tailWord_4469879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469879).length < 2 ^ (prefixWord ++ tailWord_4469879).sum := by decide
  have hdescent : baseEnd_4469879 < baseStart_4469879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469898 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 1, 9]
def baseStart_4469898 : Nat := 118140960795 + 4469898 * 2 ^ 59
def prefixEnd_4469898 : Nat := 4983230072969 + 3 ^ 40 * 4469898 * 2
def baseEnd_4469898 : Nat := 765068716856952579072773

theorem tailTrace_4469898 : CollatzResearch.WordTrace tailWord_4469898 prefixEnd_4469898 765068716856952579072773 := by
  unfold tailWord_4469898
  simp only [CollatzResearch.WordTrace]
  refine ⟨40757643390082604661576587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108687049040220279097537565 40757643390082604661576587)
  ·
    refine ⟨61136465085123906992364881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40757643390082604661576587 61136465085123906992364881)
    ·
      refine ⟨45852348813842930244273661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61136465085123906992364881 45852348813842930244273661)
      ·
        refine ⟨17194630805191098841602623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45852348813842930244273661 17194630805191098841602623)
        ·
          refine ⟨25791946207786648262403935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17194630805191098841602623 25791946207786648262403935)
          ·
            refine ⟨38687919311679972393605903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25791946207786648262403935 38687919311679972393605903)
            ·
              refine ⟨58031878967519958590408855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38687919311679972393605903 58031878967519958590408855)
              ·
                refine ⟨87047818451279937885613283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58031878967519958590408855 87047818451279937885613283)
                ·
                  refine ⟨130571727676919906828419925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87047818451279937885613283 130571727676919906828419925)
                  ·
                    refine ⟨765068716856952579072773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 130571727676919906828419925 765068716856952579072773)
                    ·
                      rfl

theorem cell23_4469898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_4469898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469898 prefixEnd_4469898 := by exact prefixLift 4469898
  have htrace : WordTrace (prefixWord ++ tailWord_4469898) baseStart_4469898 baseEnd_4469898 := by
    simpa [prefixWord, tailWord_4469898, baseEnd_4469898] using wordTrace_append hprefix tailTrace_4469898
  have hstable : (prefixWord ++ tailWord_4469898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469898).length < 2 ^ (prefixWord ++ tailWord_4469898).sum := by decide
  have hdescent : baseEnd_4469898 < baseStart_4469898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469912 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 1, 3, 3]
def baseStart_4469912 : Nat := 118140960795 + 4469912 * 2 ^ 59
def prefixEnd_4469912 : Nat := 4983230072969 + 3 ^ 40 * 4469912 * 2
def baseEnd_4469912 : Nat := 2295213339300020682443255

theorem tailTrace_4469912 : CollatzResearch.WordTrace tailWord_4469912 prefixEnd_4469912 2295213339300020682443255 := by
  unfold tailWord_4469912
  simp only [CollatzResearch.WordTrace]
  refine ⟨81515542091139849518657995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108687389454853132691543993 81515542091139849518657995)
  ·
    refine ⟨122273313136709774277986993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81515542091139849518657995 122273313136709774277986993)
    ·
      refine ⟨91704984852532330708490245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122273313136709774277986993 91704984852532330708490245)
      ·
        refine ⟨17194684659849812007841921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91704984852532330708490245 17194684659849812007841921)
        ·
          refine ⟨12896013494887359005881441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17194684659849812007841921 12896013494887359005881441)
          ·
            refine ⟨9672010121165519254411081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12896013494887359005881441 9672010121165519254411081)
            ·
              refine ⟨7254007590874139440808311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9672010121165519254411081 7254007590874139440808311)
              ·
                refine ⟨10881011386311209161212467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7254007590874139440808311 10881011386311209161212467)
                ·
                  refine ⟨16321517079466813741818701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10881011386311209161212467 16321517079466813741818701)
                  ·
                    refine ⟨6120568904800055153182013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16321517079466813741818701 6120568904800055153182013)
                    ·
                      refine ⟨2295213339300020682443255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6120568904800055153182013 2295213339300020682443255)
                      ·
                        rfl

theorem cell23_4469912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_4469912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469912 prefixEnd_4469912 := by exact prefixLift 4469912
  have htrace : WordTrace (prefixWord ++ tailWord_4469912) baseStart_4469912 baseEnd_4469912 := by
    simpa [prefixWord, tailWord_4469912, baseEnd_4469912] using wordTrace_append hprefix tailTrace_4469912
  have hstable : (prefixWord ++ tailWord_4469912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469912).length < 2 ^ (prefixWord ++ tailWord_4469912).sum := by decide
  have hdescent : baseEnd_4469912 < baseStart_4469912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469933 : List Nat := [1, 5, 2, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_4469933 : Nat := 118140960795 + 4469933 * 2 ^ 59
def prefixEnd_4469933 : Nat := 4983230072969 + 3 ^ 40 * 4469933 * 2
def baseEnd_4469933 : Nat := 2295224122393765100280659

theorem tailTrace_4469933 : CollatzResearch.WordTrace tailWord_4469933 prefixEnd_4469933 2295224122393765100280659 := by
  unfold tailWord_4469933
  simp only [CollatzResearch.WordTrace]
  refine ⟨163031850115203619623830453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108687900076802413082553635 163031850115203619623830453)
  ·
    refine ⟨15284235948300339339734105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 163031850115203619623830453 15284235948300339339734105)
    ·
      refine ⟨11463176961225254504800579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15284235948300339339734105 11463176961225254504800579)
      ·
        refine ⟨17194765441837881757200869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11463176961225254504800579 17194765441837881757200869)
        ·
          refine ⟨3224018520344602829475163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17194765441837881757200869 3224018520344602829475163)
          ·
            refine ⟨4836027780516904244212745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3224018520344602829475163 4836027780516904244212745)
            ·
              refine ⟨3627020835387678183159559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4836027780516904244212745 3627020835387678183159559)
              ·
                refine ⟨5440531253081517274739339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3627020835387678183159559 5440531253081517274739339)
                ·
                  refine ⟨8160796879622275912109009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5440531253081517274739339 8160796879622275912109009)
                  ·
                    refine ⟨6120597659716706934081757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8160796879622275912109009 6120597659716706934081757)
                    ·
                      refine ⟨2295224122393765100280659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6120597659716706934081757 2295224122393765100280659)
                      ·
                        rfl

theorem cell23_4469933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_4469933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469933 prefixEnd_4469933 := by exact prefixLift 4469933
  have htrace : WordTrace (prefixWord ++ tailWord_4469933) baseStart_4469933 baseEnd_4469933 := by
    simpa [prefixWord, tailWord_4469933, baseEnd_4469933] using wordTrace_append hprefix tailTrace_4469933
  have hstable : (prefixWord ++ tailWord_4469933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469933).length < 2 ^ (prefixWord ++ tailWord_4469933).sum := by decide
  have hdescent : baseEnd_4469933 < baseStart_4469933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4469939 : List Nat := [1, 1, 1, 2, 3, 2, 6, 1, 1, 3, 2]
def baseStart_4469939 : Nat := 118140960795 + 4469939 * 2 ^ 59
def prefixEnd_4469939 : Nat := 4983230072969 + 3 ^ 40 * 4469939 * 2
def baseEnd_4469939 : Nat := 2295227203277692076805631

theorem tailTrace_4469939 : CollatzResearch.WordTrace tailWord_4469939 prefixEnd_4469939 2295227203277692076805631 := by
  unfold tailWord_4469939
  simp only [CollatzResearch.WordTrace]
  refine ⟨163032068953181882648548871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108688045968787921765699247 163032068953181882648548871)
  ·
    refine ⟨244548103429772823972823307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163032068953181882648548871 244548103429772823972823307)
    ·
      refine ⟨366822155144659235959234961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244548103429772823972823307 366822155144659235959234961)
      ·
        refine ⟨275116616358494426969426221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366822155144659235959234961 275116616358494426969426221)
        ·
          refine ⟨103168731134435410113534833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275116616358494426969426221 103168731134435410113534833)
          ·
            refine ⟨77376548350826557585151125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103168731134435410113534833 77376548350826557585151125)
            ·
              refine ⟨3627025703944994886803959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 77376548350826557585151125 3627025703944994886803959)
              ·
                refine ⟨5440538555917492330205939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3627025703944994886803959 5440538555917492330205939)
                ·
                  refine ⟨8160807833876238495308909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5440538555917492330205939 8160807833876238495308909)
                  ·
                    refine ⟨3060302937703589435740841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8160807833876238495308909 3060302937703589435740841)
                    ·
                      refine ⟨2295227203277692076805631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3060302937703589435740841 2295227203277692076805631)
                      ·
                        rfl

theorem cell23_4469939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 1, 3, 2].length) (baseStart_4469939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4469939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4469939 prefixEnd_4469939 := by exact prefixLift 4469939
  have htrace : WordTrace (prefixWord ++ tailWord_4469939) baseStart_4469939 baseEnd_4469939 := by
    simpa [prefixWord, tailWord_4469939, baseEnd_4469939] using wordTrace_append hprefix tailTrace_4469939
  have hstable : (prefixWord ++ tailWord_4469939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4469939).length < 2 ^ (prefixWord ++ tailWord_4469939).sum := by decide
  have hdescent : baseEnd_4469939 < baseStart_4469939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4469939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470008 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 2, 2, 8]
def baseStart_4470008 : Nat := 118140960795 + 4470008 * 2 ^ 59
def prefixEnd_4470008 : Nat := 4983230072969 + 3 ^ 40 * 4470008 * 2
def baseEnd_4470008 : Nat := 2295262633442852306842813

theorem tailTrace_4470008 : CollatzResearch.WordTrace tailWord_4470008 prefixEnd_4470008 2295262633442852306842813 := by
  unfold tailWord_4470008
  simp only [CollatzResearch.WordTrace]
  refine ⟨81517292794965953716405339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108689723726621271621873785 81517292794965953716405339)
  ·
    refine ⟨122275939192448930574608009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81517292794965953716405339 122275939192448930574608009)
    ·
      refine ⟨91706954394336697930956007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122275939192448930574608009 91706954394336697930956007)
      ·
        refine ⟨137560431591505046896434011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91706954394336697930956007 137560431591505046896434011)
        ·
          refine ⟨206340647387257570344651017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137560431591505046896434011 206340647387257570344651017)
          ·
            refine ⟨154755485540443177758488263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206340647387257570344651017 154755485540443177758488263)
            ·
              refine ⟨232133228310664766637732395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154755485540443177758488263 232133228310664766637732395)
              ·
                refine ⟨348199842465997149956598593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232133228310664766637732395 348199842465997149956598593)
                ·
                  refine ⟨261149881849497862467448945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348199842465997149956598593 261149881849497862467448945)
                  ·
                    refine ⟨195862411387123396850586709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 261149881849497862467448945 195862411387123396850586709)
                    ·
                      refine ⟨2295262633442852306842813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 195862411387123396850586709 2295262633442852306842813)
                      ·
                        rfl

theorem cell23_4470008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_4470008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470008 prefixEnd_4470008 := by exact prefixLift 4470008
  have htrace : WordTrace (prefixWord ++ tailWord_4470008) baseStart_4470008 baseEnd_4470008 := by
    simpa [prefixWord, tailWord_4470008, baseEnd_4470008] using wordTrace_append hprefix tailTrace_4470008
  have hstable : (prefixWord ++ tailWord_4470008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470008).length < 2 ^ (prefixWord ++ tailWord_4470008).sum := by decide
  have hdescent : baseEnd_4470008 < baseStart_4470008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470015 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 5]
def baseStart_4470015 : Nat := 118140960795 + 4470015 * 2 ^ 59
def prefixEnd_4470015 : Nat := 4983230072969 + 3 ^ 40 * 4470015 * 2
def baseEnd_4470015 : Nat := 2295266227807433779455281

theorem tailTrace_4470015 : CollatzResearch.WordTrace tailWord_4470015 prefixEnd_4470015 2295266227807433779455281 := by
  unfold tailWord_4470015
  simp only [CollatzResearch.WordTrace]
  refine ⟨163034840900906547628315499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108689893933937698418876999 163034840900906547628315499)
  ·
    refine ⟨244552261351359821442473249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163034840900906547628315499 244552261351359821442473249)
    ·
      refine ⟨183414196013519866081854937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244552261351359821442473249 183414196013519866081854937)
      ·
        refine ⟨137560647010139899561391203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183414196013519866081854937 137560647010139899561391203)
        ·
          refine ⟨206340970515209849342086805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137560647010139899561391203 206340970515209849342086805)
          ·
            refine ⟨9672232992900461687910319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 206340970515209849342086805 9672232992900461687910319)
            ·
              refine ⟨14508349489350692531865479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9672232992900461687910319 14508349489350692531865479)
              ·
                refine ⟨21762524234026038797798219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14508349489350692531865479 21762524234026038797798219)
                ·
                  refine ⟨32643786351039058196697329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21762524234026038797798219 32643786351039058196697329)
                  ·
                    refine ⟨24482839763279293647522997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32643786351039058196697329 24482839763279293647522997)
                    ·
                      refine ⟨2295266227807433779455281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24482839763279293647522997 2295266227807433779455281)
                      ·
                        rfl

theorem cell23_4470015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_4470015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470015 prefixEnd_4470015 := by exact prefixLift 4470015
  have htrace : WordTrace (prefixWord ++ tailWord_4470015) baseStart_4470015 baseEnd_4470015 := by
    simpa [prefixWord, tailWord_4470015, baseEnd_4470015] using wordTrace_append hprefix tailTrace_4470015
  have hstable : (prefixWord ++ tailWord_4470015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470015).length < 2 ^ (prefixWord ++ tailWord_4470015).sum := by decide
  have hdescent : baseEnd_4470015 < baseStart_4470015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470025 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 4, 1, 4]
def baseStart_4470025 : Nat := 118140960795 + 4470025 * 2 ^ 59
def prefixEnd_4470025 : Nat := 4983230072969 + 3 ^ 40 * 4470025 * 2
def baseEnd_4470025 : Nat := 2295271362613978740330235

theorem tailTrace_4470025 : CollatzResearch.WordTrace tailWord_4470025 prefixEnd_4470025 2295271362613978740330235 := by
  unfold tailWord_4470025
  simp only [CollatzResearch.WordTrace]
  refine ⟨163035205630870319336179529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108690137087246879557453019 163035205630870319336179529)
  ·
    refine ⟨122276404223152739502134647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163035205630870319336179529 122276404223152739502134647)
    ·
      refine ⟨183414606334729109253201971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122276404223152739502134647 183414606334729109253201971)
      ·
        refine ⟨275121909502093663879802957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183414606334729109253201971 275121909502093663879802957)
        ·
          refine ⟨103170716063285123954926109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275121909502093663879802957 103170716063285123954926109)
          ·
            refine ⟨38689018523731921483097291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103170716063285123954926109 38689018523731921483097291)
            ·
              refine ⟨58033527785597882224645937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38689018523731921483097291 58033527785597882224645937)
              ·
                refine ⟨43525145839198411668484453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58033527785597882224645937 43525145839198411668484453)
                ·
                  refine ⟨8160964844849702187840835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43525145839198411668484453 8160964844849702187840835)
                  ·
                    refine ⟨12241447267274553281761253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8160964844849702187840835 12241447267274553281761253)
                    ·
                      refine ⟨2295271362613978740330235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12241447267274553281761253 2295271362613978740330235)
                      ·
                        rfl

theorem cell23_4470025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 1, 4].length) (baseStart_4470025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470025 prefixEnd_4470025 := by exact prefixLift 4470025
  have htrace : WordTrace (prefixWord ++ tailWord_4470025) baseStart_4470025 baseEnd_4470025 := by
    simpa [prefixWord, tailWord_4470025, baseEnd_4470025] using wordTrace_append hprefix tailTrace_4470025
  have hstable : (prefixWord ++ tailWord_4470025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470025).length < 2 ^ (prefixWord ++ tailWord_4470025).sum := by decide
  have hdescent : baseEnd_4470025 < baseStart_4470025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470042 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4]
def baseStart_4470042 : Nat := 118140960795 + 4470042 * 2 ^ 59
def prefixEnd_4470042 : Nat := 4983230072969 + 3 ^ 40 * 4470042 * 2
def baseEnd_4470042 : Nat := 2295280091785105173817657

theorem tailTrace_4470042 : CollatzResearch.WordTrace tailWord_4470042 prefixEnd_4470042 2295280091785105173817657 := by
  unfold tailWord_4470042
  simp only [CollatzResearch.WordTrace]
  refine ⟨40758956417952182809887095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108690550447872487493032253 40758956417952182809887095)
  ·
    refine ⟨61138434626928274214830643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40758956417952182809887095 61138434626928274214830643)
    ·
      refine ⟨91707651940392411322245965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61138434626928274214830643 91707651940392411322245965)
      ·
        refine ⟨34390369477647154245842237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91707651940392411322245965 34390369477647154245842237)
        ·
          refine ⟨12896388554117682842190839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34390369477647154245842237 12896388554117682842190839)
          ·
            refine ⟨19344582831176524263286259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12896388554117682842190839 19344582831176524263286259)
            ·
              refine ⟨29016874246764786394929389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19344582831176524263286259 29016874246764786394929389)
              ·
                refine ⟨10881327842536794898098521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29016874246764786394929389 10881327842536794898098521)
                ·
                  refine ⟨8160995881902596173573891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10881327842536794898098521 8160995881902596173573891)
                  ·
                    refine ⟨12241493822853894260360837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8160995881902596173573891 12241493822853894260360837)
                    ·
                      refine ⟨2295280091785105173817657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12241493822853894260360837 2295280091785105173817657)
                      ·
                        rfl

theorem cell23_4470042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_4470042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470042 prefixEnd_4470042 := by exact prefixLift 4470042
  have htrace : WordTrace (prefixWord ++ tailWord_4470042) baseStart_4470042 baseEnd_4470042 := by
    simpa [prefixWord, tailWord_4470042, baseEnd_4470042] using wordTrace_append hprefix tailTrace_4470042
  have hstable : (prefixWord ++ tailWord_4470042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470042).length < 2 ^ (prefixWord ++ tailWord_4470042).sum := by decide
  have hdescent : baseEnd_4470042 < baseStart_4470042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470093 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_4470093 : Nat := 118140960795 + 4470093 * 2 ^ 59
def prefixEnd_4470093 : Nat := 4983230072969 + 3 ^ 40 * 4470093 * 2
def baseEnd_4470093 : Nat := 2295306279298484474279923

theorem tailTrace_4470093 : CollatzResearch.WordTrace tailWord_4470093 prefixEnd_4470093 2295306279298484474279923 := by
  unfold tailWord_4470093
  simp only [CollatzResearch.WordTrace]
  refine ⟨163037685794623966949654933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108691790529749311299769955 163037685794623966949654933)
  ·
    refine ⟨7642391521622998450765075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 163037685794623966949654933 7642391521622998450765075)
    ·
      refine ⟨11463587282434497676147613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7642391521622998450765075 11463587282434497676147613)
      ·
        refine ⟨4298845230912936628555355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11463587282434497676147613 4298845230912936628555355)
        ·
          refine ⟨6448267846369404942833033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4298845230912936628555355 6448267846369404942833033)
          ·
            refine ⟨4836200884777053707124775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6448267846369404942833033 4836200884777053707124775)
            ·
              refine ⟨7254301327165580560687163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4836200884777053707124775 7254301327165580560687163)
              ·
                refine ⟨10881451990748370841030745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7254301327165580560687163 10881451990748370841030745)
                ·
                  refine ⟨8161088993061278130773059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10881451990748370841030745 8161088993061278130773059)
                  ·
                    refine ⟨12241633489591917196159589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8161088993061278130773059 12241633489591917196159589)
                    ·
                      refine ⟨2295306279298484474279923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12241633489591917196159589 2295306279298484474279923)
                      ·
                        rfl

theorem cell23_4470093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_4470093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470093 prefixEnd_4470093 := by exact prefixLift 4470093
  have htrace : WordTrace (prefixWord ++ tailWord_4470093) baseStart_4470093 baseEnd_4470093 := by
    simpa [prefixWord, tailWord_4470093, baseEnd_4470093] using wordTrace_append hprefix tailTrace_4470093
  have hstable : (prefixWord ++ tailWord_4470093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470093).length < 2 ^ (prefixWord ++ tailWord_4470093).sum := by decide
  have hdescent : baseEnd_4470093 < baseStart_4470093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470146 : List Nat := [3, 4, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_4470146 : Nat := 118140960795 + 4470146 * 2 ^ 59
def prefixEnd_4470146 : Nat := 4983230072969 + 3 ^ 40 * 4470146 * 2
def baseEnd_4470146 : Nat := 765111164591057588972393

theorem tailTrace_4470146 : CollatzResearch.WordTrace tailWord_4470146 prefixEnd_4470146 765111164591057588972393 := by
  unfold tailWord_4470146
  simp only [CollatzResearch.WordTrace]
  refine ⟨40759904715857989250333573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108693079242287971334222861 40759904715857989250333573)
  ·
    refine ⟨7642482134223372984437545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40759904715857989250333573 7642482134223372984437545)
    ·
      refine ⟨5731861600667529738328159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7642482134223372984437545 5731861600667529738328159)
      ·
        refine ⟨8597792401001294607492239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5731861600667529738328159 8597792401001294607492239)
        ·
          refine ⟨12896688601501941911238359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8597792401001294607492239 12896688601501941911238359)
          ·
            refine ⟨19345032902252912866857539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12896688601501941911238359 19345032902252912866857539)
            ·
              refine ⟨29017549353379369300286309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19345032902252912866857539 29017549353379369300286309)
              ·
                refine ⟨5440790503758631743803683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29017549353379369300286309 5440790503758631743803683)
                ·
                  refine ⟨8161185755637947615705525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5440790503758631743803683 8161185755637947615705525)
                  ·
                    refine ⟨765111164591057588972393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8161185755637947615705525 765111164591057588972393)
                    ·
                      rfl

theorem cell23_4470146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_4470146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470146 prefixEnd_4470146 := by exact prefixLift 4470146
  have htrace : WordTrace (prefixWord ++ tailWord_4470146) baseStart_4470146 baseEnd_4470146 := by
    simpa [prefixWord, tailWord_4470146, baseEnd_4470146] using wordTrace_append hprefix tailTrace_4470146
  have hstable : (prefixWord ++ tailWord_4470146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470146).length < 2 ^ (prefixWord ++ tailWord_4470146).sum := by decide
  have hdescent : baseEnd_4470146 < baseStart_4470146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470155 : List Nat := [1, 1, 1, 1, 4, 3, 3, 9]
def baseStart_4470155 : Nat := 118140960795 + 4470155 * 2 ^ 59
def prefixEnd_4470155 : Nat := 4983230072969 + 3 ^ 40 * 4470155 * 2
def baseEnd_4470155 : Nat := 85012522781446786359431

theorem tailTrace_4470155 : CollatzResearch.WordTrace tailWord_4470155 prefixEnd_4470155 85012522781446786359431 := by
  unfold tailWord_4470155
  simp only [CollatzResearch.WordTrace]
  refine ⟨163039947120399351538411919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108693298080266234358941279 163039947120399351538411919)
  ·
    refine ⟨244559920680599027307617879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163039947120399351538411919 244559920680599027307617879)
    ·
      refine ⟨366839881020898540961426819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244559920680599027307617879 366839881020898540961426819)
      ·
        refine ⟨550259821531347811442140229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366839881020898540961426819 550259821531347811442140229)
        ·
          refine ⟨103173716537127714645401293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 550259821531347811442140229 103173716537127714645401293)
          ·
            refine ⟨38690143701422892992025485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103173716537127714645401293 38690143701422892992025485)
            ·
              refine ⟨14508803888033584872009557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38690143701422892992025485 14508803888033584872009557)
              ·
                refine ⟨85012522781446786359431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14508803888033584872009557 85012522781446786359431)
                ·
                  rfl

theorem cell23_4470155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 9].length) (baseStart_4470155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470155 prefixEnd_4470155 := by exact prefixLift 4470155
  have htrace : WordTrace (prefixWord ++ tailWord_4470155) baseStart_4470155 baseEnd_4470155 := by
    simpa [prefixWord, tailWord_4470155, baseEnd_4470155] using wordTrace_append hprefix tailTrace_4470155
  have hstable : (prefixWord ++ tailWord_4470155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470155).length < 2 ^ (prefixWord ++ tailWord_4470155).sum := by decide
  have hdescent : baseEnd_4470155 < baseStart_4470155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470169 : List Nat := [1, 2, 1, 2, 1, 5, 2, 3, 1, 2, 3]
def baseStart_4470169 : Nat := 118140960795 + 4470169 * 2 ^ 59
def prefixEnd_4470169 : Nat := 4983230072969 + 3 ^ 40 * 4470169 * 2
def baseEnd_4470169 : Nat := 2295345303828226176929573

theorem tailTrace_4470169 : CollatzResearch.WordTrace tailWord_4470169 prefixEnd_4470169 2295345303828226176929573 := by
  unfold tailWord_4470169
  simp only [CollatzResearch.WordTrace]
  refine ⟨163040457742348631929421561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108693638494899087952947707 163040457742348631929421561)
  ·
    refine ⟨122280343306761473947066171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163040457742348631929421561 122280343306761473947066171)
    ·
      refine ⟨183420514960142210920599257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122280343306761473947066171 183420514960142210920599257)
      ·
        refine ⟨137565386220106658190449443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183420514960142210920599257 137565386220106658190449443)
        ·
          refine ⟨206348079330159987285674165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137565386220106658190449443 206348079330159987285674165)
          ·
            refine ⟨19345132437202498808031953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 206348079330159987285674165 19345132437202498808031953)
            ·
              refine ⟨14508849327901874106023965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19345132437202498808031953 14508849327901874106023965)
              ·
                refine ⟨5440818497963202789758987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14508849327901874106023965 5440818497963202789758987)
                ·
                  refine ⟨8161227746944804184638481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5440818497963202789758987 8161227746944804184638481)
                  ·
                    refine ⟨6120920810208603138478861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8161227746944804184638481 6120920810208603138478861)
                    ·
                      refine ⟨2295345303828226176929573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6120920810208603138478861 2295345303828226176929573)
                      ·
                        rfl

theorem cell23_4470169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_4470169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470169 prefixEnd_4470169 := by exact prefixLift 4470169
  have htrace : WordTrace (prefixWord ++ tailWord_4470169) baseStart_4470169 baseEnd_4470169 := by
    simpa [prefixWord, tailWord_4470169, baseEnd_4470169] using wordTrace_append hprefix tailTrace_4470169
  have hstable : (prefixWord ++ tailWord_4470169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470169).length < 2 ^ (prefixWord ++ tailWord_4470169).sum := by decide
  have hdescent : baseEnd_4470169 < baseStart_4470169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
