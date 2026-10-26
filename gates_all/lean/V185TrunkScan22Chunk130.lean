import V185TrunkScan22Chunk129

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1163516 : List Nat := [2, 2, 2, 1, 4, 2, 2, 2, 2, 3]
def baseStart_1163516 : Nat := 118140960795 + 1163516 * 2 ^ 59
def prefixEnd_1163516 : Nat := 4983230072969 + 3 ^ 40 * 1163516 * 2
def baseEnd_1163516 : Nat := 398295304797849981332729

theorem tailTrace_1163516 : CollatzResearch.WordTrace tailWord_1163516 prefixEnd_1163516 398295304797849981332729 := by
  unfold tailWord_1163516
  simp only [CollatzResearch.WordTrace]
  refine ⟨21218457426393859778791201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28291276568525146371721601 21218457426393859778791201)
  ·
    refine ⟨15913843069795394834093401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21218457426393859778791201 15913843069795394834093401)
    ·
      refine ⟨11935382302346546125570051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15913843069795394834093401 11935382302346546125570051)
      ·
        refine ⟨17903073453519819188355077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11935382302346546125570051 17903073453519819188355077)
        ·
          refine ⟨3356826272534966097816577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17903073453519819188355077 3356826272534966097816577)
          ·
            refine ⟨2517619704401224573362433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3356826272534966097816577 2517619704401224573362433)
            ·
              refine ⟨1888214778300918430021825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2517619704401224573362433 1888214778300918430021825)
              ·
                refine ⟨1416161083725688822516369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1888214778300918430021825 1416161083725688822516369)
                ·
                  refine ⟨1062120812794266616887277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1416161083725688822516369 1062120812794266616887277)
                  ·
                    refine ⟨398295304797849981332729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1062120812794266616887277 398295304797849981332729)
                    ·
                      rfl

theorem cell22_1163516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_1163516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163516 prefixEnd_1163516 := by exact prefixLift 1163516
  have htrace : WordTrace (prefixWord ++ tailWord_1163516) baseStart_1163516 baseEnd_1163516 := by
    simpa [prefixWord, tailWord_1163516, baseEnd_1163516] using wordTrace_append hprefix tailTrace_1163516
  have hstable : (prefixWord ++ tailWord_1163516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163516).length < 2 ^ (prefixWord ++ tailWord_1163516).sum := by decide
  have hdescent : baseEnd_1163516 < baseStart_1163516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163544 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 3, 3]
def baseStart_1163544 : Nat := 118140960795 + 1163544 * 2 ^ 59
def prefixEnd_1163544 : Nat := 4983230072969 + 3 ^ 40 * 1163544 * 2
def baseEnd_1163544 : Nat := 398304889770067241632643

theorem tailTrace_1163544 : CollatzResearch.WordTrace tailWord_1163544 prefixEnd_1163544 398304889770067241632643 := by
  unfold tailWord_1163544
  simp only [CollatzResearch.WordTrace]
  refine ⟨21218968048343140169800843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28291957397790853559734457 21218968048343140169800843)
  ·
    refine ⟨31828452072514710254701265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21218968048343140169800843 31828452072514710254701265)
    ·
      refine ⟨23871339054386032691025949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31828452072514710254701265 23871339054386032691025949)
      ·
        refine ⟨8951752145394762259134731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23871339054386032691025949 8951752145394762259134731)
        ·
          refine ⟨13427628218092143388702097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8951752145394762259134731 13427628218092143388702097)
          ·
            refine ⟨10070721163569107541526573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13427628218092143388702097 10070721163569107541526573)
            ·
              refine ⟨3776520436338415328072465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10070721163569107541526573 3776520436338415328072465)
              ·
                refine ⟨2832390327253811496054349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3776520436338415328072465 2832390327253811496054349)
                ·
                  refine ⟨1062146372720179311020381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2832390327253811496054349 1062146372720179311020381)
                  ·
                    refine ⟨398304889770067241632643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1062146372720179311020381 398304889770067241632643)
                    ·
                      rfl

theorem cell22_1163544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_1163544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163544 prefixEnd_1163544 := by exact prefixLift 1163544
  have htrace : WordTrace (prefixWord ++ tailWord_1163544) baseStart_1163544 baseEnd_1163544 := by
    simpa [prefixWord, tailWord_1163544, baseEnd_1163544] using wordTrace_append hprefix tailTrace_1163544
  have hstable : (prefixWord ++ tailWord_1163544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163544).length < 2 ^ (prefixWord ++ tailWord_1163544).sum := by decide
  have hdescent : baseEnd_1163544 < baseStart_1163544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163587 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 5, 4]
def baseStart_1163587 : Nat := 118140960795 + 1163587 * 2 ^ 59
def prefixEnd_1163587 : Nat := 4983230072969 + 3 ^ 40 * 1163587 * 2
def baseEnd_1163587 : Nat := 398319609548829462807511

theorem tailTrace_1163587 : CollatzResearch.WordTrace tailWord_1163587 prefixEnd_1163587 398319609548829462807511 := by
  unfold tailWord_1163587
  simp only [CollatzResearch.WordTrace]
  refine ⟨42439504435530498683417015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28293002957020332455611343 42439504435530498683417015)
  ·
    refine ⟨63659256653295748025125523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42439504435530498683417015 63659256653295748025125523)
    ·
      refine ⟨95488884979943622037688285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63659256653295748025125523 95488884979943622037688285)
      ·
        refine ⟨35808331867478858264133107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95488884979943622037688285 35808331867478858264133107)
        ·
          refine ⟨53712497801218287396199661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35808331867478858264133107 53712497801218287396199661)
          ·
            refine ⟨20142186675456857773574873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53712497801218287396199661 20142186675456857773574873)
            ·
              refine ⟨15106640006592643330181155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20142186675456857773574873 15106640006592643330181155)
              ·
                refine ⟨22659960009888964995271733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15106640006592643330181155 22659960009888964995271733)
                ·
                  refine ⟨2124371250927090468306725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22659960009888964995271733 2124371250927090468306725)
                  ·
                    refine ⟨398319609548829462807511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2124371250927090468306725 398319609548829462807511)
                    ·
                      rfl

theorem cell22_1163587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 4].length) (baseStart_1163587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163587 prefixEnd_1163587 := by exact prefixLift 1163587
  have htrace : WordTrace (prefixWord ++ tailWord_1163587) baseStart_1163587 baseEnd_1163587 := by
    simpa [prefixWord, tailWord_1163587, baseEnd_1163587] using wordTrace_append hprefix tailTrace_1163587
  have hstable : (prefixWord ++ tailWord_1163587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163587).length < 2 ^ (prefixWord ++ tailWord_1163587).sum := by decide
  have hdescent : baseEnd_1163587 < baseStart_1163587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163612 : List Nat := [2, 2, 4, 3, 1, 2, 1, 3, 1, 3]
def baseStart_1163612 : Nat := 118140960795 + 1163612 * 2 ^ 59
def prefixEnd_1163612 : Nat := 4983230072969 + 3 ^ 40 * 1163612 * 2
def baseEnd_1163612 : Nat := 398328167559737730932435

theorem tailTrace_1163612 : CollatzResearch.WordTrace tailWord_1163612 prefixEnd_1163612 398328167559737730932435 := by
  unfold tailWord_1163612
  simp only [CollatzResearch.WordTrace]
  refine ⟨21220208130219963976538545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28293610840293285302051393 21220208130219963976538545)
  ·
    refine ⟨15915156097664972982403909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21220208130219963976538545 15915156097664972982403909)
    ·
      refine ⟨2984091768312182434200733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15915156097664972982403909 2984091768312182434200733)
      ·
        refine ⟨1119034413117068412825275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2984091768312182434200733 1119034413117068412825275)
        ·
          refine ⟨1678551619675602619237913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119034413117068412825275 1678551619675602619237913)
          ·
            refine ⟨1258913714756701964428435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1678551619675602619237913 1258913714756701964428435)
            ·
              refine ⟨1888370572135052946642653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1258913714756701964428435 1888370572135052946642653)
              ·
                refine ⟨708138964550644854990995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1888370572135052946642653 708138964550644854990995)
                ·
                  refine ⟨1062208446825967282486493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708138964550644854990995 1062208446825967282486493)
                  ·
                    refine ⟨398328167559737730932435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1062208446825967282486493 398328167559737730932435)
                    ·
                      rfl

theorem cell22_1163612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_1163612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163612 prefixEnd_1163612 := by exact prefixLift 1163612
  have htrace : WordTrace (prefixWord ++ tailWord_1163612) baseStart_1163612 baseEnd_1163612 := by
    simpa [prefixWord, tailWord_1163612, baseEnd_1163612] using wordTrace_append hprefix tailTrace_1163612
  have hstable : (prefixWord ++ tailWord_1163612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163612).length < 2 ^ (prefixWord ++ tailWord_1163612).sum := by decide
  have hdescent : baseEnd_1163612 < baseStart_1163612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163681 : List Nat := [1, 2, 3, 5, 2, 9]
def baseStart_1163681 : Nat := 118140960795 + 1163681 * 2 ^ 59
def prefixEnd_1163681 : Nat := 4983230072969 + 3 ^ 40 * 1163681 * 2
def baseEnd_1163681 : Nat := 4917923304565982110583

theorem tailTrace_1163681 : CollatzResearch.WordTrace tailWord_1163681 prefixEnd_1163681 4917923304565982110583 := by
  unfold tailWord_1163681
  simp only [CollatzResearch.WordTrace]
  refine ⟨42442932897189952737338897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28295288598126635158225931 42442932897189952737338897)
  ·
    refine ⟨31832199672892464553004173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42442932897189952737338897 31832199672892464553004173)
    ·
      refine ⟨11937074877334674207376565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31832199672892464553004173 11937074877334674207376565)
      ·
        refine ⟨1119100769750125706941553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11937074877334674207376565 1119100769750125706941553)
        ·
          refine ⟨839325577312594280206165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1119100769750125706941553 839325577312594280206165)
          ·
            refine ⟨4917923304565982110583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 839325577312594280206165 4917923304565982110583)
            ·
              rfl

theorem cell22_1163681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 9].length) (baseStart_1163681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163681 prefixEnd_1163681 := by exact prefixLift 1163681
  have htrace : WordTrace (prefixWord ++ tailWord_1163681) baseStart_1163681 baseEnd_1163681 := by
    simpa [prefixWord, tailWord_1163681, baseEnd_1163681] using wordTrace_append hprefix tailTrace_1163681
  have hstable : (prefixWord ++ tailWord_1163681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163681).length < 2 ^ (prefixWord ++ tailWord_1163681).sum := by decide
  have hdescent : baseEnd_1163681 < baseStart_1163681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163786 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 6, 3]
def baseStart_1163786 : Nat := 118140960795 + 1163786 * 2 ^ 59
def prefixEnd_1163786 : Nat := 4983230072969 + 3 ^ 40 * 1163786 * 2
def baseEnd_1163786 : Nat := 398387731315659277081901

theorem tailTrace_1163786 : CollatzResearch.WordTrace tailWord_1163786 prefixEnd_1163786 398387731315659277081901 := by
  unfold tailWord_1163786
  simp only [CollatzResearch.WordTrace]
  refine ⟨10611690640452388917477803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28297841707873037113274141 10611690640452388917477803)
  ·
    refine ⟨15917535960678583376216705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10611690640452388917477803 15917535960678583376216705)
    ·
      refine ⟨11938151970508937532162529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15917535960678583376216705 11938151970508937532162529)
      ·
        refine ⟨8953613977881703149121897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11938151970508937532162529 8953613977881703149121897)
        ·
          refine ⟨6715210483411277361841423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8953613977881703149121897 6715210483411277361841423)
          ·
            refine ⟨10072815725116916042762135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6715210483411277361841423 10072815725116916042762135)
            ·
              refine ⟨15109223587675374064143203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10072815725116916042762135 15109223587675374064143203)
              ·
                refine ⟨22663835381513061096214805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15109223587675374064143203 22663835381513061096214805)
                ·
                  refine ⟨1062367283508424738885069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22663835381513061096214805 1062367283508424738885069)
                  ·
                    refine ⟨398387731315659277081901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1062367283508424738885069 398387731315659277081901)
                    ·
                      rfl

theorem cell22_1163786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_1163786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163786 prefixEnd_1163786 := by exact prefixLift 1163786
  have htrace : WordTrace (prefixWord ++ tailWord_1163786) baseStart_1163786 baseEnd_1163786 := by
    simpa [prefixWord, tailWord_1163786, baseEnd_1163786] using wordTrace_append hprefix tailTrace_1163786
  have hstable : (prefixWord ++ tailWord_1163786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163786).length < 2 ^ (prefixWord ++ tailWord_1163786).sum := by decide
  have hdescent : baseEnd_1163786 < baseStart_1163786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163788 : List Nat := [2, 2, 1, 2, 4, 1, 3, 3, 4]
def baseStart_1163788 : Nat := 118140960795 + 1163788 * 2 ^ 59
def prefixEnd_1163788 : Nat := 4983230072969 + 3 ^ 40 * 1163788 * 2
def baseEnd_1163788 : Nat := 132796138652177312843965

theorem tailTrace_1163788 : CollatzResearch.WordTrace tailWord_1163788 prefixEnd_1163788 132796138652177312843965 := by
  unfold tailWord_1163788
  simp only [CollatzResearch.WordTrace]
  refine ⟨21223417753901155005742009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28297890338534873340989345 21223417753901155005742009)
  ·
    refine ⟨15917563315425866254306507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21223417753901155005742009 15917563315425866254306507)
    ·
      refine ⟨23876344973138799381459761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15917563315425866254306507 23876344973138799381459761)
      ·
        refine ⟨17907258729854099536094821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23876344973138799381459761 17907258729854099536094821)
        ·
          refine ⟨3357611011847643663017779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17907258729854099536094821 3357611011847643663017779)
          ·
            refine ⟨5036416517771465494526669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3357611011847643663017779 5036416517771465494526669)
            ·
              refine ⟨1888656194164299560447501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5036416517771465494526669 1888656194164299560447501)
              ·
                refine ⟨708246072811612335167813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1888656194164299560447501 708246072811612335167813)
                ·
                  refine ⟨132796138652177312843965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 708246072811612335167813 132796138652177312843965)
                  ·
                    rfl

theorem cell22_1163788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_1163788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163788 prefixEnd_1163788 := by exact prefixLift 1163788
  have htrace : WordTrace (prefixWord ++ tailWord_1163788) baseStart_1163788 baseEnd_1163788 := by
    simpa [prefixWord, tailWord_1163788, baseEnd_1163788] using wordTrace_append hprefix tailTrace_1163788
  have hstable : (prefixWord ++ tailWord_1163788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163788).length < 2 ^ (prefixWord ++ tailWord_1163788).sum := by decide
  have hdescent : baseEnd_1163788 < baseStart_1163788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163805 : List Nat := [1, 4, 2, 2, 1, 3, 3, 2, 4]
def baseStart_1163805 : Nat := 118140960795 + 1163805 * 2 ^ 59
def prefixEnd_1163805 : Nat := 4983230072969 + 3 ^ 40 * 1163805 * 2
def baseEnd_1163805 : Nat := 132798078467983186952281

theorem tailTrace_1163805 : CollatzResearch.WordTrace tailWord_1163805 prefixEnd_1163805 132798078467983186952281 := by
  unfold tailWord_1163805
  simp only [CollatzResearch.WordTrace]
  refine ⟨42447455548740721914852869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28298303699160481276568579 42447455548740721914852869)
  ·
    refine ⟨7958897915388885359034913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42447455548740721914852869 7958897915388885359034913)
    ·
      refine ⟨5969173436541664019276185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7958897915388885359034913 5969173436541664019276185)
      ·
        refine ⟨4476880077406248014457139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5969173436541664019276185 4476880077406248014457139)
        ·
          refine ⟨6715320116109372021685709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4476880077406248014457139 6715320116109372021685709)
          ·
            refine ⟨2518245043541014508132141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6715320116109372021685709 2518245043541014508132141)
            ·
              refine ⟨944341891327880440549553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2518245043541014508132141 944341891327880440549553)
              ·
                refine ⟨708256418495910330412165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 944341891327880440549553 708256418495910330412165)
                ·
                  refine ⟨132798078467983186952281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 708256418495910330412165 132798078467983186952281)
                  ·
                    rfl

theorem cell22_1163805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_1163805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163805 prefixEnd_1163805 := by exact prefixLift 1163805
  have htrace : WordTrace (prefixWord ++ tailWord_1163805) baseStart_1163805 baseEnd_1163805 := by
    simpa [prefixWord, tailWord_1163805, baseEnd_1163805] using wordTrace_append hprefix tailTrace_1163805
  have hstable : (prefixWord ++ tailWord_1163805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163805).length < 2 ^ (prefixWord ++ tailWord_1163805).sum := by decide
  have hdescent : baseEnd_1163805 < baseStart_1163805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163816 : List Nat := [2, 1, 5, 2, 1, 1, 1, 9]
def baseStart_1163816 : Nat := 118140960795 + 1163816 * 2 ^ 59
def prefixEnd_1163816 : Nat := 4983230072969 + 3 ^ 40 * 1163816 * 2
def baseEnd_1163816 : Nat := 44266444547638799870201

theorem tailTrace_1163816 : CollatzResearch.WordTrace tailWord_1163816 prefixEnd_1163816 44266444547638799870201 := by
  unfold tailWord_1163816
  simp only [CollatzResearch.WordTrace]
  refine ⟨21223928375850435396751651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28298571167800580529002201 21223928375850435396751651)
  ·
    refine ⟨31835892563775653095127477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21223928375850435396751651 31835892563775653095127477)
    ·
      refine ⟨2984614927853967477668201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31835892563775653095127477 2984614927853967477668201)
      ·
        refine ⟨2238461195890475608251151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2984614927853967477668201 2238461195890475608251151)
        ·
          refine ⟨3357691793835713412376727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2238461195890475608251151 3357691793835713412376727)
          ·
            refine ⟨5036537690753570118565091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3357691793835713412376727 5036537690753570118565091)
            ·
              refine ⟨7554806536130355177847637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5036537690753570118565091 7554806536130355177847637)
              ·
                refine ⟨44266444547638799870201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7554806536130355177847637 44266444547638799870201)
                ·
                  rfl

theorem cell22_1163816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 9].length) (baseStart_1163816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163816 prefixEnd_1163816 := by exact prefixLift 1163816
  have htrace : WordTrace (prefixWord ++ tailWord_1163816) baseStart_1163816 baseEnd_1163816 := by
    simpa [prefixWord, tailWord_1163816, baseEnd_1163816] using wordTrace_append hprefix tailTrace_1163816
  have hstable : (prefixWord ++ tailWord_1163816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163816).length < 2 ^ (prefixWord ++ tailWord_1163816).sum := by decide
  have hdescent : baseEnd_1163816 < baseStart_1163816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163831 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 5, 3]
def baseStart_1163831 : Nat := 118140960795 + 1163831 * 2 ^ 59
def prefixEnd_1163831 : Nat := 4983230072969 + 3 ^ 40 * 1163831 * 2
def baseEnd_1163831 : Nat := 398403135735294159706763

theorem tailTrace_1163831 : CollatzResearch.WordTrace tailWord_1163831 prefixEnd_1163831 398403135735294159706763 := by
  unfold tailWord_1163831
  simp only [CollatzResearch.WordTrace]
  refine ⟨42448403846646528355299347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28298935897764352236866231 42448403846646528355299347)
  ·
    refine ⟨63672605769969792532949021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42448403846646528355299347 63672605769969792532949021)
    ·
      refine ⟨23877227163738672199855883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63672605769969792532949021 23877227163738672199855883)
      ·
        refine ⟨35815840745608008299783825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23877227163738672199855883 35815840745608008299783825)
        ·
          refine ⟨26861880559206006224837869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35815840745608008299783825 26861880559206006224837869)
          ·
            refine ⟨10073205209702252334314201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26861880559206006224837869 10073205209702252334314201)
            ·
              refine ⟨7554903907276689250735651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10073205209702252334314201 7554903907276689250735651)
              ·
                refine ⟨11332355860915033876103477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7554903907276689250735651 11332355860915033876103477)
                ·
                  refine ⟨1062408361960784425884701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11332355860915033876103477 1062408361960784425884701)
                  ·
                    refine ⟨398403135735294159706763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1062408361960784425884701 398403135735294159706763)
                    ·
                      rfl

theorem cell22_1163831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_1163831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163831 prefixEnd_1163831 := by exact prefixLift 1163831
  have htrace : WordTrace (prefixWord ++ tailWord_1163831) baseStart_1163831 baseEnd_1163831 := by
    simpa [prefixWord, tailWord_1163831, baseEnd_1163831] using wordTrace_append hprefix tailTrace_1163831
  have hstable : (prefixWord ++ tailWord_1163831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163831).length < 2 ^ (prefixWord ++ tailWord_1163831).sum := by decide
  have hdescent : baseEnd_1163831 < baseStart_1163831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163861 : List Nat := [1, 3, 2, 2, 1, 1, 3, 4, 5]
def baseStart_1163861 : Nat := 118140960795 + 1163861 * 2 ^ 59
def prefixEnd_1163861 : Nat := 4983230072969 + 3 ^ 40 * 1163861 * 2
def baseEnd_1163861 : Nat := 132804468449461360485557

theorem tailTrace_1163861 : CollatzResearch.WordTrace tailWord_1163861 prefixEnd_1163861 132804468449461360485557 := by
  unfold tailWord_1163861
  simp only [CollatzResearch.WordTrace]
  refine ⟨42449498036537843478891437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28299665357691895652594291 42449498036537843478891437)
  ·
    refine ⟨15918561763701691304584289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42449498036537843478891437 15918561763701691304584289)
    ·
      refine ⟨11938921322776268478438217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15918561763701691304584289 11938921322776268478438217)
      ·
        refine ⟨8954190992082201358828663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11938921322776268478438217 8954190992082201358828663)
        ·
          refine ⟨13431286488123302038242995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8954190992082201358828663 13431286488123302038242995)
          ·
            refine ⟨20146929732184953057364493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13431286488123302038242995 20146929732184953057364493)
            ·
              refine ⟨7555098649569357396511685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20146929732184953057364493 7555098649569357396511685)
              ·
                refine ⟨1416580996794254511845941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7555098649569357396511685 1416580996794254511845941)
                ·
                  refine ⟨132804468449461360485557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1416580996794254511845941 132804468449461360485557)
                  ·
                    rfl

theorem cell22_1163861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_1163861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163861 prefixEnd_1163861 := by exact prefixLift 1163861
  have htrace : WordTrace (prefixWord ++ tailWord_1163861) baseStart_1163861 baseEnd_1163861 := by
    simpa [prefixWord, tailWord_1163861, baseEnd_1163861] using wordTrace_append hprefix tailTrace_1163861
  have hstable : (prefixWord ++ tailWord_1163861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163861).length < 2 ^ (prefixWord ++ tailWord_1163861).sum := by decide
  have hdescent : baseEnd_1163861 < baseStart_1163861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163876 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_1163876 : Nat := 118140960795 + 1163876 * 2 ^ 59
def prefixEnd_1163876 : Nat := 4983230072969 + 3 ^ 40 * 1163876 * 2
def baseEnd_1163876 : Nat := 398418540154929042331625

theorem tailTrace_1163876 : CollatzResearch.WordTrace tailWord_1163876 prefixEnd_1163876 398418540154929042331625 := by
  unfold tailWord_1163876
  simp only [CollatzResearch.WordTrace]
  refine ⟨21225022565741750520343741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28300030087655667360458321 21225022565741750520343741)
  ·
    refine ⟨7959383462153156445128903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21225022565741750520343741 7959383462153156445128903)
    ·
      refine ⟨11939075193229734667693355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7959383462153156445128903 11939075193229734667693355)
      ·
        refine ⟨17908612789844602001540033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11939075193229734667693355 17908612789844602001540033)
        ·
          refine ⟨13431459592383451501155025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17908612789844602001540033 13431459592383451501155025)
          ·
            refine ⟨10073594694287588625866269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13431459592383451501155025 10073594694287588625866269)
            ·
              refine ⟨3777598010357845734699851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10073594694287588625866269 3777598010357845734699851)
              ·
                refine ⟨5666397015536768602049777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3777598010357845734699851 5666397015536768602049777)
                ·
                  refine ⟨4249797761652576451537333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5666397015536768602049777 4249797761652576451537333)
                  ·
                    refine ⟨398418540154929042331625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4249797761652576451537333 398418540154929042331625)
                    ·
                      rfl

theorem cell22_1163876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_1163876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163876 prefixEnd_1163876 := by exact prefixLift 1163876
  have htrace : WordTrace (prefixWord ++ tailWord_1163876) baseStart_1163876 baseEnd_1163876 := by
    simpa [prefixWord, tailWord_1163876, baseEnd_1163876] using wordTrace_append hprefix tailTrace_1163876
  have hstable : (prefixWord ++ tailWord_1163876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163876).length < 2 ^ (prefixWord ++ tailWord_1163876).sum := by decide
  have hdescent : baseEnd_1163876 < baseStart_1163876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163951 : List Nat := [1, 1, 2, 1, 2, 6, 1, 8]
def baseStart_1163951 : Nat := 118140960795 + 1163951 * 2 ^ 59
def prefixEnd_1163951 : Nat := 4983230072969 + 3 ^ 40 * 1163951 * 2
def baseEnd_1163951 : Nat := 44271579354183760745155

theorem tailTrace_1163951 : CollatzResearch.WordTrace tailWord_1163951 prefixEnd_1163951 44271579354183760745155 := by
  unfold tailWord_1163951
  simp only [CollatzResearch.WordTrace]
  refine ⟨42452780606211788849667707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28301853737474525899778471 42452780606211788849667707)
  ·
    refine ⟨63679170909317683274501561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42452780606211788849667707 63679170909317683274501561)
    ·
      refine ⟨47759378181988262455876171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63679170909317683274501561 47759378181988262455876171)
      ·
        refine ⟨71639067272982393683814257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47759378181988262455876171 71639067272982393683814257)
        ·
          refine ⟨53729300454736795262860693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71639067272982393683814257 53729300454736795262860693)
          ·
            refine ⟨2518560958815787277946595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53729300454736795262860693 2518560958815787277946595)
            ·
              refine ⟨3777841438223680916919893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2518560958815787277946595 3777841438223680916919893)
              ·
                refine ⟨44271579354183760745155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3777841438223680916919893 44271579354183760745155)
                ·
                  rfl

theorem cell22_1163951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 8].length) (baseStart_1163951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163951 prefixEnd_1163951 := by exact prefixLift 1163951
  have htrace : WordTrace (prefixWord ++ tailWord_1163951) baseStart_1163951 baseEnd_1163951 := by
    simpa [prefixWord, tailWord_1163951, baseEnd_1163951] using wordTrace_append hprefix tailTrace_1163951
  have hstable : (prefixWord ++ tailWord_1163951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163951).length < 2 ^ (prefixWord ++ tailWord_1163951).sum := by decide
  have hdescent : baseEnd_1163951 < baseStart_1163951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163957 : List Nat := [1, 3, 3, 3, 1, 3, 1, 3, 4]
def baseStart_1163957 : Nat := 118140960795 + 1163957 * 2 ^ 59
def prefixEnd_1163957 : Nat := 4983230072969 + 3 ^ 40 * 1163957 * 2
def baseEnd_1163957 : Nat := 132815422703423943685459

theorem tailTrace_1163957 : CollatzResearch.WordTrace tailWord_1163957 prefixEnd_1163957 132815422703423943685459 := by
  unfold tailWord_1163957
  simp only [CollatzResearch.WordTrace]
  refine ⟨42452999444190051874386125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28301999629460034582924083 42452999444190051874386125)
  ·
    refine ⟨15919874791571269452894797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42452999444190051874386125 15919874791571269452894797)
    ·
      refine ⟨5969953046839226044835549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15919874791571269452894797 5969953046839226044835549)
      ·
        refine ⟨2238732392564709766813331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5969953046839226044835549 2238732392564709766813331)
        ·
          refine ⟨3358098588847064650219997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2238732392564709766813331 3358098588847064650219997)
          ·
            refine ⟨1259286970817649243832499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3358098588847064650219997 1259286970817649243832499)
            ·
              refine ⟨1888930456226473865748749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259286970817649243832499 1888930456226473865748749)
              ·
                refine ⟨708348921084927699655781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1888930456226473865748749 708348921084927699655781)
                ·
                  refine ⟨132815422703423943685459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 708348921084927699655781 132815422703423943685459)
                  ·
                    rfl

theorem cell22_1163957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_1163957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163957 prefixEnd_1163957 := by exact prefixLift 1163957
  have htrace : WordTrace (prefixWord ++ tailWord_1163957) baseStart_1163957 baseEnd_1163957 := by
    simpa [prefixWord, tailWord_1163957, baseEnd_1163957] using wordTrace_append hprefix tailTrace_1163957
  have hstable : (prefixWord ++ tailWord_1163957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163957).length < 2 ^ (prefixWord ++ tailWord_1163957).sum := by decide
  have hdescent : baseEnd_1163957 < baseStart_1163957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1163974 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_1163974 : Nat := 118140960795 + 1163974 * 2 ^ 59
def prefixEnd_1163974 : Nat := 4983230072969 + 3 ^ 40 * 1163974 * 2
def baseEnd_1163974 : Nat := 132817362519229817793775

theorem tailTrace_1163974 : CollatzResearch.WordTrace tailWord_1163974 prefixEnd_1163974 132817362519229817793775 := by
  unfold tailWord_1163974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1326675608910264493054843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28302412990085642518503317 1326675608910264493054843)
  ·
    refine ⟨1990013413365396739582265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1326675608910264493054843 1990013413365396739582265)
    ·
      refine ⟨1492510060024047554686699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1990013413365396739582265 1492510060024047554686699)
      ·
        refine ⟨2238765090036071332030049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492510060024047554686699 2238765090036071332030049)
        ·
          refine ⟨1679073817527053499022537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2238765090036071332030049 1679073817527053499022537)
          ·
            refine ⟨1259305363145290124266903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1679073817527053499022537 1259305363145290124266903)
            ·
              refine ⟨1888958044717935186400355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259305363145290124266903 1888958044717935186400355)
              ·
                refine ⟨2833437067076902779600533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1888958044717935186400355 2833437067076902779600533)
                ·
                  refine ⟨132817362519229817793775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2833437067076902779600533 132817362519229817793775)
                  ·
                    rfl

theorem cell22_1163974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_1163974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1163974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1163974 prefixEnd_1163974 := by exact prefixLift 1163974
  have htrace : WordTrace (prefixWord ++ tailWord_1163974) baseStart_1163974 baseEnd_1163974 := by
    simpa [prefixWord, tailWord_1163974, baseEnd_1163974] using wordTrace_append hprefix tailTrace_1163974
  have hstable : (prefixWord ++ tailWord_1163974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1163974).length < 2 ^ (prefixWord ++ tailWord_1163974).sum := by decide
  have hdescent : baseEnd_1163974 < baseStart_1163974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1163974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164011 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 4, 5]
def baseStart_1164011 : Nat := 118140960795 + 1164011 * 2 ^ 59
def prefixEnd_1164011 : Nat := 4983230072969 + 3 ^ 40 * 1164011 * 2
def baseEnd_1164011 : Nat := 398464753413833690206211

theorem tailTrace_1164011 : CollatzResearch.WordTrace tailWord_1164011 prefixEnd_1164011 398464753413833690206211 := by
  unfold tailWord_1164011
  simp only [CollatzResearch.WordTrace]
  refine ⟨42454968985994419096851887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28303312657329612731234591 42454968985994419096851887)
  ·
    refine ⟨63682453478991628645277831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42454968985994419096851887 63682453478991628645277831)
    ·
      refine ⟨95523680218487442967916747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63682453478991628645277831 95523680218487442967916747)
      ·
        refine ⟨143285520327731164451875121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95523680218487442967916747 143285520327731164451875121)
        ·
          refine ⟨107464140245798373338906341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143285520327731164451875121 107464140245798373338906341)
          ·
            refine ⟨20149526296087195001044939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107464140245798373338906341 20149526296087195001044939)
            ·
              refine ⟨30224289444130792501567409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20149526296087195001044939 30224289444130792501567409)
              ·
                refine ⟨22668217083098094376175557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30224289444130792501567409 22668217083098094376175557)
                ·
                  refine ⟨4250290703080892695532917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22668217083098094376175557 4250290703080892695532917)
                  ·
                    refine ⟨398464753413833690206211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4250290703080892695532917 398464753413833690206211)
                    ·
                      rfl

theorem cell22_1164011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 5].length) (baseStart_1164011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164011 prefixEnd_1164011 := by exact prefixLift 1164011
  have htrace : WordTrace (prefixWord ++ tailWord_1164011) baseStart_1164011 baseEnd_1164011 := by
    simpa [prefixWord, tailWord_1164011, baseEnd_1164011] using wordTrace_append hprefix tailTrace_1164011
  have hstable : (prefixWord ++ tailWord_1164011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164011).length < 2 ^ (prefixWord ++ tailWord_1164011).sum := by decide
  have hdescent : baseEnd_1164011 < baseStart_1164011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164030 : List Nat := [4, 2, 2, 1, 2, 1, 1, 4, 5]
def baseStart_1164030 : Nat := 118140960795 + 1164030 * 2 ^ 59
def prefixEnd_1164030 : Nat := 4983230072969 + 3 ^ 40 * 1164030 * 2
def baseEnd_1164030 : Nat := 132823752500707991327051

theorem tailTrace_1164030 : CollatzResearch.WordTrace tailWord_1164030 prefixEnd_1164030 132823752500707991327051 := by
  unfold tailWord_1164030
  simp only [CollatzResearch.WordTrace]
  refine ⟨5306957746615698167724193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28303774648617056894529029 5306957746615698167724193)
  ·
    refine ⟨3980218309961773625793145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5306957746615698167724193 3980218309961773625793145)
    ·
      refine ⟨2985163732471330219344859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3980218309961773625793145 2985163732471330219344859)
      ·
        refine ⟨4477745598706995329017289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2985163732471330219344859 4477745598706995329017289)
        ·
          refine ⟨3358309199030246496762967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4477745598706995329017289 3358309199030246496762967)
          ·
            refine ⟨5037463798545369745144451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3358309199030246496762967 5037463798545369745144451)
            ·
              refine ⟨7556195697818054617716677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5037463798545369745144451 7556195697818054617716677)
              ·
                refine ⟨1416786693340885240821877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7556195697818054617716677 1416786693340885240821877)
                ·
                  refine ⟨132823752500707991327051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1416786693340885240821877 132823752500707991327051)
                  ·
                    rfl

theorem cell22_1164030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_1164030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164030 prefixEnd_1164030 := by exact prefixLift 1164030
  have htrace : WordTrace (prefixWord ++ tailWord_1164030) baseStart_1164030 baseEnd_1164030 := by
    simpa [prefixWord, tailWord_1164030, baseEnd_1164030] using wordTrace_append hprefix tailTrace_1164030
  have hstable : (prefixWord ++ tailWord_1164030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164030).length < 2 ^ (prefixWord ++ tailWord_1164030).sum := by decide
  have hdescent : baseEnd_1164030 < baseStart_1164030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164034 : List Nat := [3, 4, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_1164034 : Nat := 118140960795 + 1164034 * 2 ^ 59
def prefixEnd_1164034 : Nat := 4983230072969 + 3 ^ 40 * 1164034 * 2
def baseEnd_1164034 : Nat := 398472626783869296881141

theorem tailTrace_1164034 : CollatzResearch.WordTrace tailWord_1164034 prefixEnd_1164034 398472626783869296881141 := by
  unfold tailWord_1164034
  simp only [CollatzResearch.WordTrace]
  refine ⟨10613951966227773506234789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28303871909940729349959437 10613951966227773506234789)
  ·
    refine ⟨1990115993667707532419023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10613951966227773506234789 1990115993667707532419023)
    ·
      refine ⟨2985173990501561298628535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1990115993667707532419023 2985173990501561298628535)
      ·
        refine ⟨4477760985752341947942803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2985173990501561298628535 4477760985752341947942803)
        ·
          refine ⟨6716641478628512921914205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4477760985752341947942803 6716641478628512921914205)
          ·
            refine ⟨2518740554485692345717827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6716641478628512921914205 2518740554485692345717827)
            ·
              refine ⟨3778110831728538518576741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2518740554485692345717827 3778110831728538518576741)
              ·
                refine ⟨708395780949100972233139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3778110831728538518576741 708395780949100972233139)
                ·
                  refine ⟨1062593671423651458349709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708395780949100972233139 1062593671423651458349709)
                  ·
                    refine ⟨398472626783869296881141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1062593671423651458349709 398472626783869296881141)
                    ·
                      rfl

theorem cell22_1164034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_1164034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164034 prefixEnd_1164034 := by exact prefixLift 1164034
  have htrace : WordTrace (prefixWord ++ tailWord_1164034) baseStart_1164034 baseEnd_1164034 := by
    simpa [prefixWord, tailWord_1164034, baseEnd_1164034] using wordTrace_append hprefix tailTrace_1164034
  have hstable : (prefixWord ++ tailWord_1164034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164034).length < 2 ^ (prefixWord ++ tailWord_1164034).sum := by decide
  have hdescent : baseEnd_1164034 < baseStart_1164034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164058 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 6]
def baseStart_1164058 : Nat := 118140960795 + 1164058 * 2 ^ 59
def prefixEnd_1164058 : Nat := 4983230072969 + 3 ^ 40 * 1164058 * 2
def baseEnd_1164058 : Nat := 132826947491447078093689

theorem tailTrace_1164058 : CollatzResearch.WordTrace tailWord_1164058 prefixEnd_1164058 132826947491447078093689 := by
  unfold tailWord_1164058
  simp only [CollatzResearch.WordTrace]
  refine ⟨10614170804206036530953207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28304455477882764082541885 10614170804206036530953207)
  ·
    refine ⟨15921256206309054796429811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10614170804206036530953207 15921256206309054796429811)
    ·
      refine ⟨23881884309463582194644717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15921256206309054796429811 23881884309463582194644717)
      ·
        refine ⟨8955706616048843322991769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23881884309463582194644717 8955706616048843322991769)
        ·
          refine ⟨6716779962036632492243827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8955706616048843322991769 6716779962036632492243827)
          ·
            refine ⟨10075169943054948738365741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6716779962036632492243827 10075169943054948738365741)
            ·
              refine ⟨3778188728645605776887153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10075169943054948738365741 3778188728645605776887153)
              ·
                refine ⟨2833641546484204332665365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3778188728645605776887153 2833641546484204332665365)
                ·
                  refine ⟨132826947491447078093689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2833641546484204332665365 132826947491447078093689)
                  ·
                    rfl

theorem cell22_1164058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_1164058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164058 prefixEnd_1164058 := by exact prefixLift 1164058
  have htrace : WordTrace (prefixWord ++ tailWord_1164058) baseStart_1164058 baseEnd_1164058 := by
    simpa [prefixWord, tailWord_1164058, baseEnd_1164058] using wordTrace_append hprefix tailTrace_1164058
  have hstable : (prefixWord ++ tailWord_1164058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164058).length < 2 ^ (prefixWord ++ tailWord_1164058).sum := by decide
  have hdescent : baseEnd_1164058 < baseStart_1164058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164073 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 6, 3]
def baseStart_1164073 : Nat := 118140960795 + 1164073 * 2 ^ 59
def prefixEnd_1164073 : Nat := 4983230072969 + 3 ^ 40 * 1164073 * 2
def baseEnd_1164073 : Nat := 398485977280886195156021

theorem tailTrace_1164073 : CollatzResearch.WordTrace tailWord_1164073 prefixEnd_1164073 398485977280886195156021 := by
  unfold tailWord_1164073
  simp only [CollatzResearch.WordTrace]
  refine ⟨42457230311769803685608873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28304820207846535790405915 42457230311769803685608873)
  ·
    refine ⟨31842922733827352764206655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42457230311769803685608873 31842922733827352764206655)
    ·
      refine ⟨47764384100741029146309983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31842922733827352764206655 47764384100741029146309983)
      ·
        refine ⟨71646576151111543719464975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47764384100741029146309983 71646576151111543719464975)
        ·
          refine ⟨107469864226667315579197463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71646576151111543719464975 107469864226667315579197463)
          ·
            refine ⟨161204796340000973368796195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107469864226667315579197463 161204796340000973368796195)
            ·
              refine ⟨241807194510001460053194293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161204796340000973368796195 241807194510001460053194293)
              ·
                refine ⟨22669424485312636879986965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 241807194510001460053194293 22669424485312636879986965)
                ·
                  refine ⟨1062629272749029853749389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22669424485312636879986965 1062629272749029853749389)
                  ·
                    refine ⟨398485977280886195156021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1062629272749029853749389 398485977280886195156021)
                    ·
                      rfl

theorem cell22_1164073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 3].length) (baseStart_1164073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164073 prefixEnd_1164073 := by exact prefixLift 1164073
  have htrace : WordTrace (prefixWord ++ tailWord_1164073) baseStart_1164073 baseEnd_1164073 := by
    simpa [prefixWord, tailWord_1164073, baseEnd_1164073] using wordTrace_append hprefix tailTrace_1164073
  have hstable : (prefixWord ++ tailWord_1164073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164073).length < 2 ^ (prefixWord ++ tailWord_1164073).sum := by decide
  have hdescent : baseEnd_1164073 < baseStart_1164073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164088 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 4, 4]
def baseStart_1164088 : Nat := 118140960795 + 1164088 * 2 ^ 59
def prefixEnd_1164088 : Nat := 4983230072969 + 3 ^ 40 * 1164088 * 2
def baseEnd_1164088 : Nat := 398491112087431156030975

theorem tailTrace_1164088 : CollatzResearch.WordTrace tailWord_1164088 prefixEnd_1164088 398491112087431156030975 := by
  unfold tailWord_1164088
  simp only [CollatzResearch.WordTrace]
  refine ⟨21228888703357730623702459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28305184937810307498269945 21228888703357730623702459)
  ·
    refine ⟨31843333055036595935553689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21228888703357730623702459 31843333055036595935553689)
    ·
      refine ⟨23882499791277446951665267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31843333055036595935553689 23882499791277446951665267)
      ·
        refine ⟨35823749686916170427497901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23882499791277446951665267 35823749686916170427497901)
        ·
          refine ⟨13433906132593563910311713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35823749686916170427497901 13433906132593563910311713)
          ·
            refine ⟨10075429599445172932733785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13433906132593563910311713 10075429599445172932733785)
            ·
              refine ⟨7556572199583879699550339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10075429599445172932733785 7556572199583879699550339)
              ·
                refine ⟨11334858299375819549325509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7556572199583879699550339 11334858299375819549325509)
                ·
                  refine ⟨2125285931132966165498533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11334858299375819549325509 2125285931132966165498533)
                  ·
                    refine ⟨398491112087431156030975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2125285931132966165498533 398491112087431156030975)
                    ·
                      rfl

theorem cell22_1164088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_1164088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164088 prefixEnd_1164088 := by exact prefixLift 1164088
  have htrace : WordTrace (prefixWord ++ tailWord_1164088) baseStart_1164088 baseEnd_1164088 := by
    simpa [prefixWord, tailWord_1164088, baseEnd_1164088] using wordTrace_append hprefix tailTrace_1164088
  have hstable : (prefixWord ++ tailWord_1164088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164088).length < 2 ^ (prefixWord ++ tailWord_1164088).sum := by decide
  have hdescent : baseEnd_1164088 < baseStart_1164088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164158 : List Nat := [4, 2, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1164158 : Nat := 118140960795 + 1164158 * 2 ^ 59
def prefixEnd_1164158 : Nat := 4983230072969 + 3 ^ 40 * 1164158 * 2
def baseEnd_1164158 : Nat := 398515074517974306780761

theorem tailTrace_1164158 : CollatzResearch.WordTrace tailWord_1164158 prefixEnd_1164158 398515074517974306780761 := by
  unfold tailWord_1164158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5307541314557732900306641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28306887010974575468302085 5307541314557732900306641)
  ·
    refine ⟨3980655985918299675229981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5307541314557732900306641 3980655985918299675229981)
    ·
      refine ⟨1492745994719362378211243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3980655985918299675229981 1492745994719362378211243)
      ·
        refine ⟨2239118992079043567316865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492745994719362378211243 2239118992079043567316865)
        ·
          refine ⟨1679339244059282675487649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2239118992079043567316865 1679339244059282675487649)
          ·
            refine ⟨1259504433044462006615737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1679339244059282675487649 1259504433044462006615737)
            ·
              refine ⟨944628324783346504961803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1259504433044462006615737 944628324783346504961803)
              ·
                refine ⟨1416942487175019757442705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944628324783346504961803 1416942487175019757442705)
                ·
                  refine ⟨1062706865381264818082029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1416942487175019757442705 1062706865381264818082029)
                  ·
                    refine ⟨398515074517974306780761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1062706865381264818082029 398515074517974306780761)
                    ·
                      rfl

theorem cell22_1164158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1164158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164158 prefixEnd_1164158 := by exact prefixLift 1164158
  have htrace : WordTrace (prefixWord ++ tailWord_1164158) baseStart_1164158 baseEnd_1164158 := by
    simpa [prefixWord, tailWord_1164158, baseEnd_1164158] using wordTrace_append hprefix tailTrace_1164158
  have hstable : (prefixWord ++ tailWord_1164158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164158).length < 2 ^ (prefixWord ++ tailWord_1164158).sum := by decide
  have hdescent : baseEnd_1164158 < baseStart_1164158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164163 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 1, 7]
def baseStart_1164163 : Nat := 118140960795 + 1164163 * 2 ^ 59
def prefixEnd_1164163 : Nat := 4983230072969 + 3 ^ 40 * 1164163 * 2
def baseEnd_1164163 : Nat := 398516786120155960405745

theorem tailTrace_1164163 : CollatzResearch.WordTrace tailWord_1164163 prefixEnd_1164163 398516786120155960405745 := by
  unfold tailWord_1164163
  simp only [CollatzResearch.WordTrace]
  refine ⟨42460512881443749056385143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28307008587629166037590095 42460512881443749056385143)
  ·
    refine ⟨63690769322165623584577715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42460512881443749056385143 63690769322165623584577715)
    ·
      refine ⟨95536153983248435376866573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63690769322165623584577715 95536153983248435376866573)
      ·
        refine ⟨35826057743718163266324965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95536153983248435376866573 35826057743718163266324965)
        ·
          refine ⟨6717385826947155612435931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35826057743718163266324965 6717385826947155612435931)
          ·
            refine ⟨10076078740420733418653897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6717385826947155612435931 10076078740420733418653897)
            ·
              refine ⟨7557059055315550063990423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10076078740420733418653897 7557059055315550063990423)
              ·
                refine ⟨11335588582973325095985635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7557059055315550063990423 11335588582973325095985635)
                ·
                  refine ⟨17003382874459987643978453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11335588582973325095985635 17003382874459987643978453)
                  ·
                    refine ⟨398516786120155960405745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17003382874459987643978453 398516786120155960405745)
                    ·
                      rfl

theorem cell22_1164163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 7].length) (baseStart_1164163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164163 prefixEnd_1164163 := by exact prefixLift 1164163
  have htrace : WordTrace (prefixWord ++ tailWord_1164163) baseStart_1164163 baseEnd_1164163 := by
    simpa [prefixWord, tailWord_1164163, baseEnd_1164163] using wordTrace_append hprefix tailTrace_1164163
  have hstable : (prefixWord ++ tailWord_1164163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164163).length < 2 ^ (prefixWord ++ tailWord_1164163).sum := by decide
  have hdescent : baseEnd_1164163 < baseStart_1164163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164165 : List Nat := [1, 3, 1, 1, 3, 4, 1, 3, 5]
def baseStart_1164165 : Nat := 118140960795 + 1164165 * 2 ^ 59
def prefixEnd_1164165 : Nat := 4983230072969 + 3 ^ 40 * 1164165 * 2
def baseEnd_1164165 : Nat := 132839156920342873951913

theorem tailTrace_1164165 : CollatzResearch.WordTrace tailWord_1164165 prefixEnd_1164165 132839156920342873951913 := by
  unfold tailWord_1164165
  simp only [CollatzResearch.WordTrace]
  refine ⟨42460585827436503397957949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28307057218291002265305299 42460585827436503397957949)
  ·
    refine ⟨15922719685288688774234231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42460585827436503397957949 15922719685288688774234231)
    ·
      refine ⟨23884079527933033161351347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15922719685288688774234231 23884079527933033161351347)
      ·
        refine ⟨35826119291899549742027021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23884079527933033161351347 35826119291899549742027021)
        ·
          refine ⟨13434794734462331153260133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35826119291899549742027021 13434794734462331153260133)
          ·
            refine ⟨2519024012711687091236275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13434794734462331153260133 2519024012711687091236275)
            ·
              refine ⟨3778536019067530636854413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2519024012711687091236275 3778536019067530636854413)
              ·
                refine ⟨1416951007150323988820405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3778536019067530636854413 1416951007150323988820405)
                ·
                  refine ⟨132839156920342873951913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1416951007150323988820405 132839156920342873951913)
                  ·
                    rfl

theorem cell22_1164165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_1164165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164165 prefixEnd_1164165 := by exact prefixLift 1164165
  have htrace : WordTrace (prefixWord ++ tailWord_1164165) baseStart_1164165 baseEnd_1164165 := by
    simpa [prefixWord, tailWord_1164165, baseEnd_1164165] using wordTrace_append hprefix tailTrace_1164165
  have hstable : (prefixWord ++ tailWord_1164165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164165).length < 2 ^ (prefixWord ++ tailWord_1164165).sum := by decide
  have hdescent : baseEnd_1164165 < baseStart_1164165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164195 : List Nat := [1, 1, 1, 4, 1, 2, 2, 5, 1, 4]
def baseStart_1164195 : Nat := 118140960795 + 1164195 * 2 ^ 59
def prefixEnd_1164195 : Nat := 4983230072969 + 3 ^ 40 * 1164195 * 2
def baseEnd_1164195 : Nat := 398527740374118543605647

theorem tailTrace_1164195 : CollatzResearch.WordTrace tailWord_1164195 prefixEnd_1164195 398527740374118543605647 := by
  unfold tailWord_1164195
  simp only [CollatzResearch.WordTrace]
  refine ⟨42461680017327818521550039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28307786678218545681033359 42461680017327818521550039)
  ·
    refine ⟨63692520025991727782325059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42461680017327818521550039 63692520025991727782325059)
    ·
      refine ⟨95538780038987591673487589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63692520025991727782325059 95538780038987591673487589)
      ·
        refine ⟨17913521257310173438778923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95538780038987591673487589 17913521257310173438778923)
        ·
          refine ⟨26870281885965260158168385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17913521257310173438778923 26870281885965260158168385)
          ·
            refine ⟨20152711414473945118626289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26870281885965260158168385 20152711414473945118626289)
            ·
              refine ⟨15114533560855458838969717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20152711414473945118626289 15114533560855458838969717)
              ·
                refine ⟨1416987521330199266153411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15114533560855458838969717 1416987521330199266153411)
                ·
                  refine ⟨2125481281995298899230117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1416987521330199266153411 2125481281995298899230117)
                  ·
                    refine ⟨398527740374118543605647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2125481281995298899230117 398527740374118543605647)
                    ·
                      rfl

theorem cell22_1164195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 4].length) (baseStart_1164195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164195 prefixEnd_1164195 := by exact prefixLift 1164195
  have htrace : WordTrace (prefixWord ++ tailWord_1164195) baseStart_1164195 baseEnd_1164195 := by
    simpa [prefixWord, tailWord_1164195, baseEnd_1164195] using wordTrace_append hprefix tailTrace_1164195
  have hstable : (prefixWord ++ tailWord_1164195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164195).length < 2 ^ (prefixWord ++ tailWord_1164195).sum := by decide
  have hdescent : baseEnd_1164195 < baseStart_1164195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164242 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_1164242 : Nat := 118140960795 + 1164242 * 2 ^ 59
def prefixEnd_1164242 : Nat := 4983230072969 + 3 ^ 40 * 1164242 * 2
def baseEnd_1164242 : Nat := 398543829434626087680503

theorem tailTrace_1164242 : CollatzResearch.WordTrace tailWord_1164242 prefixEnd_1164242 398543829434626087680503 := by
  unfold tailWord_1164242
  simp only [CollatzResearch.WordTrace]
  refine ⟨10615848562039386387127745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28308929498771697032340653 10615848562039386387127745)
  ·
    refine ⟨7961886421529539790345809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10615848562039386387127745 7961886421529539790345809)
    ·
      refine ⟨5971414816147154842759357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7961886421529539790345809 5971414816147154842759357)
      ·
        refine ⟨2239280556055183066034759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5971414816147154842759357 2239280556055183066034759)
        ·
          refine ⟨3358920834082774599052139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2239280556055183066034759 3358920834082774599052139)
          ·
            refine ⟨5038381251124161898578209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3358920834082774599052139 5038381251124161898578209)
            ·
              refine ⟨3778785938343121423933657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5038381251124161898578209 3778785938343121423933657)
              ·
                refine ⟨2834089453757341067950243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3778785938343121423933657 2834089453757341067950243)
                ·
                  refine ⟨4251134180636011601925365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834089453757341067950243 4251134180636011601925365)
                  ·
                    refine ⟨398543829434626087680503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4251134180636011601925365 398543829434626087680503)
                    ·
                      rfl

theorem cell22_1164242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_1164242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164242 prefixEnd_1164242 := by exact prefixLift 1164242
  have htrace : WordTrace (prefixWord ++ tailWord_1164242) baseStart_1164242 baseEnd_1164242 := by
    simpa [prefixWord, tailWord_1164242, baseEnd_1164242] using wordTrace_append hprefix tailTrace_1164242
  have hstable : (prefixWord ++ tailWord_1164242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164242).length < 2 ^ (prefixWord ++ tailWord_1164242).sum := by decide
  have hdescent : baseEnd_1164242 < baseStart_1164242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164244 : List Nat := [2, 4, 1, 2, 1, 3, 2, 3, 4]
def baseStart_1164244 : Nat := 118140960795 + 1164244 * 2 ^ 59
def prefixEnd_1164244 : Nat := 4983230072969 + 3 ^ 40 * 1164244 * 2
def baseEnd_1164244 : Nat := 132848171358499583043499

theorem tailTrace_1164244 : CollatzResearch.WordTrace tailWord_1164244 prefixEnd_1164244 132848171358499583043499 := by
  unfold tailWord_1164244
  simp only [CollatzResearch.WordTrace]
  refine ⟨21231733597075149945041893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28308978129433533260055857 21231733597075149945041893)
  ·
    refine ⟨3980950049451590614695355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21231733597075149945041893 3980950049451590614695355)
    ·
      refine ⟨5971425074177385922043033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3980950049451590614695355 5971425074177385922043033)
      ·
        refine ⟨4478568805633039441532275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5971425074177385922043033 4478568805633039441532275)
        ·
          refine ⟨6717853208449559162298413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4478568805633039441532275 6717853208449559162298413)
          ·
            refine ⟨2519194953168584685861905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6717853208449559162298413 2519194953168584685861905)
            ·
              refine ⟨1889396214876438514396429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2519194953168584685861905 1889396214876438514396429)
              ·
                refine ⟨708523580578664442898661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1889396214876438514396429 708523580578664442898661)
                ·
                  refine ⟨132848171358499583043499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 708523580578664442898661 132848171358499583043499)
                  ·
                    rfl

theorem cell22_1164244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_1164244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164244 prefixEnd_1164244 := by exact prefixLift 1164244
  have htrace : WordTrace (prefixWord ++ tailWord_1164244) baseStart_1164244 baseEnd_1164244 := by
    simpa [prefixWord, tailWord_1164244, baseEnd_1164244] using wordTrace_append hprefix tailTrace_1164244
  have hstable : (prefixWord ++ tailWord_1164244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164244).length < 2 ^ (prefixWord ++ tailWord_1164244).sum := by decide
  have hdescent : baseEnd_1164244 < baseStart_1164244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164246 : List Nat := [5, 2, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_1164246 : Nat := 118140960795 + 1164246 * 2 ^ 59
def prefixEnd_1164246 : Nat := 4983230072969 + 3 ^ 40 * 1164246 * 2
def baseEnd_1164246 : Nat := 398545198716371410580491

theorem tailTrace_1164246 : CollatzResearch.WordTrace tailWord_1164246 prefixEnd_1164246 398545198716371410580491 := by
  unfold tailWord_1164246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2653971258758940889478537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28309026760095369487771061 2653971258758940889478537)
  ·
    refine ⟨1990478444069205667108903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2653971258758940889478537 1990478444069205667108903)
    ·
      refine ⟨2985717666103808500663355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1990478444069205667108903 2985717666103808500663355)
      ·
        refine ⟨4478576499155712750995033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2985717666103808500663355 4478576499155712750995033)
        ·
          refine ⟨3358932374366784563246275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4478576499155712750995033 3358932374366784563246275)
          ·
            refine ⟨5038398561550176844869413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3358932374366784563246275 5038398561550176844869413)
            ·
              refine ⟨944699730290658158413015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5038398561550176844869413 944699730290658158413015)
              ·
                refine ⟨1417049595435987237619523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944699730290658158413015 1417049595435987237619523)
                ·
                  refine ⟨2125574393153980856429285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417049595435987237619523 2125574393153980856429285)
                  ·
                    refine ⟨398545198716371410580491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2125574393153980856429285 398545198716371410580491)
                    ·
                      rfl

theorem cell22_1164246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_1164246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164246 prefixEnd_1164246 := by exact prefixLift 1164246
  have htrace : WordTrace (prefixWord ++ tailWord_1164246) baseStart_1164246 baseEnd_1164246 := by
    simpa [prefixWord, tailWord_1164246, baseEnd_1164246] using wordTrace_append hprefix tailTrace_1164246
  have hstable : (prefixWord ++ tailWord_1164246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164246).length < 2 ^ (prefixWord ++ tailWord_1164246).sum := by decide
  have hdescent : baseEnd_1164246 < baseStart_1164246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164255 : List Nat := [1, 1, 2, 3, 5, 1, 9]
def baseStart_1164255 : Nat := 118140960795 + 1164255 * 2 ^ 59
def prefixEnd_1164255 : Nat := 4983230072969 + 3 ^ 40 * 1164255 * 2
def baseEnd_1164255 : Nat := 14761047392603643966869

theorem tailTrace_1164255 : CollatzResearch.WordTrace tailWord_1164255 prefixEnd_1164255 14761047392603643966869 := by
  unfold tailWord_1164255
  simp only [CollatzResearch.WordTrace]
  refine ⟨42463868397110448768734219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28309245598073632512489479 42463868397110448768734219)
  ·
    refine ⟨63695802595665673153101329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42463868397110448768734219 63695802595665673153101329)
    ·
      refine ⟨47771851946749254864825997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63695802595665673153101329 47771851946749254864825997)
      ·
        refine ⟨17914444480030970574309749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47771851946749254864825997 17914444480030970574309749)
        ·
          refine ⟨1679479170002903491341539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17914444480030970574309749 1679479170002903491341539)
          ·
            refine ⟨2519218755004355237012309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1679479170002903491341539 2519218755004355237012309)
            ·
              refine ⟨14761047392603643966869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2519218755004355237012309 14761047392603643966869)
              ·
                rfl

theorem cell22_1164255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 9].length) (baseStart_1164255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164255 prefixEnd_1164255 := by exact prefixLift 1164255
  have htrace : WordTrace (prefixWord ++ tailWord_1164255) baseStart_1164255 baseEnd_1164255 := by
    simpa [prefixWord, tailWord_1164255, baseEnd_1164255] using wordTrace_append hprefix tailTrace_1164255
  have hstable : (prefixWord ++ tailWord_1164255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164255).length < 2 ^ (prefixWord ++ tailWord_1164255).sum := by decide
  have hdescent : baseEnd_1164255 < baseStart_1164255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164300 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 7]
def baseStart_1164300 : Nat := 118140960795 + 1164300 * 2 ^ 59
def prefixEnd_1164300 : Nat := 4983230072969 + 3 ^ 40 * 1164300 * 2
def baseEnd_1164300 : Nat := 132854561339977756576775

theorem tailTrace_1164300 : CollatzResearch.WordTrace tailWord_1164300 prefixEnd_1164300 132854561339977756576775 := by
  unfold tailWord_1164300
  simp only [CollatzResearch.WordTrace]
  refine ⟨21232754840973710727061177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28310339787964947636081569 21232754840973710727061177)
  ·
    refine ⟨15924566130730283045295883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21232754840973710727061177 15924566130730283045295883)
    ·
      refine ⟨23886849196095424567943825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15924566130730283045295883 23886849196095424567943825)
      ·
        refine ⟨17915136897071568425957869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23886849196095424567943825 17915136897071568425957869)
        ·
          refine ⟨6718176336401838159734201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17915136897071568425957869 6718176336401838159734201)
          ·
            refine ⟨5038632252301378619800651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6718176336401838159734201 5038632252301378619800651)
            ·
              refine ⟨7557948378452067929700977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5038632252301378619800651 7557948378452067929700977)
              ·
                refine ⟨5668461283839050947275733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7557948378452067929700977 5668461283839050947275733)
                ·
                  refine ⟨132854561339977756576775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5668461283839050947275733 132854561339977756576775)
                  ·
                    rfl

theorem cell22_1164300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_1164300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164300 prefixEnd_1164300 := by exact prefixLift 1164300
  have htrace : WordTrace (prefixWord ++ tailWord_1164300) baseStart_1164300 baseEnd_1164300 := by
    simpa [prefixWord, tailWord_1164300, baseEnd_1164300] using wordTrace_append hprefix tailTrace_1164300
  have hstable : (prefixWord ++ tailWord_1164300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164300).length < 2 ^ (prefixWord ++ tailWord_1164300).sum := by decide
  have hdescent : baseEnd_1164300 < baseStart_1164300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164306 : List Nat := [3, 2, 5, 1, 1, 2, 8]
def baseStart_1164306 : Nat := 118140960795 + 1164306 * 2 ^ 59
def prefixEnd_1164306 : Nat := 4983230072969 + 3 ^ 40 * 1164306 * 2
def baseEnd_1164306 : Nat := 14761693997872268669641

theorem tailTrace_1164306 : CollatzResearch.WordTrace tailWord_1164306 prefixEnd_1164306 14761693997872268669641 := by
  unfold tailWord_1164306
  simp only [CollatzResearch.WordTrace]
  refine ⟨10616432129981421119710193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28310485679950456319227181 10616432129981421119710193)
  ·
    refine ⟨7962324097486065839782645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10616432129981421119710193 7962324097486065839782645)
    ·
      refine ⟨746467884139318672479623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7962324097486065839782645 746467884139318672479623)
      ·
        refine ⟨1119701826208978008719435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 746467884139318672479623 1119701826208978008719435)
        ·
          refine ⟨1679552739313467013079153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119701826208978008719435 1679552739313467013079153)
          ·
            refine ⟨1259664554485100259809365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1679552739313467013079153 1259664554485100259809365)
            ·
              refine ⟨14761693997872268669641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1259664554485100259809365 14761693997872268669641)
              ·
                rfl

theorem cell22_1164306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 8].length) (baseStart_1164306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164306 prefixEnd_1164306 := by exact prefixLift 1164306
  have htrace : WordTrace (prefixWord ++ tailWord_1164306) baseStart_1164306 baseEnd_1164306 := by
    simpa [prefixWord, tailWord_1164306, baseEnd_1164306] using wordTrace_append hprefix tailTrace_1164306
  have hstable : (prefixWord ++ tailWord_1164306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164306).length < 2 ^ (prefixWord ++ tailWord_1164306).sum := by decide
  have hdescent : baseEnd_1164306 < baseStart_1164306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164375 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 3, 6]
def baseStart_1164375 : Nat := 118140960795 + 1164375 * 2 ^ 59
def prefixEnd_1164375 : Nat := 4983230072969 + 3 ^ 40 * 1164375 * 2
def baseEnd_1164375 : Nat := 398589358052658074105095

theorem tailTrace_1164375 : CollatzResearch.WordTrace tailWord_1164375 prefixEnd_1164375 398589358052658074105095 := by
  unfold tailWord_1164375
  simp only [CollatzResearch.WordTrace]
  refine ⟨42468245156675709263102579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28312163437783806175401719 42468245156675709263102579)
  ·
    refine ⟨63702367735013563894653869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42468245156675709263102579 63702367735013563894653869)
    ·
      refine ⟨23888387900630086460495201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63702367735013563894653869 23888387900630086460495201)
      ·
        refine ⟨17916290925472564845371401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23888387900630086460495201 17916290925472564845371401)
        ·
          refine ⟨13437218194104423634028551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17916290925472564845371401 13437218194104423634028551)
          ·
            refine ⟨20155827291156635451042827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13437218194104423634028551 20155827291156635451042827)
            ·
              refine ⟨30233740936734953176564241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20155827291156635451042827 30233740936734953176564241)
              ·
                refine ⟨22675305702551214882423181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30233740936734953176564241 22675305702551214882423181)
                ·
                  refine ⟨8503239638456705580908693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22675305702551214882423181 8503239638456705580908693)
                  ·
                    refine ⟨398589358052658074105095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8503239638456705580908693 398589358052658074105095)
                    ·
                      rfl

theorem cell22_1164375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_1164375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164375 prefixEnd_1164375 := by exact prefixLift 1164375
  have htrace : WordTrace (prefixWord ++ tailWord_1164375) baseStart_1164375 baseEnd_1164375 := by
    simpa [prefixWord, tailWord_1164375, baseEnd_1164375] using wordTrace_append hprefix tailTrace_1164375
  have hstable : (prefixWord ++ tailWord_1164375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164375).length < 2 ^ (prefixWord ++ tailWord_1164375).sum := by decide
  have hdescent : baseEnd_1164375 < baseStart_1164375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164394 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 1, 5]
def baseStart_1164394 : Nat := 118140960795 + 1164394 * 2 ^ 59
def prefixEnd_1164394 : Nat := 4983230072969 + 3 ^ 40 * 1164394 * 2
def baseEnd_1164394 : Nat := 398595862140948357880037

theorem tailTrace_1164394 : CollatzResearch.WordTrace tailWord_1164394 prefixEnd_1164394 398595862140948357880037 := by
  unfold tailWord_1164394
  simp only [CollatzResearch.WordTrace]
  refine ⟨10617234535901718877011059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28312625429071250338696157 10617234535901718877011059)
  ·
    refine ⟨15925851803852578315516589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10617234535901718877011059 15925851803852578315516589)
    ·
      refine ⟨5972194426444716868318721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15925851803852578315516589 5972194426444716868318721)
      ·
        refine ⟨4479145819833537651239041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5972194426444716868318721 4479145819833537651239041)
        ·
          refine ⟨3359359364875153238429281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4479145819833537651239041 3359359364875153238429281)
          ·
            refine ⟨2519519523656364928821961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3359359364875153238429281 2519519523656364928821961)
            ·
              refine ⟨1889639642742273696616471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2519519523656364928821961 1889639642742273696616471)
              ·
                refine ⟨2834459464113410544924707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889639642742273696616471 2834459464113410544924707)
                ·
                  refine ⟨4251689196170115817387061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834459464113410544924707 4251689196170115817387061)
                  ·
                    refine ⟨398595862140948357880037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4251689196170115817387061 398595862140948357880037)
                    ·
                      rfl

theorem cell22_1164394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_1164394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164394 prefixEnd_1164394 := by exact prefixLift 1164394
  have htrace : WordTrace (prefixWord ++ tailWord_1164394) baseStart_1164394 baseEnd_1164394 := by
    simpa [prefixWord, tailWord_1164394, baseEnd_1164394] using wordTrace_append hprefix tailTrace_1164394
  have hstable : (prefixWord ++ tailWord_1164394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164394).length < 2 ^ (prefixWord ++ tailWord_1164394).sum := by decide
  have hdescent : baseEnd_1164394 < baseStart_1164394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164407 : List Nat := [1, 1, 3, 1, 1, 4, 5, 6]
def baseStart_1164407 : Nat := 118140960795 + 1164407 * 2 ^ 59
def prefixEnd_1164407 : Nat := 4983230072969 + 3 ^ 40 * 1164407 * 2
def baseEnd_1164407 : Nat := 44288923589624517478333

theorem tailTrace_1164407 : CollatzResearch.WordTrace tailWord_1164407 prefixEnd_1164407 44288923589624517478333 := by
  unfold tailWord_1164407
  simp only [CollatzResearch.WordTrace]
  refine ⟨42469412292559778728267475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28312941528373185818844983 42469412292559778728267475)
  ·
    refine ⟨63704118438839668092401213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42469412292559778728267475 63704118438839668092401213)
    ·
      refine ⟨23889044414564875534650455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63704118438839668092401213 23889044414564875534650455)
      ·
        refine ⟨35833566621847313301975683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23889044414564875534650455 35833566621847313301975683)
        ·
          refine ⟨53750349932770969952963525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35833566621847313301975683 53750349932770969952963525)
          ·
            refine ⟨10078190612394556866180661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53750349932770969952963525 10078190612394556866180661)
            ·
              refine ⟨944830369911989706204437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10078190612394556866180661 944830369911989706204437)
              ·
                refine ⟨44288923589624517478333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 944830369911989706204437 44288923589624517478333)
                ·
                  rfl

theorem cell22_1164407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 6].length) (baseStart_1164407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164407 prefixEnd_1164407 := by exact prefixLift 1164407
  have htrace : WordTrace (prefixWord ++ tailWord_1164407) baseStart_1164407 baseEnd_1164407 := by
    simpa [prefixWord, tailWord_1164407, baseEnd_1164407] using wordTrace_append hprefix tailTrace_1164407
  have hstable : (prefixWord ++ tailWord_1164407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164407).length < 2 ^ (prefixWord ++ tailWord_1164407).sum := by decide
  have hdescent : baseEnd_1164407 < baseStart_1164407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164439 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 3, 3]
def baseStart_1164439 : Nat := 118140960795 + 1164439 * 2 ^ 59
def prefixEnd_1164439 : Nat := 4983230072969 + 3 ^ 40 * 1164439 * 2
def baseEnd_1164439 : Nat := 398611266560583240504899

theorem tailTrace_1164439 : CollatzResearch.WordTrace tailWord_1164439 prefixEnd_1164439 398611266560583240504899 := by
  unfold tailWord_1164439
  simp only [CollatzResearch.WordTrace]
  refine ⟨42470579428443848193432371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28313719618962565462288247 42470579428443848193432371)
  ·
    refine ⟨63705869142665772290148557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42470579428443848193432371 63705869142665772290148557)
    ·
      refine ⟨23889700928499664608805709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63705869142665772290148557 23889700928499664608805709)
      ·
        refine ⟨8958637848187374228302141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23889700928499664608805709 8958637848187374228302141)
        ·
          refine ⟨3359489193070265335613303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8958637848187374228302141 3359489193070265335613303)
          ·
            refine ⟨5039233789605398003419955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3359489193070265335613303 5039233789605398003419955)
            ·
              refine ⟨7558850684408097005129933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5039233789605398003419955 7558850684408097005129933)
              ·
                refine ⟨2834569006653036376923725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7558850684408097005129933 2834569006653036376923725)
                ·
                  refine ⟨1062963377494888641346397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2834569006653036376923725 1062963377494888641346397)
                  ·
                    refine ⟨398611266560583240504899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1062963377494888641346397 398611266560583240504899)
                    ·
                      rfl

theorem cell22_1164439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_1164439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164439 prefixEnd_1164439 := by exact prefixLift 1164439
  have htrace : WordTrace (prefixWord ++ tailWord_1164439) baseStart_1164439 baseEnd_1164439 := by
    simpa [prefixWord, tailWord_1164439, baseEnd_1164439] using wordTrace_append hprefix tailTrace_1164439
  have hstable : (prefixWord ++ tailWord_1164439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164439).length < 2 ^ (prefixWord ++ tailWord_1164439).sum := by decide
  have hdescent : baseEnd_1164439 < baseStart_1164439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164473 : List Nat := [1, 2, 1, 4, 1, 5, 1, 3, 1, 3]
def baseStart_1164473 : Nat := 118140960795 + 1164473 * 2 ^ 59
def prefixEnd_1164473 : Nat := 4983230072969 + 3 ^ 40 * 1164473 * 2
def baseEnd_1164473 : Nat := 398622905455418485154795

theorem tailTrace_1164473 : CollatzResearch.WordTrace tailWord_1164473 prefixEnd_1164473 398622905455418485154795 := by
  unfold tailWord_1164473
  simp only [CollatzResearch.WordTrace]
  refine ⟨42471819510320672000170073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28314546340213781333446715 42471819510320672000170073)
  ·
    refine ⟨31853864632740504000127555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42471819510320672000170073 31853864632740504000127555)
    ·
      refine ⟨47780796949110756000191333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31853864632740504000127555 47780796949110756000191333)
      ·
        refine ⟨8958899427958266750035875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47780796949110756000191333 8958899427958266750035875)
        ·
          refine ⟨13438349141937400125053813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8958899427958266750035875 13438349141937400125053813)
          ·
            refine ⟨1259845232056631261723795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13438349141937400125053813 1259845232056631261723795)
            ·
              refine ⟨1889767848084946892585693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259845232056631261723795 1889767848084946892585693)
              ·
                refine ⟨708662943031855084719635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1889767848084946892585693 708662943031855084719635)
                ·
                  refine ⟨1062994414547782627079453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708662943031855084719635 1062994414547782627079453)
                  ·
                    refine ⟨398622905455418485154795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1062994414547782627079453 398622905455418485154795)
                    ·
                      rfl

theorem cell22_1164473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 1, 3].length) (baseStart_1164473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164473 prefixEnd_1164473 := by exact prefixLift 1164473
  have htrace : WordTrace (prefixWord ++ tailWord_1164473) baseStart_1164473 baseEnd_1164473 := by
    simpa [prefixWord, tailWord_1164473, baseEnd_1164473] using wordTrace_append hprefix tailTrace_1164473
  have hstable : (prefixWord ++ tailWord_1164473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164473).length < 2 ^ (prefixWord ++ tailWord_1164473).sum := by decide
  have hdescent : baseEnd_1164473 < baseStart_1164473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164548 : List Nat := [2, 3, 2, 2, 2, 1, 4, 2, 4]
def baseStart_1164548 : Nat := 118140960795 + 1164548 * 2 ^ 59
def prefixEnd_1164548 : Nat := 4983230072969 + 3 ^ 40 * 1164548 * 2
def baseEnd_1164548 : Nat := 132882859829381096509855

theorem tailTrace_1164548 : CollatzResearch.WordTrace tailWord_1164548 prefixEnd_1164548 132882859829381096509855 := by
  unfold tailWord_1164548
  simp only [CollatzResearch.WordTrace]
  refine ⟨21237277492524479904575149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28316369990032639872766865 21237277492524479904575149)
  ·
    refine ⟨7963979059696679964215681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21237277492524479904575149 7963979059696679964215681)
    ·
      refine ⟨5972984294772509973161761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7963979059696679964215681 5972984294772509973161761)
      ·
        refine ⟨4479738221079382479871321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5972984294772509973161761 4479738221079382479871321)
        ·
          refine ⟨3359803665809536859903491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4479738221079382479871321 3359803665809536859903491)
          ·
            refine ⟨5039705498714305289855237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3359803665809536859903491 5039705498714305289855237)
            ·
              refine ⟨944944781008932241847857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5039705498714305289855237 944944781008932241847857)
              ·
                refine ⟨708708585756699181385893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 944944781008932241847857 708708585756699181385893)
                ·
                  refine ⟨132882859829381096509855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 708708585756699181385893 132882859829381096509855)
                  ·
                    rfl

theorem cell22_1164548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_1164548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164548 prefixEnd_1164548 := by exact prefixLift 1164548
  have htrace : WordTrace (prefixWord ++ tailWord_1164548) baseStart_1164548 baseEnd_1164548 := by
    simpa [prefixWord, tailWord_1164548, baseEnd_1164548] using wordTrace_append hprefix tailTrace_1164548
  have hstable : (prefixWord ++ tailWord_1164548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164548).length < 2 ^ (prefixWord ++ tailWord_1164548).sum := by decide
  have hdescent : baseEnd_1164548 < baseStart_1164548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164576 : List Nat := [2, 1, 1, 5, 3, 1, 3, 6]
def baseStart_1164576 : Nat := 118140960795 + 1164576 * 2 ^ 59
def prefixEnd_1164576 : Nat := 4983230072969 + 3 ^ 40 * 1164576 * 2
def baseEnd_1164576 : Nat := 44295351606706727758831

theorem tailTrace_1164576 : CollatzResearch.WordTrace tailWord_1164576 prefixEnd_1164576 44295351606706727758831 := by
  unfold tailWord_1164576
  simp only [CollatzResearch.WordTrace]
  refine ⟨21237788114473760295584791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28317050819298347060779721 21237788114473760295584791)
  ·
    refine ⟨31856682171710640443377187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21237788114473760295584791 31856682171710640443377187)
    ·
      refine ⟨47785023257565960665065781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31856682171710640443377187 47785023257565960665065781)
      ·
        refine ⟨4479845930396808812349917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47785023257565960665065781 4479845930396808812349917)
        ·
          refine ⟨1679942223898803304631219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4479845930396808812349917 1679942223898803304631219)
          ·
            refine ⟨2519913335848204956946829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1679942223898803304631219 2519913335848204956946829)
            ·
              refine ⟨944967500943076858855061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2519913335848204956946829 944967500943076858855061)
              ·
                refine ⟨44295351606706727758831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 944967500943076858855061 44295351606706727758831)
                ·
                  rfl

theorem cell22_1164576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 6].length) (baseStart_1164576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164576 prefixEnd_1164576 := by exact prefixLift 1164576
  have htrace : WordTrace (prefixWord ++ tailWord_1164576) baseStart_1164576 baseEnd_1164576 := by
    simpa [prefixWord, tailWord_1164576, baseEnd_1164576] using wordTrace_append hprefix tailTrace_1164576
  have hstable : (prefixWord ++ tailWord_1164576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164576).length < 2 ^ (prefixWord ++ tailWord_1164576).sum := by decide
  have hdescent : baseEnd_1164576 < baseStart_1164576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164578 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_1164578 : Nat := 118140960795 + 1164578 * 2 ^ 59
def prefixEnd_1164578 : Nat := 4983230072969 + 3 ^ 40 * 1164578 * 2
def baseEnd_1164578 : Nat := 398658849101233211279473

theorem tailTrace_1164578 : CollatzResearch.WordTrace tailWord_1164578 prefixEnd_1164578 398658849101233211279473 := by
  unfold tailWord_1164578
  simp only [CollatzResearch.WordTrace]
  refine ⟨10618912293735068733185597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28317099449960183288494925 10618912293735068733185597)
  ·
    refine ⟨3982092110150650774944599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10618912293735068733185597 3982092110150650774944599)
    ·
      refine ⟨5973138165225976162416899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3982092110150650774944599 5973138165225976162416899)
      ·
        refine ⟨8959707247838964243625349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5973138165225976162416899 8959707247838964243625349)
        ·
          refine ⟨1679945108969805795679753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8959707247838964243625349 1679945108969805795679753)
          ·
            refine ⟨1259958831727354346759815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1679945108969805795679753 1259958831727354346759815)
            ·
              refine ⟨1889938247591031520139723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1259958831727354346759815 1889938247591031520139723)
              ·
                refine ⟨2834907371386547280209585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889938247591031520139723 2834907371386547280209585)
                ·
                  refine ⟨2126180528539910460157189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2834907371386547280209585 2126180528539910460157189)
                  ·
                    refine ⟨398658849101233211279473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2126180528539910460157189 398658849101233211279473)
                    ·
                      rfl

theorem cell22_1164578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_1164578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164578 prefixEnd_1164578 := by exact prefixLift 1164578
  have htrace : WordTrace (prefixWord ++ tailWord_1164578) baseStart_1164578 baseEnd_1164578 := by
    simpa [prefixWord, tailWord_1164578, baseEnd_1164578] using wordTrace_append hprefix tailTrace_1164578
  have hstable : (prefixWord ++ tailWord_1164578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164578).length < 2 ^ (prefixWord ++ tailWord_1164578).sum := by decide
  have hdescent : baseEnd_1164578 < baseStart_1164578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164604 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 7]
def baseStart_1164604 : Nat := 118140960795 + 1164604 * 2 ^ 59
def prefixEnd_1164604 : Nat := 4983230072969 + 3 ^ 40 * 1164604 * 2
def baseEnd_1164604 : Nat := 132889249810859270043131

theorem tailTrace_1164604 : CollatzResearch.WordTrace tailWord_1164604 prefixEnd_1164604 132889249810859270043131 := by
  unfold tailWord_1164604
  simp only [CollatzResearch.WordTrace]
  refine ⟨21238298736423040686594433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28317731648564054248792577 21238298736423040686594433)
  ·
    refine ⟨15928724052317280514945825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21238298736423040686594433 15928724052317280514945825)
    ·
      refine ⟨11946543039237960386209369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15928724052317280514945825 11946543039237960386209369)
      ·
        refine ⟨8959907279428470289657027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11946543039237960386209369 8959907279428470289657027)
        ·
          refine ⟨13439860919142705434485541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8959907279428470289657027 13439860919142705434485541)
          ·
            refine ⟨2519973922339257268966039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13439860919142705434485541 2519973922339257268966039)
            ·
              refine ⟨3779960883508885903449059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2519973922339257268966039 3779960883508885903449059)
              ·
                refine ⟨5669941325263328855173589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3779960883508885903449059 5669941325263328855173589)
                ·
                  refine ⟨132889249810859270043131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5669941325263328855173589 132889249810859270043131)
                  ·
                    rfl

theorem cell22_1164604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_1164604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164604 prefixEnd_1164604 := by exact prefixLift 1164604
  have htrace : WordTrace (prefixWord ++ tailWord_1164604) baseStart_1164604 baseEnd_1164604 := by
    simpa [prefixWord, tailWord_1164604, baseEnd_1164604] using wordTrace_append hprefix tailTrace_1164604
  have hstable : (prefixWord ++ tailWord_1164604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164604).length < 2 ^ (prefixWord ++ tailWord_1164604).sum := by decide
  have hdescent : baseEnd_1164604 < baseStart_1164604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164614 : List Nat := [6, 1, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_1164614 : Nat := 118140960795 + 1164614 * 2 ^ 59
def prefixEnd_1164614 : Nat := 4983230072969 + 3 ^ 40 * 1164614 * 2
def baseEnd_1164614 : Nat := 398671172636941117379363

theorem tailTrace_1164614 : CollatzResearch.WordTrace tailWord_1164614 prefixEnd_1164614 398671172636941117379363 := by
  unfold tailWord_1164614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1327405068837807908782903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28317974801873235387368597 1327405068837807908782903)
  ·
    refine ⟨1991107603256711863174355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1327405068837807908782903 1991107603256711863174355)
    ·
      refine ⟨2986661404885067794761533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1991107603256711863174355 2986661404885067794761533)
      ·
        refine ⟨1119998026831900423035575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2986661404885067794761533 1119998026831900423035575)
        ·
          refine ⟨1679997040247850634553363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119998026831900423035575 1679997040247850634553363)
          ·
            refine ⟨2519995560371775951830045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1679997040247850634553363 2519995560371775951830045)
            ·
              refine ⟨944998335139415981936267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2519995560371775951830045 944998335139415981936267)
              ·
                refine ⟨1417497502709123972904401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 944998335139415981936267 1417497502709123972904401)
                ·
                  refine ⟨1063123127031842979678301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1417497502709123972904401 1063123127031842979678301)
                  ·
                    refine ⟨398671172636941117379363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1063123127031842979678301 398671172636941117379363)
                    ·
                      rfl

theorem cell22_1164614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_1164614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164614 prefixEnd_1164614 := by exact prefixLift 1164614
  have htrace : WordTrace (prefixWord ++ tailWord_1164614) baseStart_1164614 baseEnd_1164614 := by
    simpa [prefixWord, tailWord_1164614, baseEnd_1164614] using wordTrace_append hprefix tailTrace_1164614
  have hstable : (prefixWord ++ tailWord_1164614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164614).length < 2 ^ (prefixWord ++ tailWord_1164614).sum := by decide
  have hdescent : baseEnd_1164614 < baseStart_1164614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164634 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 3, 4]
def baseStart_1164634 : Nat := 118140960795 + 1164634 * 2 ^ 59
def prefixEnd_1164634 : Nat := 4983230072969 + 3 ^ 40 * 1164634 * 2
def baseEnd_1164634 : Nat := 398678019045667731879301

theorem tailTrace_1164634 : CollatzResearch.WordTrace tailWord_1164634 prefixEnd_1164634 398678019045667731879301 := by
  unfold tailWord_1164634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10619422915684349124195239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28318461108491597664520637 10619422915684349124195239)
  ·
    refine ⟨15929134373526523686292859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10619422915684349124195239 15929134373526523686292859)
    ·
      refine ⟨23893701560289785529439289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15929134373526523686292859 23893701560289785529439289)
      ·
        refine ⟨17920276170217339147079467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23893701560289785529439289 17920276170217339147079467)
        ·
          refine ⟨26880414255326008720619201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17920276170217339147079467 26880414255326008720619201)
          ·
            refine ⟨20160310691494506540464401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26880414255326008720619201 20160310691494506540464401)
            ·
              refine ⟨15120233018620879905348301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20160310691494506540464401 15120233018620879905348301)
              ·
                refine ⟨5670087381982829964505613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15120233018620879905348301 5670087381982829964505613)
                ·
                  refine ⟨2126282768243561236689605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5670087381982829964505613 2126282768243561236689605)
                  ·
                    refine ⟨398678019045667731879301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2126282768243561236689605 398678019045667731879301)
                    ·
                      rfl

theorem cell22_1164634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_1164634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164634 prefixEnd_1164634 := by exact prefixLift 1164634
  have htrace : WordTrace (prefixWord ++ tailWord_1164634) baseStart_1164634 baseEnd_1164634 := by
    simpa [prefixWord, tailWord_1164634, baseEnd_1164634] using wordTrace_append hprefix tailTrace_1164634
  have hstable : (prefixWord ++ tailWord_1164634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164634).length < 2 ^ (prefixWord ++ tailWord_1164634).sum := by decide
  have hdescent : baseEnd_1164634 < baseStart_1164634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164702 : List Nat := [4, 3, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_1164702 : Nat := 118140960795 + 1164702 * 2 ^ 59
def prefixEnd_1164702 : Nat := 4983230072969 + 3 ^ 40 * 1164702 * 2
def baseEnd_1164702 : Nat := 398701296835338221179093

theorem tailTrace_1164702 : CollatzResearch.WordTrace tailWord_1164702 prefixEnd_1164702 398701296835338221179093 := by
  unfold tailWord_1164702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5310021478311380513782045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28320114550994029406837573 5310021478311380513782045)
  ·
    refine ⟨1991258054366767692668267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5310021478311380513782045 1991258054366767692668267)
    ·
      refine ⟨2986887081550151539002401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1991258054366767692668267 2986887081550151539002401)
      ·
        refine ⟨2240165311162613654251801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2986887081550151539002401 2240165311162613654251801)
        ·
          refine ⟨1680123983371960240688851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2240165311162613654251801 1680123983371960240688851)
          ·
            refine ⟨2520185975057940361033277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1680123983371960240688851 2520185975057940361033277)
            ·
              refine ⟨945069740646727635387479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2520185975057940361033277 945069740646727635387479)
              ·
                refine ⟨1417604610970091453081219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945069740646727635387479 1417604610970091453081219)
                ·
                  refine ⟨2126406916455137179621829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417604610970091453081219 2126406916455137179621829)
                  ·
                    refine ⟨398701296835338221179093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2126406916455137179621829 398701296835338221179093)
                    ·
                      rfl

theorem cell22_1164702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_1164702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164702 prefixEnd_1164702 := by exact prefixLift 1164702
  have htrace : WordTrace (prefixWord ++ tailWord_1164702) baseStart_1164702 baseEnd_1164702 := by
    simpa [prefixWord, tailWord_1164702, baseEnd_1164702] using wordTrace_append hprefix tailTrace_1164702
  have hstable : (prefixWord ++ tailWord_1164702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164702).length < 2 ^ (prefixWord ++ tailWord_1164702).sum := by decide
  have hdescent : baseEnd_1164702 < baseStart_1164702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164717 : List Nat := [1, 5, 2, 2, 1, 3, 2, 2, 4]
def baseStart_1164717 : Nat := 118140960795 + 1164717 * 2 ^ 59
def prefixEnd_1164717 : Nat := 4983230072969 + 3 ^ 40 * 1164717 * 2
def baseEnd_1164717 : Nat := 132902143880627727351349

theorem tailTrace_1164717 : CollatzResearch.WordTrace tailWord_1164717 prefixEnd_1164717 132902143880627727351349 := by
  unfold tailWord_1164717
  simp only [CollatzResearch.WordTrace]
  refine ⟨42480718921436701672052405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28320479280957801114701603 42480718921436701672052405)
  ·
    refine ⟨3982567398884690781754913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42480718921436701672052405 3982567398884690781754913)
    ·
      refine ⟨2986925549163518086316185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3982567398884690781754913 2986925549163518086316185)
      ·
        refine ⟨2240194161872638564737139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2986925549163518086316185 2240194161872638564737139)
        ·
          refine ⟨3360291242808957847105709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2240194161872638564737139 3360291242808957847105709)
          ·
            refine ⟨1260109216053359192664641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3360291242808957847105709 1260109216053359192664641)
            ·
              refine ⟨945081912040019394498481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1260109216053359192664641 945081912040019394498481)
              ·
                refine ⟨708811434030014545873861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 945081912040019394498481 708811434030014545873861)
                ·
                  refine ⟨132902143880627727351349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 708811434030014545873861 132902143880627727351349)
                  ·
                    rfl

theorem cell22_1164717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_1164717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164717 prefixEnd_1164717 := by exact prefixLift 1164717
  have htrace : WordTrace (prefixWord ++ tailWord_1164717) baseStart_1164717 baseEnd_1164717 := by
    simpa [prefixWord, tailWord_1164717, baseEnd_1164717] using wordTrace_append hprefix tailTrace_1164717
  have hstable : (prefixWord ++ tailWord_1164717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164717).length < 2 ^ (prefixWord ++ tailWord_1164717).sum := by decide
  have hdescent : baseEnd_1164717 < baseStart_1164717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164771 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 2, 5]
def baseStart_1164771 : Nat := 118140960795 + 1164771 * 2 ^ 59
def prefixEnd_1164771 : Nat := 4983230072969 + 3 ^ 40 * 1164771 * 2
def baseEnd_1164771 : Nat := 398724916945445041203881

theorem tailTrace_1164771 : CollatzResearch.WordTrace tailWord_1164771 prefixEnd_1164771 398724916945445041203881 := by
  unfold tailWord_1164771
  simp only [CollatzResearch.WordTrace]
  refine ⟨42482688463241068894518167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28321792308827379263012111 42482688463241068894518167)
  ·
    refine ⟨63724032694861603341777251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42482688463241068894518167 63724032694861603341777251)
    ·
      refine ⟨95586049042292405012665877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63724032694861603341777251 95586049042292405012665877)
      ·
        refine ⟨4480596048857456484968713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 95586049042292405012665877 4480596048857456484968713)
        ·
          refine ⟨3360447036643092363726535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4480596048857456484968713 3360447036643092363726535)
          ·
            refine ⟨5040670554964638545589803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3360447036643092363726535 5040670554964638545589803)
            ·
              refine ⟨7561005832446957818384705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5040670554964638545589803 7561005832446957818384705)
              ·
                refine ⟨5670754374335218363788529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7561005832446957818384705 5670754374335218363788529)
                ·
                  refine ⟨4253065780751413772841397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5670754374335218363788529 4253065780751413772841397)
                  ·
                    refine ⟨398724916945445041203881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4253065780751413772841397 398724916945445041203881)
                    ·
                      rfl

theorem cell22_1164771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 5].length) (baseStart_1164771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164771 prefixEnd_1164771 := by exact prefixLift 1164771
  have htrace : WordTrace (prefixWord ++ tailWord_1164771) baseStart_1164771 baseEnd_1164771 := by
    simpa [prefixWord, tailWord_1164771, baseEnd_1164771] using wordTrace_append hprefix tailTrace_1164771
  have hstable : (prefixWord ++ tailWord_1164771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164771).length < 2 ^ (prefixWord ++ tailWord_1164771).sum := by decide
  have hdescent : baseEnd_1164771 < baseStart_1164771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164773 : List Nat := [1, 3, 1, 5, 1, 1, 3, 2, 5]
def baseStart_1164773 : Nat := 118140960795 + 1164773 * 2 ^ 59
def prefixEnd_1164773 : Nat := 4983230072969 + 3 ^ 40 * 1164773 * 2
def baseEnd_1164773 : Nat := 132908533862105900884625

theorem tailTrace_1164773 : CollatzResearch.WordTrace tailWord_1164773 prefixEnd_1164773 132908533862105900884625 := by
  unfold tailWord_1164773
  simp only [CollatzResearch.WordTrace]
  refine ⟨42482761409233823236090973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28321840939489215490727315 42482761409233823236090973)
  ·
    refine ⟨15931035528462683713534115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42482761409233823236090973 15931035528462683713534115)
    ·
      refine ⟨23896553292694025570301173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15931035528462683713534115 23896553292694025570301173)
      ·
        refine ⟨2240301871190064897215735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23896553292694025570301173 2240301871190064897215735)
        ·
          refine ⟨3360452806785097345823603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2240301871190064897215735 3360452806785097345823603)
          ·
            refine ⟨5040679210177646018735405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3360452806785097345823603 5040679210177646018735405)
            ·
              refine ⟨1890254703816617257025777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5040679210177646018735405 1890254703816617257025777)
              ·
                refine ⟨1417691027862462942769333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1890254703816617257025777 1417691027862462942769333)
                ·
                  refine ⟨132908533862105900884625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1417691027862462942769333 132908533862105900884625)
                  ·
                    rfl

theorem cell22_1164773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_1164773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164773 prefixEnd_1164773 := by exact prefixLift 1164773
  have htrace : WordTrace (prefixWord ++ tailWord_1164773) baseStart_1164773 baseEnd_1164773 := by
    simpa [prefixWord, tailWord_1164773, baseEnd_1164773] using wordTrace_append hprefix tailTrace_1164773
  have hstable : (prefixWord ++ tailWord_1164773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164773).length < 2 ^ (prefixWord ++ tailWord_1164773).sum := by decide
  have hdescent : baseEnd_1164773 < baseStart_1164773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164790 : List Nat := [5, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_1164790 : Nat := 118140960795 + 1164790 * 2 ^ 59
def prefixEnd_1164790 : Nat := 4983230072969 + 3 ^ 40 * 1164790 * 2
def baseEnd_1164790 : Nat := 132910473677911774992941

theorem tailTrace_1164790 : CollatzResearch.WordTrace tailWord_1164790 prefixEnd_1164790 132910473677911774992941 := by
  unfold tailWord_1164790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2655211340635764696216239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28322254300114823426306549 2655211340635764696216239)
  ·
    refine ⟨3982817010953647044324359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2655211340635764696216239 3982817010953647044324359)
    ·
      refine ⟨5974225516430470566486539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3982817010953647044324359 5974225516430470566486539)
      ·
        refine ⟨8961338274645705849729809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5974225516430470566486539 8961338274645705849729809)
        ·
          refine ⟨6721003705984279387297357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8961338274645705849729809 6721003705984279387297357)
          ·
            refine ⟨2520376389744104770236509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6721003705984279387297357 2520376389744104770236509)
            ·
              refine ⟨945141146154039288838691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2520376389744104770236509 945141146154039288838691)
              ·
                refine ⟨1417711719231058933258037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945141146154039288838691 1417711719231058933258037)
                ·
                  refine ⟨132910473677911774992941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1417711719231058933258037 132910473677911774992941)
                  ·
                    rfl

theorem cell22_1164790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_1164790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164790 prefixEnd_1164790 := by exact prefixLift 1164790
  have htrace : WordTrace (prefixWord ++ tailWord_1164790) baseStart_1164790 baseEnd_1164790 := by
    simpa [prefixWord, tailWord_1164790, baseEnd_1164790] using wordTrace_append hprefix tailTrace_1164790
  have hstable : (prefixWord ++ tailWord_1164790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164790).length < 2 ^ (prefixWord ++ tailWord_1164790).sum := by decide
  have hdescent : baseEnd_1164790 < baseStart_1164790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164831 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 4, 4]
def baseStart_1164831 : Nat := 118140960795 + 1164831 * 2 ^ 59
def prefixEnd_1164831 : Nat := 4983230072969 + 3 ^ 40 * 1164831 * 2
def baseEnd_1164831 : Nat := 398745456171624884703697

theorem tailTrace_1164831 : CollatzResearch.WordTrace tailWord_1164831 prefixEnd_1164831 398745456171624884703697 := by
  unfold tailWord_1164831
  simp only [CollatzResearch.WordTrace]
  refine ⟨42484876843023699141702347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28323251228682466094468231 42484876843023699141702347)
  ·
    refine ⟨63727315264535548712553521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42484876843023699141702347 63727315264535548712553521)
    ·
      refine ⟨47795486448401661534415141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63727315264535548712553521 47795486448401661534415141)
      ·
        refine ⟨8961653709075311537702839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47795486448401661534415141 8961653709075311537702839)
        ·
          refine ⟨13442480563612967306554259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8961653709075311537702839 13442480563612967306554259)
          ·
            refine ⟨20163720845419450959831389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13442480563612967306554259 20163720845419450959831389)
            ·
              refine ⟨7561395317032294109936771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20163720845419450959831389 7561395317032294109936771)
              ·
                refine ⟨11342092975548441164905157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7561395317032294109936771 11342092975548441164905157)
                ·
                  refine ⟨2126642432915332718419717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11342092975548441164905157 2126642432915332718419717)
                  ·
                    refine ⟨398745456171624884703697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2126642432915332718419717 398745456171624884703697)
                    ·
                      rfl

theorem cell22_1164831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_1164831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164831 prefixEnd_1164831 := by exact prefixLift 1164831
  have htrace : WordTrace (prefixWord ++ tailWord_1164831) baseStart_1164831 baseEnd_1164831 := by
    simpa [prefixWord, tailWord_1164831, baseEnd_1164831] using wordTrace_append hprefix tailTrace_1164831
  have hstable : (prefixWord ++ tailWord_1164831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164831).length < 2 ^ (prefixWord ++ tailWord_1164831).sum := by decide
  have hdescent : baseEnd_1164831 < baseStart_1164831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164833 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 4, 3]
def baseStart_1164833 : Nat := 118140960795 + 1164833 * 2 ^ 59
def prefixEnd_1164833 : Nat := 4983230072969 + 3 ^ 40 * 1164833 * 2
def baseEnd_1164833 : Nat := 398746140812497546153691

theorem tailTrace_1164833 : CollatzResearch.WordTrace tailWord_1164833 prefixEnd_1164833 398746140812497546153691 := by
  unfold tailWord_1164833
  simp only [CollatzResearch.WordTrace]
  refine ⟨42484949789016453483275153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28323299859344302322183435 42484949789016453483275153)
  ·
    refine ⟨31863712341762340112456365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42484949789016453483275153 31863712341762340112456365)
    ·
      refine ⟨11948892128160877542171137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31863712341762340112456365 11948892128160877542171137)
      ·
        refine ⟨8961669096120658156628353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11948892128160877542171137 8961669096120658156628353)
        ·
          refine ⟨6721251822090493617471265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8961669096120658156628353 6721251822090493617471265)
          ·
            refine ⟨5040938866567870213103449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6721251822090493617471265 5040938866567870213103449)
            ·
              refine ⟨3780704149925902659827587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5040938866567870213103449 3780704149925902659827587)
              ·
                refine ⟨5671056224888853989741381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3780704149925902659827587 5671056224888853989741381)
                ·
                  refine ⟨1063323042166660123076509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5671056224888853989741381 1063323042166660123076509)
                  ·
                    refine ⟨398746140812497546153691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1063323042166660123076509 398746140812497546153691)
                    ·
                      rfl

theorem cell22_1164833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_1164833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164833 prefixEnd_1164833 := by exact prefixLift 1164833
  have htrace : WordTrace (prefixWord ++ tailWord_1164833) baseStart_1164833 baseEnd_1164833 := by
    simpa [prefixWord, tailWord_1164833, baseEnd_1164833] using wordTrace_append hprefix tailTrace_1164833
  have hstable : (prefixWord ++ tailWord_1164833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164833).length < 2 ^ (prefixWord ++ tailWord_1164833).sum := by decide
  have hdescent : baseEnd_1164833 < baseStart_1164833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164835 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 6]
def baseStart_1164835 : Nat := 118140960795 + 1164835 * 2 ^ 59
def prefixEnd_1164835 : Nat := 4983230072969 + 3 ^ 40 * 1164835 * 2
def baseEnd_1164835 : Nat := 132915608484456735867895

theorem tailTrace_1164835 : CollatzResearch.WordTrace tailWord_1164835 prefixEnd_1164835 132915608484456735867895 := by
  unfold tailWord_1164835
  simp only [CollatzResearch.WordTrace]
  refine ⟨42485022735009207824847959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28323348490006138549898639 42485022735009207824847959)
  ·
    refine ⟨63727534102513811737271939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42485022735009207824847959 63727534102513811737271939)
    ·
      refine ⟨95591301153770717605907909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63727534102513811737271939 95591301153770717605907909)
      ·
        refine ⟨17923368966332009551107733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95591301153770717605907909 17923368966332009551107733)
        ·
          refine ⟨840157920296812947708175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17923368966332009551107733 840157920296812947708175)
          ·
            refine ⟨1260236880445219421562263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840157920296812947708175 1260236880445219421562263)
            ·
              refine ⟨1890355320667829132343395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260236880445219421562263 1890355320667829132343395)
              ·
                refine ⟨2835532981001743698515093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1890355320667829132343395 2835532981001743698515093)
                ·
                  refine ⟨132915608484456735867895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2835532981001743698515093 132915608484456735867895)
                  ·
                    rfl

theorem cell22_1164835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 6].length) (baseStart_1164835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164835 prefixEnd_1164835 := by exact prefixLift 1164835
  have htrace : WordTrace (prefixWord ++ tailWord_1164835) baseStart_1164835 baseEnd_1164835 := by
    simpa [prefixWord, tailWord_1164835, baseEnd_1164835] using wordTrace_append hprefix tailTrace_1164835
  have hstable : (prefixWord ++ tailWord_1164835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164835).length < 2 ^ (prefixWord ++ tailWord_1164835).sum := by decide
  have hdescent : baseEnd_1164835 < baseStart_1164835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164854 : List Nat := [5, 1, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_1164854 : Nat := 118140960795 + 1164854 * 2 ^ 59
def prefixEnd_1164854 : Nat := 4983230072969 + 3 ^ 40 * 1164854 * 2
def baseEnd_1164854 : Nat := 398753329541660491378627

theorem tailTrace_1164854 : CollatzResearch.WordTrace tailWord_1164854 prefixEnd_1164854 398753329541660491378627 := by
  unfold tailWord_1164854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2655357232621273379361851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28323810481293582713193077 2655357232621273379361851)
  ·
    refine ⟨3983035848931910069042777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2655357232621273379361851 3983035848931910069042777)
    ·
      refine ⟨2987276886698932551782083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3983035848931910069042777 2987276886698932551782083)
      ·
        refine ⟨4480915330048398827673125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2987276886698932551782083 4480915330048398827673125)
        ·
          refine ⟨840171624384074780188711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4480915330048398827673125 840171624384074780188711)
          ·
            refine ⟨1260257436576112170283067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840171624384074780188711 1260257436576112170283067)
            ·
              refine ⟨1890386154864168255424601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260257436576112170283067 1890386154864168255424601)
              ·
                refine ⟨1417789616148126191568451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1890386154864168255424601 1417789616148126191568451)
                ·
                  refine ⟨2126684424222189287352677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417789616148126191568451 2126684424222189287352677)
                  ·
                    refine ⟨398753329541660491378627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2126684424222189287352677 398753329541660491378627)
                    ·
                      rfl

theorem cell22_1164854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_1164854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164854 prefixEnd_1164854 := by exact prefixLift 1164854
  have htrace : WordTrace (prefixWord ++ tailWord_1164854) baseStart_1164854 baseEnd_1164854 := by
    simpa [prefixWord, tailWord_1164854, baseEnd_1164854] using wordTrace_append hprefix tailTrace_1164854
  have hstable : (prefixWord ++ tailWord_1164854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164854).length < 2 ^ (prefixWord ++ tailWord_1164854).sum := by decide
  have hdescent : baseEnd_1164854 < baseStart_1164854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1164983 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 1, 6]
def baseStart_1164983 : Nat := 118140960795 + 1164983 * 2 ^ 59
def prefixEnd_1164983 : Nat := 4983230072969 + 3 ^ 40 * 1164983 * 2
def baseEnd_1164983 : Nat := 398797488877947154903231

theorem tailTrace_1164983 : CollatzResearch.WordTrace tailWord_1164983 prefixEnd_1164983 398797488877947154903231 := by
  unfold tailWord_1164983
  simp only [CollatzResearch.WordTrace]
  refine ⟨42490420738473029101235603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28326947158982019400823735 42490420738473029101235603)
  ·
    refine ⟨63735631107709543651853405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42490420738473029101235603 63735631107709543651853405)
    ·
      refine ⟨23900861665391078869445027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63735631107709543651853405 23900861665391078869445027)
      ·
        refine ⟨35851292498086618304167541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23900861665391078869445027 35851292498086618304167541)
        ·
          refine ⟨3361058671695620466015707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35851292498086618304167541 3361058671695620466015707)
          ·
            refine ⟨5041588007543430699023561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3361058671695620466015707 5041588007543430699023561)
            ·
              refine ⟨3781191005657573024267671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5041588007543430699023561 3781191005657573024267671)
              ·
                refine ⟨5671786508486359536401507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3781191005657573024267671 5671786508486359536401507)
                ·
                  refine ⟨8507679762729539304602261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5671786508486359536401507 8507679762729539304602261)
                  ·
                    refine ⟨398797488877947154903231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8507679762729539304602261 398797488877947154903231)
                    ·
                      rfl

theorem cell22_1164983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_1164983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1164983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1164983 prefixEnd_1164983 := by exact prefixLift 1164983
  have htrace : WordTrace (prefixWord ++ tailWord_1164983) baseStart_1164983 baseEnd_1164983 := by
    simpa [prefixWord, tailWord_1164983, baseEnd_1164983] using wordTrace_append hprefix tailTrace_1164983
  have hstable : (prefixWord ++ tailWord_1164983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1164983).length < 2 ^ (prefixWord ++ tailWord_1164983).sum := by decide
  have hdescent : baseEnd_1164983 < baseStart_1164983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1164983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165004 : List Nat := [2, 2, 1, 5, 2, 1, 3, 2, 4]
def baseStart_1165004 : Nat := 118140960795 + 1165004 * 2 ^ 59
def prefixEnd_1165004 : Nat := 4983230072969 + 3 ^ 40 * 1165004 * 2
def baseEnd_1165004 : Nat := 132934892535703366709389

theorem tailTrace_1165004 : CollatzResearch.WordTrace tailWord_1165004 prefixEnd_1165004 132934892535703366709389 := by
  unfold tailWord_1165004
  simp only [CollatzResearch.WordTrace]
  refine ⟨21245593335698474843875033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28327457780931299791833377 21245593335698474843875033)
  ·
    refine ⟨15934195001773856132906275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21245593335698474843875033 15934195001773856132906275)
    ·
      refine ⟨23901292502660784199359413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15934195001773856132906275 23901292502660784199359413)
      ·
        refine ⟨2240746172124448518689945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23901292502660784199359413 2240746172124448518689945)
        ·
          refine ⟨1680559629093336389017459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2240746172124448518689945 1680559629093336389017459)
          ·
            refine ⟨2520839443640004583526189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1680559629093336389017459 2520839443640004583526189)
            ·
              refine ⟨945314791365001718822321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2520839443640004583526189 945314791365001718822321)
              ·
                refine ⟨708986093523751289116741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 945314791365001718822321 708986093523751289116741)
                ·
                  refine ⟨132934892535703366709389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 708986093523751289116741 132934892535703366709389)
                  ·
                    rfl

theorem cell22_1165004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_1165004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165004 prefixEnd_1165004 := by exact prefixLift 1165004
  have htrace : WordTrace (prefixWord ++ tailWord_1165004) baseStart_1165004 baseEnd_1165004 := by
    simpa [prefixWord, tailWord_1165004, baseEnd_1165004] using wordTrace_append hprefix tailTrace_1165004
  have hstable : (prefixWord ++ tailWord_1165004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165004).length < 2 ^ (prefixWord ++ tailWord_1165004).sum := by decide
  have hdescent : baseEnd_1165004 < baseStart_1165004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165060 : List Nat := [2, 3, 2, 2, 1, 2, 1, 4, 5]
def baseStart_1165060 : Nat := 118140960795 + 1165060 * 2 ^ 59
def prefixEnd_1165060 : Nat := 4983230072969 + 3 ^ 40 * 1165060 * 2
def baseEnd_1165060 : Nat := 132941282517181540242665

theorem tailTrace_1165060 : CollatzResearch.WordTrace tailWord_1165060 prefixEnd_1165060 132941282517181540242665 := by
  unfold tailWord_1165060
  simp only [CollatzResearch.WordTrace]
  refine ⟨21246614579597035625894317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28328819439462714167859089 21246614579597035625894317)
  ·
    refine ⟨7967480467348888359710369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21246614579597035625894317 7967480467348888359710369)
    ·
      refine ⟨5975610350511666269782777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7967480467348888359710369 5975610350511666269782777)
      ·
        refine ⟨4481707762883749702337083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5975610350511666269782777 4481707762883749702337083)
        ·
          refine ⟨6722561644325624553505625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4481707762883749702337083 6722561644325624553505625)
          ·
            refine ⟨5041921233244218415129219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6722561644325624553505625 5041921233244218415129219)
            ·
              refine ⟨7562881849866327622693829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5041921233244218415129219 7562881849866327622693829)
              ·
                refine ⟨1418040346849936429255093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7562881849866327622693829 1418040346849936429255093)
                ·
                  refine ⟨132941282517181540242665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1418040346849936429255093 132941282517181540242665)
                  ·
                    rfl

theorem cell22_1165060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_1165060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165060 prefixEnd_1165060 := by exact prefixLift 1165060
  have htrace : WordTrace (prefixWord ++ tailWord_1165060) baseStart_1165060 baseEnd_1165060 := by
    simpa [prefixWord, tailWord_1165060, baseEnd_1165060] using wordTrace_append hprefix tailTrace_1165060
  have hstable : (prefixWord ++ tailWord_1165060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165060).length < 2 ^ (prefixWord ++ tailWord_1165060).sum := by decide
  have hdescent : baseEnd_1165060 < baseStart_1165060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165090 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_1165090 : Nat := 118140960795 + 1165090 * 2 ^ 59
def prefixEnd_1165090 : Nat := 4983230072969 + 3 ^ 40 * 1165090 * 2
def baseEnd_1165090 : Nat := 398834117164634542477903

theorem tailTrace_1165090 : CollatzResearch.WordTrace tailWord_1165090 prefixEnd_1165090 398834117164634542477903 := by
  unfold tailWord_1165090
  simp only [CollatzResearch.WordTrace]
  refine ⟨10623580837271346593845181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28329548899390257583587149 10623580837271346593845181)
  ·
    refine ⟨3983842813976754972691943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10623580837271346593845181 3983842813976754972691943)
    ·
      refine ⟨5975764220965132459037915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3983842813976754972691943 5975764220965132459037915)
      ·
        refine ⟨8963646331447698688556873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5975764220965132459037915 8963646331447698688556873)
        ·
          refine ⟨6722734748585774016417655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8963646331447698688556873 6722734748585774016417655)
          ·
            refine ⟨10084102122878661024626483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6722734748585774016417655 10084102122878661024626483)
            ·
              refine ⟨15126153184317991536939725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10084102122878661024626483 15126153184317991536939725)
              ·
                refine ⟨5672307444119246826352397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15126153184317991536939725 5672307444119246826352397)
                ·
                  refine ⟨2127115291544717559882149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5672307444119246826352397 2127115291544717559882149)
                  ·
                    refine ⟨398834117164634542477903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2127115291544717559882149 398834117164634542477903)
                    ·
                      rfl

theorem cell22_1165090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_1165090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165090 prefixEnd_1165090 := by exact prefixLift 1165090
  have htrace : WordTrace (prefixWord ++ tailWord_1165090) baseStart_1165090 baseEnd_1165090 := by
    simpa [prefixWord, tailWord_1165090, baseEnd_1165090] using wordTrace_append hprefix tailTrace_1165090
  have hstable : (prefixWord ++ tailWord_1165090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165090).length < 2 ^ (prefixWord ++ tailWord_1165090).sum := by decide
  have hdescent : baseEnd_1165090 < baseStart_1165090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165107 : List Nat := [1, 1, 1, 2, 7, 1, 1, 3, 1, 4]
def baseStart_1165107 : Nat := 118140960795 + 1165107 * 2 ^ 59
def prefixEnd_1165107 : Nat := 4983230072969 + 3 ^ 40 * 1165107 * 2
def baseEnd_1165107 : Nat := 398839936612052164802851

theorem tailTrace_1165107 : CollatzResearch.WordTrace tailWord_1165107 prefixEnd_1165107 398839936612052164802851 := by
  unfold tailWord_1165107
  simp only [CollatzResearch.WordTrace]
  refine ⟨42494943390023798278749575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28329962260015865519166383 42494943390023798278749575)
  ·
    refine ⟨63742415085035697418124363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42494943390023798278749575 63742415085035697418124363)
    ·
      refine ⟨95613622627553546127186545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63742415085035697418124363 95613622627553546127186545)
      ·
        refine ⟨71710216970665159595389909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95613622627553546127186545 71710216970665159595389909)
        ·
          refine ⟨1680708210249964678016951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 71710216970665159595389909 1680708210249964678016951)
          ·
            refine ⟨2521062315374947017025427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1680708210249964678016951 2521062315374947017025427)
            ·
              refine ⟨3781593473062420525538141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2521062315374947017025427 3781593473062420525538141)
              ·
                refine ⟨1418097552398407697076803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3781593473062420525538141 1418097552398407697076803)
                ·
                  refine ⟨2127146328597611545615205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418097552398407697076803 2127146328597611545615205)
                  ·
                    refine ⟨398839936612052164802851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2127146328597611545615205 398839936612052164802851)
                    ·
                      rfl

theorem cell22_1165107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 4].length) (baseStart_1165107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165107 prefixEnd_1165107 := by exact prefixLift 1165107
  have htrace : WordTrace (prefixWord ++ tailWord_1165107) baseStart_1165107 baseEnd_1165107 := by
    simpa [prefixWord, tailWord_1165107, baseEnd_1165107] using wordTrace_append hprefix tailTrace_1165107
  have hstable : (prefixWord ++ tailWord_1165107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165107).length < 2 ^ (prefixWord ++ tailWord_1165107).sum := by decide
  have hdescent : baseEnd_1165107 < baseStart_1165107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165137 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 1, 5]
def baseStart_1165137 : Nat := 118140960795 + 1165137 * 2 ^ 59
def prefixEnd_1165137 : Nat := 4983230072969 + 3 ^ 40 * 1165137 * 2
def baseEnd_1165137 : Nat := 398850206225142086552759

theorem tailTrace_1165137 : CollatzResearch.WordTrace tailWord_1165137 prefixEnd_1165137 398850206225142086552759 := by
  unfold tailWord_1165137
  simp only [CollatzResearch.WordTrace]
  refine ⟨42496037579915113402341665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28330691719943408934894443 42496037579915113402341665)
  ·
    refine ⟨31872028184936335051756249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42496037579915113402341665 31872028184936335051756249)
    ·
      refine ⟨23904021138702251288817187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31872028184936335051756249 23904021138702251288817187)
      ·
        refine ⟨35856031708053376933225781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23904021138702251288817187 35856031708053376933225781)
        ·
          refine ⟨3361502972630004087489917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35856031708053376933225781 3361502972630004087489917)
          ·
            refine ⟨1260563614736251532808719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3361502972630004087489917 1260563614736251532808719)
            ·
              refine ⟨1890845422104377299213079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260563614736251532808719 1890845422104377299213079)
              ·
                refine ⟨2836268133156565948819619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1890845422104377299213079 2836268133156565948819619)
                ·
                  refine ⟨4254402199734848923229429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2836268133156565948819619 4254402199734848923229429)
                  ·
                    refine ⟨398850206225142086552759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4254402199734848923229429 398850206225142086552759)
                    ·
                      rfl

theorem cell22_1165137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_1165137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165137 prefixEnd_1165137 := by exact prefixLift 1165137
  have htrace : WordTrace (prefixWord ++ tailWord_1165137) baseStart_1165137 baseEnd_1165137 := by
    simpa [prefixWord, tailWord_1165137, baseEnd_1165137] using wordTrace_append hprefix tailTrace_1165137
  have hstable : (prefixWord ++ tailWord_1165137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165137).length < 2 ^ (prefixWord ++ tailWord_1165137).sum := by decide
  have hdescent : baseEnd_1165137 < baseStart_1165137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165156 : List Nat := [2, 3, 1, 1, 6, 1, 1, 3, 4]
def baseStart_1165156 : Nat := 118140960795 + 1165156 * 2 ^ 59
def prefixEnd_1165156 : Nat := 4983230072969 + 3 ^ 40 * 1165156 * 2
def baseEnd_1165156 : Nat := 132952236771144123442567

theorem tailTrace_1165156 : CollatzResearch.WordTrace tailWord_1165156 prefixEnd_1165156 132952236771144123442567 := by
  unfold tailWord_1165156
  simp only [CollatzResearch.WordTrace]
  refine ⟨21248365283423139823641661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28331153711230853098188881 21248365283423139823641661)
  ·
    refine ⟨7968136981283677433865623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21248365283423139823641661 7968136981283677433865623)
    ·
      refine ⟨11952205471925516150798435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7968136981283677433865623 11952205471925516150798435)
      ·
        refine ⟨17928308207888274226197653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11952205471925516150798435 17928308207888274226197653)
        ·
          refine ⟨840389447244762854353015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17928308207888274226197653 840389447244762854353015)
          ·
            refine ⟨1260584170867144281529523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840389447244762854353015 1260584170867144281529523)
            ·
              refine ⟨1890876256300716422294285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1260584170867144281529523 1890876256300716422294285)
              ·
                refine ⟨709078596112768658360357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1890876256300716422294285 709078596112768658360357)
                ·
                  refine ⟨132952236771144123442567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 709078596112768658360357 132952236771144123442567)
                  ·
                    rfl

theorem cell22_1165156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_1165156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165156 prefixEnd_1165156 := by exact prefixLift 1165156
  have htrace : WordTrace (prefixWord ++ tailWord_1165156) baseStart_1165156 baseEnd_1165156 := by
    simpa [prefixWord, tailWord_1165156, baseEnd_1165156] using wordTrace_append hprefix tailTrace_1165156
  have hstable : (prefixWord ++ tailWord_1165156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165156).length < 2 ^ (prefixWord ++ tailWord_1165156).sum := by decide
  have hdescent : baseEnd_1165156 < baseStart_1165156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165163 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 1, 8]
def baseStart_1165163 : Nat := 118140960795 + 1165163 * 2 ^ 59
def prefixEnd_1165163 : Nat := 4983230072969 + 3 ^ 40 * 1165163 * 2
def baseEnd_1165163 : Nat := 398859106556486685402679

theorem tailTrace_1165163 : CollatzResearch.WordTrace tailWord_1165163 prefixEnd_1165163 398859106556486685402679 := by
  unfold tailWord_1165163
  simp only [CollatzResearch.WordTrace]
  refine ⟨42496985877820919842788143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28331323918547279895192095 42496985877820919842788143)
  ·
    refine ⟨63745478816731379764182215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42496985877820919842788143 63745478816731379764182215)
    ·
      refine ⟨95618218225097069646273323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63745478816731379764182215 95618218225097069646273323)
      ·
        refine ⟨143427327337645604469409985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95618218225097069646273323 143427327337645604469409985)
        ·
          refine ⟨107570495503234203352057489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143427327337645604469409985 107570495503234203352057489)
          ·
            refine ⟨80677871627425652514043117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107570495503234203352057489 80677871627425652514043117)
            ·
              refine ⟨30254201860284619692766169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80677871627425652514043117 30254201860284619692766169)
              ·
                refine ⟨22690651395213464769574627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30254201860284619692766169 22690651395213464769574627)
                ·
                  refine ⟨34035977092820197154361941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22690651395213464769574627 34035977092820197154361941)
                  ·
                    refine ⟨398859106556486685402679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34035977092820197154361941 398859106556486685402679)
                    ·
                      rfl

theorem cell22_1165163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 8].length) (baseStart_1165163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165163 prefixEnd_1165163 := by exact prefixLift 1165163
  have htrace : WordTrace (prefixWord ++ tailWord_1165163) baseStart_1165163 baseEnd_1165163 := by
    simpa [prefixWord, tailWord_1165163, baseEnd_1165163] using wordTrace_append hprefix tailTrace_1165163
  have hstable : (prefixWord ++ tailWord_1165163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165163).length < 2 ^ (prefixWord ++ tailWord_1165163).sum := by decide
  have hdescent : baseEnd_1165163 < baseStart_1165163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165233 : List Nat := [1, 2, 2, 4, 2, 3, 2, 2, 1, 3]
def baseStart_1165233 : Nat := 118140960795 + 1165233 * 2 ^ 59
def prefixEnd_1165233 : Nat := 4983230072969 + 3 ^ 40 * 1165233 * 2
def baseEnd_1165233 : Nat := 398883068987029836152465

theorem tailTrace_1165233 : CollatzResearch.WordTrace tailWord_1165233 prefixEnd_1165233 398883068987029836152465 := by
  unfold tailWord_1165233
  simp only [CollatzResearch.WordTrace]
  refine ⟨42499538987567321797836353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28333025991711547865224235 42499538987567321797836353)
  ·
    refine ⟨31874654240675491348377265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42499538987567321797836353 31874654240675491348377265)
    ·
      refine ⟨23905990680506618511282949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31874654240675491348377265 23905990680506618511282949)
      ·
        refine ⟨4482373252594990970865553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23905990680506618511282949 4482373252594990970865553)
        ·
          refine ⟨3361779939446243228149165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4482373252594990970865553 3361779939446243228149165)
          ·
            refine ⟨1260667477292341210555937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3361779939446243228149165 1260667477292341210555937)
            ·
              refine ⟨945500607969255907916953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1260667477292341210555937 945500607969255907916953)
              ·
                refine ⟨709125455976941930937715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 945500607969255907916953 709125455976941930937715)
                ·
                  refine ⟨1063688183965412896406573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 709125455976941930937715 1063688183965412896406573)
                  ·
                    refine ⟨398883068987029836152465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1063688183965412896406573 398883068987029836152465)
                    ·
                      rfl

theorem cell22_1165233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 1, 3].length) (baseStart_1165233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165233 prefixEnd_1165233 := by exact prefixLift 1165233
  have htrace : WordTrace (prefixWord ++ tailWord_1165233) baseStart_1165233 baseEnd_1165233 := by
    simpa [prefixWord, tailWord_1165233, baseEnd_1165233] using wordTrace_append hprefix tailTrace_1165233
  have hstable : (prefixWord ++ tailWord_1165233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165233).length < 2 ^ (prefixWord ++ tailWord_1165233).sum := by decide
  have hdescent : baseEnd_1165233 < baseStart_1165233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165240 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 6]
def baseStart_1165240 : Nat := 118140960795 + 1165240 * 2 ^ 59
def prefixEnd_1165240 : Nat := 4983230072969 + 3 ^ 40 * 1165240 * 2
def baseEnd_1165240 : Nat := 132961821743361383742481

theorem tailTrace_1165240 : CollatzResearch.WordTrace tailWord_1165240 prefixEnd_1165240 132961821743361383742481 := by
  unfold tailWord_1165240
  simp only [CollatzResearch.WordTrace]
  refine ⟨21249897149270980996670587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28333196199027974662227449 21249897149270980996670587)
  ·
    refine ⟨31874845723906471495005881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21249897149270980996670587 31874845723906471495005881)
    ·
      refine ⟨23906134292929853621254411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31874845723906471495005881 23906134292929853621254411)
      ·
        refine ⟨35859201439394780431881617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23906134292929853621254411 35859201439394780431881617)
        ·
          refine ⟨26894401079546085323911213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35859201439394780431881617 26894401079546085323911213)
          ·
            refine ⟨10085400404829781996466705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26894401079546085323911213 10085400404829781996466705)
            ·
              refine ⟨7564050303622336497350029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10085400404829781996466705 7564050303622336497350029)
              ·
                refine ⟨2836518863858376186506261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7564050303622336497350029 2836518863858376186506261)
                ·
                  refine ⟨132961821743361383742481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2836518863858376186506261 132961821743361383742481)
                  ·
                    rfl

theorem cell22_1165240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 6].length) (baseStart_1165240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165240 prefixEnd_1165240 := by exact prefixLift 1165240
  have htrace : WordTrace (prefixWord ++ tailWord_1165240) baseStart_1165240 baseEnd_1165240 := by
    simpa [prefixWord, tailWord_1165240, baseEnd_1165240] using wordTrace_append hprefix tailTrace_1165240
  have hstable : (prefixWord ++ tailWord_1165240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165240).length < 2 ^ (prefixWord ++ tailWord_1165240).sum := by decide
  have hdescent : baseEnd_1165240 < baseStart_1165240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165244 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 2, 5]
def baseStart_1165244 : Nat := 118140960795 + 1165244 * 2 ^ 59
def prefixEnd_1165244 : Nat := 4983230072969 + 3 ^ 40 * 1165244 * 2
def baseEnd_1165244 : Nat := 398886834511829474127431

theorem tailTrace_1165244 : CollatzResearch.WordTrace tailWord_1165244 prefixEnd_1165244 398886834511829474127431 := by
  unfold tailWord_1165244
  simp only [CollatzResearch.WordTrace]
  refine ⟨21249970095263735338243393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28333293460351647117657857 21249970095263735338243393)
  ·
    refine ⟨15937477571447801503682545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21249970095263735338243393 15937477571447801503682545)
    ·
      refine ⟨11953108178585851127761909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15937477571447801503682545 11953108178585851127761909)
      ·
        refine ⟨1120603891742423543227679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11953108178585851127761909 1120603891742423543227679)
        ·
          refine ⟨1680905837613635314841519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1120603891742423543227679 1680905837613635314841519)
          ·
            refine ⟨2521358756420452972262279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1680905837613635314841519 2521358756420452972262279)
            ·
              refine ⟨3782038134630679458393419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2521358756420452972262279 3782038134630679458393419)
              ·
                refine ⟨5673057201946019187590129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3782038134630679458393419 5673057201946019187590129)
                ·
                  refine ⟨4254792901459514390692597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5673057201946019187590129 4254792901459514390692597)
                  ·
                    refine ⟨398886834511829474127431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4254792901459514390692597 398886834511829474127431)
                    ·
                      rfl

theorem cell22_1165244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_1165244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165244 prefixEnd_1165244 := by exact prefixLift 1165244
  have htrace : WordTrace (prefixWord ++ tailWord_1165244) baseStart_1165244 baseEnd_1165244 := by
    simpa [prefixWord, tailWord_1165244, baseEnd_1165244] using wordTrace_append hprefix tailTrace_1165244
  have hstable : (prefixWord ++ tailWord_1165244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165244).length < 2 ^ (prefixWord ++ tailWord_1165244).sum := by decide
  have hdescent : baseEnd_1165244 < baseStart_1165244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165272 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 4, 3]
def baseStart_1165272 : Nat := 118140960795 + 1165272 * 2 ^ 59
def prefixEnd_1165272 : Nat := 4983230072969 + 3 ^ 40 * 1165272 * 2
def baseEnd_1165272 : Nat := 398896419484046734427345

theorem tailTrace_1165272 : CollatzResearch.WordTrace tailWord_1165272 prefixEnd_1165272 398896419484046734427345 := by
  unfold tailWord_1165272
  simp only [CollatzResearch.WordTrace]
  refine ⟨21250480717213015729253035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28333974289617354305670713 21250480717213015729253035)
  ·
    refine ⟨31875721075819523593879553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21250480717213015729253035 31875721075819523593879553)
    ·
      refine ⟨23906790806864642695409665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31875721075819523593879553 23906790806864642695409665)
      ·
        refine ⟨17930093105148482021557249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23906790806864642695409665 17930093105148482021557249)
        ·
          refine ⟨13447569828861361516167937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17930093105148482021557249 13447569828861361516167937)
          ·
            refine ⟨10085677371646021137125953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13447569828861361516167937 10085677371646021137125953)
            ·
              refine ⟨7564258028734515852844465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10085677371646021137125953 7564258028734515852844465)
              ·
                refine ⟨5673193521550886889633349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7564258028734515852844465 5673193521550886889633349)
                ·
                  refine ⟨1063723785290791291806253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5673193521550886889633349 1063723785290791291806253)
                  ·
                    refine ⟨398896419484046734427345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1063723785290791291806253 398896419484046734427345)
                    ·
                      rfl

theorem cell22_1165272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_1165272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165272 prefixEnd_1165272 := by exact prefixLift 1165272
  have htrace : WordTrace (prefixWord ++ tailWord_1165272) baseStart_1165272 baseEnd_1165272 := by
    simpa [prefixWord, tailWord_1165272, baseEnd_1165272] using wordTrace_append hprefix tailTrace_1165272
  have hstable : (prefixWord ++ tailWord_1165272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165272).length < 2 ^ (prefixWord ++ tailWord_1165272).sum := by decide
  have hdescent : baseEnd_1165272 < baseStart_1165272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165315 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 2, 6]
def baseStart_1165315 : Nat := 118140960795 + 1165315 * 2 ^ 59
def prefixEnd_1165315 : Nat := 4983230072969 + 3 ^ 40 * 1165315 * 2
def baseEnd_1165315 : Nat := 398911139262808955602213

theorem tailTrace_1165315 : CollatzResearch.WordTrace tailWord_1165315 prefixEnd_1165315 398911139262808955602213 := by
  unfold tailWord_1165315
  simp only [CollatzResearch.WordTrace]
  refine ⟨42502529773270249802321399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28335019848846833201547599 42502529773270249802321399)
  ·
    refine ⟨63753794659905374703482099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42502529773270249802321399 63753794659905374703482099)
    ·
      refine ⟨95630691989858062055223149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63753794659905374703482099 95630691989858062055223149)
      ·
        refine ⟨35861509496196773270708681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95630691989858062055223149 35861509496196773270708681)
        ·
          refine ⟨26896132122147579953031511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35861509496196773270708681 26896132122147579953031511)
          ·
            refine ⟨40344198183221369929547267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26896132122147579953031511 40344198183221369929547267)
            ·
              refine ⟨60516297274832054894320901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40344198183221369929547267 60516297274832054894320901)
              ·
                refine ⟨11346805739031010292685169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60516297274832054894320901 11346805739031010292685169)
                ·
                  refine ⟨8510104304273257719513877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11346805739031010292685169 8510104304273257719513877)
                  ·
                    refine ⟨398911139262808955602213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8510104304273257719513877 398911139262808955602213)
                    ·
                      rfl

theorem cell22_1165315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 6].length) (baseStart_1165315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165315 prefixEnd_1165315 := by exact prefixLift 1165315
  have htrace : WordTrace (prefixWord ++ tailWord_1165315) baseStart_1165315 baseEnd_1165315 := by
    simpa [prefixWord, tailWord_1165315, baseEnd_1165315] using wordTrace_append hprefix tailTrace_1165315
  have hstable : (prefixWord ++ tailWord_1165315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165315).length < 2 ^ (prefixWord ++ tailWord_1165315).sum := by decide
  have hdescent : baseEnd_1165315 < baseStart_1165315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165319 : List Nat := [1, 1, 4, 3, 1, 4, 2, 6]
def baseStart_1165319 : Nat := 118140960795 + 1165319 * 2 ^ 59
def prefixEnd_1165319 : Nat := 4983230072969 + 3 ^ 40 * 1165319 * 2
def baseEnd_1165319 : Nat := 44323612060506030944689

theorem tailTrace_1165319 : CollatzResearch.WordTrace tailWord_1165319 prefixEnd_1165319 44323612060506030944689 := by
  unfold tailWord_1165319
  simp only [CollatzResearch.WordTrace]
  refine ⟨42502675665255758485467011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28335117110170505656978007 42502675665255758485467011)
  ·
    refine ⟨63754013497883637728200517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42502675665255758485467011 63754013497883637728200517)
    ·
      refine ⟨11953877530853182074037597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63754013497883637728200517 11953877530853182074037597)
      ·
        refine ⟨4482704074069943277764099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11953877530853182074037597 4482704074069943277764099)
        ·
          refine ⟨6724056111104914916646149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4482704074069943277764099 6724056111104914916646149)
          ·
            refine ⟨1260760520832171546871153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6724056111104914916646149 1260760520832171546871153)
            ·
              refine ⟨945570390624128660153365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1260760520832171546871153 945570390624128660153365)
              ·
                refine ⟨44323612060506030944689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 945570390624128660153365 44323612060506030944689)
                ·
                  rfl

theorem cell22_1165319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 6].length) (baseStart_1165319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165319 prefixEnd_1165319 := by exact prefixLift 1165319
  have htrace : WordTrace (prefixWord ++ tailWord_1165319) baseStart_1165319 baseEnd_1165319 := by
    simpa [prefixWord, tailWord_1165319, baseEnd_1165319] using wordTrace_append hprefix tailTrace_1165319
  have hstable : (prefixWord ++ tailWord_1165319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165319).length < 2 ^ (prefixWord ++ tailWord_1165319).sum := by decide
  have hdescent : baseEnd_1165319 < baseStart_1165319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165347 : List Nat := [1, 1, 1, 4, 3, 1, 2, 4, 5]
def baseStart_1165347 : Nat := 118140960795 + 1165347 * 2 ^ 59
def prefixEnd_1165347 : Nat := 4983230072969 + 3 ^ 40 * 1165347 * 2
def baseEnd_1165347 : Nat := 132974031172257179600705

theorem tailTrace_1165347 : CollatzResearch.WordTrace tailWord_1165347 prefixEnd_1165347 132974031172257179600705 := by
  unfold tailWord_1165347
  simp only [CollatzResearch.WordTrace]
  refine ⟨42503696909154319267486295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28335797939436212844990863 42503696909154319267486295)
  ·
    refine ⟨63755545363731478901229443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42503696909154319267486295 63755545363731478901229443)
    ·
      refine ⟨95633318045597218351844165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63755545363731478901229443 95633318045597218351844165)
      ·
        refine ⟨17931247133549478440970781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95633318045597218351844165 17931247133549478440970781)
        ·
          refine ⟨6724217675081054415364043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17931247133549478440970781 6724217675081054415364043)
          ·
            refine ⟨10086326512621581623046065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6724217675081054415364043 10086326512621581623046065)
            ·
              refine ⟨7564744884466186217284549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10086326512621581623046065 7564744884466186217284549)
              ·
                refine ⟨1418389665837409915740853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7564744884466186217284549 1418389665837409915740853)
                ·
                  refine ⟨132974031172257179600705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1418389665837409915740853 132974031172257179600705)
                  ·
                    rfl

theorem cell22_1165347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 5].length) (baseStart_1165347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165347 prefixEnd_1165347 := by exact prefixLift 1165347
  have htrace : WordTrace (prefixWord ++ tailWord_1165347) baseStart_1165347 baseEnd_1165347 := by
    simpa [prefixWord, tailWord_1165347, baseEnd_1165347] using wordTrace_append hprefix tailTrace_1165347
  have hstable : (prefixWord ++ tailWord_1165347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165347).length < 2 ^ (prefixWord ++ tailWord_1165347).sum := by decide
  have hdescent : baseEnd_1165347 < baseStart_1165347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165398 : List Nat := [5, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_1165398 : Nat := 118140960795 + 1165398 * 2 ^ 59
def prefixEnd_1165398 : Nat := 4983230072969 + 3 ^ 40 * 1165398 * 2
def baseEnd_1165398 : Nat := 132979850619674801925653

theorem tailTrace_1165398 : CollatzResearch.WordTrace tailWord_1165398 prefixEnd_1165398 132979850619674801925653 := by
  unfold tailWord_1165398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2656597314498097186099553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28337038021313036651728565 2656597314498097186099553)
  ·
    refine ⟨1992447985873572889574665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2656597314498097186099553 1992447985873572889574665)
    ·
      refine ⟨1494335989405179667180999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1992447985873572889574665 1494335989405179667180999)
      ·
        refine ⟨2241503984107769500771499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1494335989405179667180999 2241503984107769500771499)
        ·
          refine ⟨3362255976161654251157249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2241503984107769500771499 3362255976161654251157249)
          ·
            refine ⟨2521691982121240688367937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3362255976161654251157249 2521691982121240688367937)
            ·
              refine ⟨1891268986590930516275953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2521691982121240688367937 1891268986590930516275953)
              ·
                refine ⟨1418451739943197887206965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1891268986590930516275953 1418451739943197887206965)
                ·
                  refine ⟨132979850619674801925653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1418451739943197887206965 132979850619674801925653)
                  ·
                    rfl

theorem cell22_1165398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_1165398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165398 prefixEnd_1165398 := by exact prefixLift 1165398
  have htrace : WordTrace (prefixWord ++ tailWord_1165398) baseStart_1165398 baseEnd_1165398 := by
    simpa [prefixWord, tailWord_1165398, baseEnd_1165398] using wordTrace_append hprefix tailTrace_1165398
  have hstable : (prefixWord ++ tailWord_1165398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165398).length < 2 ^ (prefixWord ++ tailWord_1165398).sum := by decide
  have hdescent : baseEnd_1165398 < baseStart_1165398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165424 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 1, 5]
def baseStart_1165424 : Nat := 118140960795 + 1165424 * 2 ^ 59
def prefixEnd_1165424 : Nat := 4983230072969 + 3 ^ 40 * 1165424 * 2
def baseEnd_1165424 : Nat := 398948452190369004626879

theorem tailTrace_1165424 : CollatzResearch.WordTrace tailWord_1165424 prefixEnd_1165424 398948452190369004626879 := by
  unfold tailWord_1165424
  simp only [CollatzResearch.WordTrace]
  refine ⟨21253252664937680709019663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28337670219916907612026217 21253252664937680709019663)
  ·
    refine ⟨31879878997406521063529495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21253252664937680709019663 31879878997406521063529495)
    ·
      refine ⟨47819818496109781595294243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31879878997406521063529495 47819818496109781595294243)
      ·
        refine ⟨71729727744164672392941365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47819818496109781595294243 71729727744164672392941365)
        ·
          refine ⟨6724661976015438036838253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71729727744164672392941365 6724661976015438036838253)
          ·
            refine ⟨2521748241005789263814345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6724661976015438036838253 2521748241005789263814345)
            ·
              refine ⟨1891311180754341947860759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2521748241005789263814345 1891311180754341947860759)
              ·
                refine ⟨2836966771131512921791139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1891311180754341947860759 2836966771131512921791139)
                ·
                  refine ⟨4255450156697269382686709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2836966771131512921791139 4255450156697269382686709)
                  ·
                    refine ⟨398948452190369004626879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4255450156697269382686709 398948452190369004626879)
                    ·
                      rfl

theorem cell22_1165424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 1, 5].length) (baseStart_1165424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165424 prefixEnd_1165424 := by exact prefixLift 1165424
  have htrace : WordTrace (prefixWord ++ tailWord_1165424) baseStart_1165424 baseEnd_1165424 := by
    simpa [prefixWord, tailWord_1165424, baseEnd_1165424] using wordTrace_append hprefix tailTrace_1165424
  have hstable : (prefixWord ++ tailWord_1165424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165424).length < 2 ^ (prefixWord ++ tailWord_1165424).sum := by decide
  have hdescent : baseEnd_1165424 < baseStart_1165424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165454 : List Nat := [4, 1, 1, 3, 3, 1, 9]
def baseStart_1165454 : Nat := 118140960795 + 1165454 * 2 ^ 59
def prefixEnd_1165454 : Nat := 4983230072969 + 3 ^ 40 * 1165454 * 2
def baseEnd_1165454 : Nat := 14776248955683663939881

theorem tailTrace_1165454 : CollatzResearch.WordTrace tailWord_1165454 prefixEnd_1165454 14776248955683663939881 := by
  unfold tailWord_1165454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5313449939970834567703927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28338399679844451027754277 5313449939970834567703927)
  ·
    refine ⟨7970174909956251851555891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5313449939970834567703927 7970174909956251851555891)
    ·
      refine ⟨11955262364934377777333837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7970174909956251851555891 11955262364934377777333837)
      ·
        refine ⟨4483223386850391666500189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11955262364934377777333837 4483223386850391666500189)
        ·
          refine ⟨1681208770068896874937571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4483223386850391666500189 1681208770068896874937571)
          ·
            refine ⟨2521813155103345312406357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1681208770068896874937571 2521813155103345312406357)
            ·
              refine ⟨14776248955683663939881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2521813155103345312406357 14776248955683663939881)
              ·
                rfl

theorem cell22_1165454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 9].length) (baseStart_1165454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165454 prefixEnd_1165454 := by exact prefixLift 1165454
  have htrace : WordTrace (prefixWord ++ tailWord_1165454) baseStart_1165454 baseEnd_1165454 := by
    simpa [prefixWord, tailWord_1165454, baseEnd_1165454] using wordTrace_append hprefix tailTrace_1165454
  have hstable : (prefixWord ++ tailWord_1165454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165454).length < 2 ^ (prefixWord ++ tailWord_1165454).sum := by decide
  have hdescent : baseEnd_1165454 < baseStart_1165454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165533 : List Nat := [1, 4, 3, 2, 1, 1, 4, 1, 5]
def baseStart_1165533 : Nat := 118140960795 + 1165533 * 2 ^ 59
def prefixEnd_1165533 : Nat := 4983230072969 + 3 ^ 40 * 1165533 * 2
def baseEnd_1165533 : Nat := 132995255039309684550515

theorem tailTrace_1165533 : CollatzResearch.WordTrace tailWord_1165533 prefixEnd_1165533 132995255039309684550515 := by
  unfold tailWord_1165533
  simp only [CollatzResearch.WordTrace]
  refine ⟨42510480886480473033757253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28340320590986982022504835 42510480886480473033757253)
  ·
    refine ⟨7970715166215088693829485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42510480886480473033757253 7970715166215088693829485)
    ·
      refine ⟨2989018187330658260186057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7970715166215088693829485 2989018187330658260186057)
      ·
        refine ⟨2241763640497993695139543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2989018187330658260186057 2241763640497993695139543)
        ·
          refine ⟨3362645460746990542709315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2241763640497993695139543 3362645460746990542709315)
          ·
            refine ⟨5043968191120485814063973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3362645460746990542709315 5043968191120485814063973)
            ·
              refine ⟨945744035835091090136995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5043968191120485814063973 945744035835091090136995)
              ·
                refine ⟨1418616053752636635205493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945744035835091090136995 1418616053752636635205493)
                ·
                  refine ⟨132995255039309684550515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1418616053752636635205493 132995255039309684550515)
                  ·
                    rfl

theorem cell22_1165533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_1165533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165533 prefixEnd_1165533 := by exact prefixLift 1165533
  have htrace : WordTrace (prefixWord ++ tailWord_1165533) baseStart_1165533 baseEnd_1165533 := by
    simpa [prefixWord, tailWord_1165533, baseEnd_1165533] using wordTrace_append hprefix tailTrace_1165533
  have hstable : (prefixWord ++ tailWord_1165533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165533).length < 2 ^ (prefixWord ++ tailWord_1165533).sum := by decide
  have hdescent : baseEnd_1165533 < baseStart_1165533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165578 : List Nat := [3, 1, 2, 2, 1, 1, 6, 2, 4]
def baseStart_1165578 : Nat := 118140960795 + 1165578 * 2 ^ 59
def prefixEnd_1165578 : Nat := 4983230072969 + 3 ^ 40 * 1165578 * 2
def baseEnd_1165578 : Nat := 133000389845854645425469

theorem tailTrace_1165578 : CollatzResearch.WordTrace tailWord_1165578 prefixEnd_1165578 133000389845854645425469 := by
  unfold tailWord_1165578
  simp only [CollatzResearch.WordTrace]
  refine ⟨10628030542829361429786347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28341414780878297146096925 10628030542829361429786347)
  ·
    refine ⟨15942045814244042144679521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10628030542829361429786347 15942045814244042144679521)
    ·
      refine ⟨11956534360683031608509641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15942045814244042144679521 11956534360683031608509641)
      ·
        refine ⟨8967400770512273706382231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11956534360683031608509641 8967400770512273706382231)
        ·
          refine ⟨13451101155768410559573347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8967400770512273706382231 13451101155768410559573347)
          ·
            refine ⟨20176651733652615839360021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13451101155768410559573347 20176651733652615839360021)
            ·
              refine ⟨945780550014966367470001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20176651733652615839360021 945780550014966367470001)
              ·
                refine ⟨709335412511224775602501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 945780550014966367470001 709335412511224775602501)
                ·
                  refine ⟨133000389845854645425469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 709335412511224775602501 133000389845854645425469)
                  ·
                    rfl

theorem cell22_1165578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_1165578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165578 prefixEnd_1165578 := by exact prefixLift 1165578
  have htrace : WordTrace (prefixWord ++ tailWord_1165578) baseStart_1165578 baseEnd_1165578 := by
    simpa [prefixWord, tailWord_1165578, baseEnd_1165578] using wordTrace_append hprefix tailTrace_1165578
  have hstable : (prefixWord ++ tailWord_1165578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165578).length < 2 ^ (prefixWord ++ tailWord_1165578).sum := by decide
  have hdescent : baseEnd_1165578 < baseStart_1165578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165589 : List Nat := [1, 3, 2, 1, 2, 1, 5, 7]
def baseStart_1165589 : Nat := 118140960795 + 1165589 * 2 ^ 59
def prefixEnd_1165589 : Nat := 4983230072969 + 3 ^ 40 * 1165589 * 2
def baseEnd_1165589 : Nat := 44333881673595952694597

theorem tailTrace_1165589 : CollatzResearch.WordTrace tailWord_1165589 prefixEnd_1165589 44333881673595952694597 := by
  unfold tailWord_1165589
  simp only [CollatzResearch.WordTrace]
  refine ⟨42512523374277594597795821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28341682249518396398530547 42512523374277594597795821)
  ·
    refine ⟨15942196265354097974173433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42512523374277594597795821 15942196265354097974173433)
    ·
      refine ⟨11956647199015573480630075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15942196265354097974173433 11956647199015573480630075)
      ·
        refine ⟨17934970798523360220945113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11956647199015573480630075 17934970798523360220945113)
        ·
          refine ⟨13451228098892520165708835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17934970798523360220945113 13451228098892520165708835)
          ·
            refine ⟨20176842148338780248563253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13451228098892520165708835 20176842148338780248563253)
            ·
              refine ⟨1891578951406760648302805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20176842148338780248563253 1891578951406760648302805)
              ·
                refine ⟨44333881673595952694597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1891578951406760648302805 44333881673595952694597)
                ·
                  rfl

theorem cell22_1165589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 7].length) (baseStart_1165589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165589 prefixEnd_1165589 := by exact prefixLift 1165589
  have htrace : WordTrace (prefixWord ++ tailWord_1165589) baseStart_1165589 baseEnd_1165589 := by
    simpa [prefixWord, tailWord_1165589, baseEnd_1165589] using wordTrace_append hprefix tailTrace_1165589
  have hstable : (prefixWord ++ tailWord_1165589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165589).length < 2 ^ (prefixWord ++ tailWord_1165589).sum := by decide
  have hdescent : baseEnd_1165589 < baseStart_1165589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165614 : List Nat := [4, 1, 3, 3, 2, 1, 2, 1, 1, 4]
def baseStart_1165614 : Nat := 118140960795 + 1165614 * 2 ^ 59
def prefixEnd_1165614 : Nat := 4983230072969 + 3 ^ 40 * 1165614 * 2
def baseEnd_1165614 : Nat := 399013493073271842376297

theorem tailTrace_1165614 : CollatzResearch.WordTrace tailWord_1165614 prefixEnd_1165614 399013493073271842376297 := by
  unfold tailWord_1165614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5314179399898377983431987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28342290132791349244970597 5314179399898377983431987)
  ·
    refine ⟨7971269099847566975147981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5314179399898377983431987 7971269099847566975147981)
    ·
      refine ⟨2989225912442837615680493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7971269099847566975147981 2989225912442837615680493)
      ·
        refine ⟨1120959717166064105880185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2989225912442837615680493 1120959717166064105880185)
        ·
          refine ⟨840719787874548079410139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1120959717166064105880185 840719787874548079410139)
          ·
            refine ⟨1261079681811822119115209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840719787874548079410139 1261079681811822119115209)
            ·
              refine ⟨945809761358866589336407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1261079681811822119115209 945809761358866589336407)
              ·
                refine ⟨1418714642038299884004611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945809761358866589336407 1418714642038299884004611)
                ·
                  refine ⟨2128071963057449826006917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418714642038299884004611 2128071963057449826006917)
                  ·
                    refine ⟨399013493073271842376297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2128071963057449826006917 399013493073271842376297)
                    ·
                      rfl

theorem cell22_1165614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_1165614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165614 prefixEnd_1165614 := by exact prefixLift 1165614
  have htrace : WordTrace (prefixWord ++ tailWord_1165614) baseStart_1165614 baseEnd_1165614 := by
    simpa [prefixWord, tailWord_1165614, baseEnd_1165614] using wordTrace_append hprefix tailTrace_1165614
  have hstable : (prefixWord ++ tailWord_1165614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165614).length < 2 ^ (prefixWord ++ tailWord_1165614).sum := by decide
  have hdescent : baseEnd_1165614 < baseStart_1165614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165621 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 5, 3]
def baseStart_1165621 : Nat := 118140960795 + 1165621 * 2 ^ 59
def prefixEnd_1165621 : Nat := 4983230072969 + 3 ^ 40 * 1165621 * 2
def baseEnd_1165621 : Nat := 399015889316326157451275

theorem tailTrace_1165621 : CollatzResearch.WordTrace tailWord_1165621 prefixEnd_1165621 399015889316326157451275 := by
  unfold tailWord_1165621
  simp only [CollatzResearch.WordTrace]
  refine ⟨42513690510161664062960717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28342460340107776041973811 42513690510161664062960717)
  ·
    refine ⟨15942633941310624023610269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42513690510161664062960717 15942633941310624023610269)
    ·
      refine ⟨5978487727991484008853851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15942633941310624023610269 5978487727991484008853851)
      ·
        refine ⟨8967731591987226013280777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5978487727991484008853851 8967731591987226013280777)
        ·
          refine ⟨6725798693990419509960583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8967731591987226013280777 6725798693990419509960583)
          ·
            refine ⟨10088698040985629264940875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6725798693990419509960583 10088698040985629264940875)
            ·
              refine ⟨15133047061478443897411313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10088698040985629264940875 15133047061478443897411313)
              ·
                refine ⟨11349785296108832923058485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15133047061478443897411313 11349785296108832923058485)
                ·
                  refine ⟨1064042371510203086536733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11349785296108832923058485 1064042371510203086536733)
                  ·
                    refine ⟨399015889316326157451275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1064042371510203086536733 399015889316326157451275)
                    ·
                      rfl

theorem cell22_1165621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_1165621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165621 prefixEnd_1165621 := by exact prefixLift 1165621
  have htrace : WordTrace (prefixWord ++ tailWord_1165621) baseStart_1165621 baseEnd_1165621 := by
    simpa [prefixWord, tailWord_1165621, baseEnd_1165621] using wordTrace_append hprefix tailTrace_1165621
  have hstable : (prefixWord ++ tailWord_1165621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165621).length < 2 ^ (prefixWord ++ tailWord_1165621).sum := by decide
  have hdescent : baseEnd_1165621 < baseStart_1165621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165672 : List Nat := [2, 1, 4, 2, 2, 3, 1, 3, 1, 3]
def baseStart_1165672 : Nat := 118140960795 + 1165672 * 2 ^ 59
def prefixEnd_1165672 : Nat := 4983230072969 + 3 ^ 40 * 1165672 * 2
def baseEnd_1165672 : Nat := 399033347658579024426119

theorem tailTrace_1165672 : CollatzResearch.WordTrace tailWord_1165672 prefixEnd_1165672 399033347658579024426119 := by
  unfold tailWord_1165672
  simp only [CollatzResearch.WordTrace]
  refine ⟨21257775316488449886533635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28343700421984599848711513 21257775316488449886533635)
  ·
    refine ⟨31886662974732674829800453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21257775316488449886533635 31886662974732674829800453)
    ·
      refine ⟨5978749307762376530587585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31886662974732674829800453 5978749307762376530587585)
      ·
        refine ⟨4484061980821782397940689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5978749307762376530587585 4484061980821782397940689)
        ·
          refine ⟨3363046485616336798455517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4484061980821782397940689 3363046485616336798455517)
          ·
            refine ⟨1261142432106126299420819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3363046485616336798455517 1261142432106126299420819)
            ·
              refine ⟨1891713648159189449131229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1261142432106126299420819 1891713648159189449131229)
              ·
                refine ⟨709392618059696043424211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1891713648159189449131229 709392618059696043424211)
                ·
                  refine ⟨1064088927089544065136317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 709392618059696043424211 1064088927089544065136317)
                  ·
                    refine ⟨399033347658579024426119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1064088927089544065136317 399033347658579024426119)
                    ·
                      rfl

theorem cell22_1165672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_1165672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165672 prefixEnd_1165672 := by exact prefixLift 1165672
  have htrace : WordTrace (prefixWord ++ tailWord_1165672) baseStart_1165672 baseEnd_1165672 := by
    simpa [prefixWord, tailWord_1165672, baseEnd_1165672] using wordTrace_append hprefix tailTrace_1165672
  have hstable : (prefixWord ++ tailWord_1165672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165672).length < 2 ^ (prefixWord ++ tailWord_1165672).sum := by decide
  have hdescent : baseEnd_1165672 < baseStart_1165672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165741 : List Nat := [1, 5, 2, 2, 12]
def baseStart_1165741 : Nat := 118140960795 + 1165741 * 2 ^ 59
def prefixEnd_1165741 : Nat := 4983230072969 + 3 ^ 40 * 1165741 * 2
def baseEnd_1165741 : Nat := 1642209743904056973049

theorem tailTrace_1165741 : CollatzResearch.WordTrace tailWord_1165741 prefixEnd_1165741 1642209743904056973049 := by
  unfold tailWord_1165741
  simp only [CollatzResearch.WordTrace]
  refine ⟨42518067269726924557329077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28345378179817949704886051 42518067269726924557329077)
  ·
    refine ⟨3986068806536899177249601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42518067269726924557329077 3986068806536899177249601)
    ·
      refine ⟨2989551604902674382937201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3986068806536899177249601 2989551604902674382937201)
      ·
        refine ⟨2242163703677005787202901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2989551604902674382937201 2242163703677005787202901)
        ·
          refine ⟨1642209743904056973049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2242163703677005787202901 1642209743904056973049)
          ·
            rfl

theorem cell22_1165741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 12].length) (baseStart_1165741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165741 prefixEnd_1165741 := by exact prefixLift 1165741
  have htrace : WordTrace (prefixWord ++ tailWord_1165741) baseStart_1165741 baseEnd_1165741 := by
    simpa [prefixWord, tailWord_1165741, baseEnd_1165741] using wordTrace_append hprefix tailTrace_1165741
  have hstable : (prefixWord ++ tailWord_1165741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165741).length < 2 ^ (prefixWord ++ tailWord_1165741).sum := by decide
  have hdescent : baseEnd_1165741 < baseStart_1165741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165745 : List Nat := [1, 2, 2, 4, 1, 3, 2, 2, 2, 3]
def baseStart_1165745 : Nat := 118140960795 + 1165745 * 2 ^ 59
def prefixEnd_1165745 : Nat := 4983230072969 + 3 ^ 40 * 1165745 * 2
def baseEnd_1165745 : Nat := 399058337050431167350895

theorem tailTrace_1165745 : CollatzResearch.WordTrace tailWord_1165745 prefixEnd_1165745 399058337050431167350895 := by
  unfold tailWord_1165745
  simp only [CollatzResearch.WordTrace]
  refine ⟨42518213161712433240474689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28345475441141622160316459 42518213161712433240474689)
  ·
    refine ⟨31888659871284324930356017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42518213161712433240474689 31888659871284324930356017)
    ·
      refine ⟨23916494903463243697767013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31888659871284324930356017 23916494903463243697767013)
      ·
        refine ⟨4484342794399358193331315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23916494903463243697767013 4484342794399358193331315)
        ·
          refine ⟨6726514191599037289996973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4484342794399358193331315 6726514191599037289996973)
          ·
            refine ⟨2522442821849638983748865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6726514191599037289996973 2522442821849638983748865)
            ·
              refine ⟨1891832116387229237811649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2522442821849638983748865 1891832116387229237811649)
              ·
                refine ⟨1418874087290421928358737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1891832116387229237811649 1418874087290421928358737)
                ·
                  refine ⟨1064155565467816446269053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1418874087290421928358737 1064155565467816446269053)
                  ·
                    refine ⟨399058337050431167350895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1064155565467816446269053 399058337050431167350895)
                    ·
                      rfl

theorem cell22_1165745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_1165745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165745 prefixEnd_1165745 := by exact prefixLift 1165745
  have htrace : WordTrace (prefixWord ++ tailWord_1165745) baseStart_1165745 baseEnd_1165745 := by
    simpa [prefixWord, tailWord_1165745, baseEnd_1165745] using wordTrace_append hprefix tailTrace_1165745
  have hstable : (prefixWord ++ tailWord_1165745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165745).length < 2 ^ (prefixWord ++ tailWord_1165745).sum := by decide
  have hdescent : baseEnd_1165745 < baseStart_1165745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165786 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 7]
def baseStart_1165786 : Nat := 118140960795 + 1165786 * 2 ^ 59
def prefixEnd_1165786 : Nat := 4983230072969 + 3 ^ 40 * 1165786 * 2
def baseEnd_1165786 : Nat := 133024124062773575691923

theorem tailTrace_1165786 : CollatzResearch.WordTrace tailWord_1165786 prefixEnd_1165786 133024124062773575691923 := by
  unfold tailWord_1165786
  simp only [CollatzResearch.WordTrace]
  refine ⟨10629927138640974310679303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28346472369709264828478141 10629927138640974310679303)
  ·
    refine ⟨15944890707961461466018955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10629927138640974310679303 15944890707961461466018955)
    ·
      refine ⟨23917336061942192199028433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15944890707961461466018955 23917336061942192199028433)
      ·
        refine ⟨17938002046456644149271325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23917336061942192199028433 17938002046456644149271325)
        ·
          refine ⟨6726750767421241555976747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17938002046456644149271325 6726750767421241555976747)
          ·
            refine ⟨10090126151131862333965121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6726750767421241555976747 10090126151131862333965121)
            ·
              refine ⟨7567594613348896750473841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10090126151131862333965121 7567594613348896750473841)
              ·
                refine ⟨5675695960011672562855381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7567594613348896750473841 5675695960011672562855381)
                ·
                  refine ⟨133024124062773575691923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5675695960011672562855381 133024124062773575691923)
                  ·
                    rfl

theorem cell22_1165786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_1165786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165786 prefixEnd_1165786 := by exact prefixLift 1165786
  have htrace : WordTrace (prefixWord ++ tailWord_1165786) baseStart_1165786 baseEnd_1165786 := by
    simpa [prefixWord, tailWord_1165786, baseEnd_1165786] using wordTrace_append hprefix tailTrace_1165786
  have hstable : (prefixWord ++ tailWord_1165786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165786).length < 2 ^ (prefixWord ++ tailWord_1165786).sum := by decide
  have hdescent : baseEnd_1165786 < baseStart_1165786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165880 : List Nat := [2, 1, 2, 1, 4, 1, 3, 3, 2, 3]
def baseStart_1165880 : Nat := 118140960795 + 1165880 * 2 ^ 59
def prefixEnd_1165880 : Nat := 4983230072969 + 3 ^ 40 * 1165880 * 2
def baseEnd_1165880 : Nat := 399104550309335815225481

theorem tailTrace_1165880 : CollatzResearch.WordTrace tailWord_1165880 prefixEnd_1165880 399104550309335815225481 := by
  unfold tailWord_1165880
  simp only [CollatzResearch.WordTrace]
  refine ⟨21261568508111675648319547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28348758010815567531092729 21261568508111675648319547)
  ·
    refine ⟨31892352762167513472479321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21261568508111675648319547 31892352762167513472479321)
    ·
      refine ⟨23919264571625635104359491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31892352762167513472479321 23919264571625635104359491)
      ·
        refine ⟨35878896857438452656539237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23919264571625635104359491 35878896857438452656539237)
        ·
          refine ⟨6727293160769709873101107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35878896857438452656539237 6727293160769709873101107)
          ·
            refine ⟨10090939741154564809651661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6727293160769709873101107 10090939741154564809651661)
            ·
              refine ⟨3784102402932961803619373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10090939741154564809651661 3784102402932961803619373)
              ·
                refine ⟨1419038401099860676357265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3784102402932961803619373 1419038401099860676357265)
                ·
                  refine ⟨1064278800824895507267949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1419038401099860676357265 1064278800824895507267949)
                  ·
                    refine ⟨399104550309335815225481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1064278800824895507267949 399104550309335815225481)
                    ·
                      rfl

theorem cell22_1165880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_1165880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165880 prefixEnd_1165880 := by exact prefixLift 1165880
  have htrace : WordTrace (prefixWord ++ tailWord_1165880) baseStart_1165880 baseEnd_1165880 := by
    simpa [prefixWord, tailWord_1165880, baseEnd_1165880] using wordTrace_append hprefix tailTrace_1165880
  have hstable : (prefixWord ++ tailWord_1165880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165880).length < 2 ^ (prefixWord ++ tailWord_1165880).sum := by decide
  have hdescent : baseEnd_1165880 < baseStart_1165880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165891 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 2, 7]
def baseStart_1165891 : Nat := 118140960795 + 1165891 * 2 ^ 59
def prefixEnd_1165891 : Nat := 4983230072969 + 3 ^ 40 * 1165891 * 2
def baseEnd_1165891 : Nat := 399108315834135453200447

theorem tailTrace_1165891 : CollatzResearch.WordTrace tailWord_1165891 prefixEnd_1165891 399108315834135453200447 := by
  unfold tailWord_1165891
  simp only [CollatzResearch.WordTrace]
  refine ⟨42523538219183500175289527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28349025479455666783526351 42523538219183500175289527)
  ·
    refine ⟨63785307328775250262934291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42523538219183500175289527 63785307328775250262934291)
    ·
      refine ⟨95677960993162875394401437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63785307328775250262934291 95677960993162875394401437)
      ·
        refine ⟨35879235372436078272900539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95677960993162875394401437 35879235372436078272900539)
        ·
          refine ⟨53818853058654117409350809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35879235372436078272900539 53818853058654117409350809)
          ·
            refine ⟨40364139793990588057013107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53818853058654117409350809 40364139793990588057013107)
            ·
              refine ⟨60546209690985882085519661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40364139793990588057013107 60546209690985882085519661)
              ·
                refine ⟨22704828634119705782069873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60546209690985882085519661 22704828634119705782069873)
                ·
                  refine ⟨17028621475589779336552405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22704828634119705782069873 17028621475589779336552405)
                  ·
                    refine ⟨399108315834135453200447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17028621475589779336552405 399108315834135453200447)
                    ·
                      rfl

theorem cell22_1165891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 7].length) (baseStart_1165891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165891 prefixEnd_1165891 := by exact prefixLift 1165891
  have htrace : WordTrace (prefixWord ++ tailWord_1165891) baseStart_1165891 baseEnd_1165891 := by
    simpa [prefixWord, tailWord_1165891, baseEnd_1165891] using wordTrace_append hprefix tailTrace_1165891
  have hstable : (prefixWord ++ tailWord_1165891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165891).length < 2 ^ (prefixWord ++ tailWord_1165891).sum := by decide
  have hdescent : baseEnd_1165891 < baseStart_1165891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165895 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 2, 4]
def baseStart_1165895 : Nat := 118140960795 + 1165895 * 2 ^ 59
def prefixEnd_1165895 : Nat := 4983230072969 + 3 ^ 40 * 1165895 * 2
def baseEnd_1165895 : Nat := 399109685115880776100435

theorem tailTrace_1165895 : CollatzResearch.WordTrace tailWord_1165895 prefixEnd_1165895 399109685115880776100435 := by
  unfold tailWord_1165895
  simp only [CollatzResearch.WordTrace]
  refine ⟨42523684111169008858435139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28349122740779339238956759 42523684111169008858435139)
  ·
    refine ⟨63785526166753513287652709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42523684111169008858435139 63785526166753513287652709)
    ·
      refine ⟨11959786156266283741434883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63785526166753513287652709 11959786156266283741434883)
      ·
        refine ⟨17939679234399425612152325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11959786156266283741434883 17939679234399425612152325)
        ·
          refine ⟨3363689856449892302278561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17939679234399425612152325 3363689856449892302278561)
          ·
            refine ⟨2522767392337419226708921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3363689856449892302278561 2522767392337419226708921)
            ·
              refine ⟨1892075544253064420031691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2522767392337419226708921 1892075544253064420031691)
              ·
                refine ⟨2838113316379596630047537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1892075544253064420031691 2838113316379596630047537)
                ·
                  refine ⟨2128584987284697472535653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2838113316379596630047537 2128584987284697472535653)
                  ·
                    refine ⟨399109685115880776100435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2128584987284697472535653 399109685115880776100435)
                    ·
                      rfl

theorem cell22_1165895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_1165895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165895 prefixEnd_1165895 := by exact prefixLift 1165895
  have htrace : WordTrace (prefixWord ++ tailWord_1165895) baseStart_1165895 baseEnd_1165895 := by
    simpa [prefixWord, tailWord_1165895, baseEnd_1165895] using wordTrace_append hprefix tailTrace_1165895
  have hstable : (prefixWord ++ tailWord_1165895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165895).length < 2 ^ (prefixWord ++ tailWord_1165895).sum := by decide
  have hdescent : baseEnd_1165895 < baseStart_1165895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165916 : List Nat := [2, 2, 4, 1, 4, 1, 2, 2, 4]
def baseStart_1165916 : Nat := 118140960795 + 1165916 * 2 ^ 59
def prefixEnd_1165916 : Nat := 4983230072969 + 3 ^ 40 * 1165916 * 2
def baseEnd_1165916 : Nat := 133038957948347907108457

theorem tailTrace_1165916 : CollatzResearch.WordTrace tailWord_1165916 prefixEnd_1165916 133038957948347907108457 := by
  unfold tailWord_1165916
  simp only [CollatzResearch.WordTrace]
  refine ⟨21262225022046464722474801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28349633362728619629966401 21262225022046464722474801)
  ·
    refine ⟨15946668766534848541856101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21262225022046464722474801 15946668766534848541856101)
    ·
      refine ⟨2990000393725284101598019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15946668766534848541856101 2990000393725284101598019)
      ·
        refine ⟨4485000590587926152397029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2990000393725284101598019 4485000590587926152397029)
        ·
          refine ⟨840937610735236153574443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4485000590587926152397029 840937610735236153574443)
          ·
            refine ⟨1261406416102854230361665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 840937610735236153574443 1261406416102854230361665)
            ·
              refine ⟨946054812077140672771249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1261406416102854230361665 946054812077140672771249)
              ·
                refine ⟨709541109057855504578437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 946054812077140672771249 709541109057855504578437)
                ·
                  refine ⟨133038957948347907108457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 709541109057855504578437 133038957948347907108457)
                  ·
                    rfl

theorem cell22_1165916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_1165916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165916 prefixEnd_1165916 := by exact prefixLift 1165916
  have htrace : WordTrace (prefixWord ++ tailWord_1165916) baseStart_1165916 baseEnd_1165916 := by
    simpa [prefixWord, tailWord_1165916, baseEnd_1165916] using wordTrace_append hprefix tailTrace_1165916
  have hstable : (prefixWord ++ tailWord_1165916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165916).length < 2 ^ (prefixWord ++ tailWord_1165916).sum := by decide
  have hdescent : baseEnd_1165916 < baseStart_1165916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165953 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1165953 : Nat := 118140960795 + 1165953 * 2 ^ 59
def prefixEnd_1165953 : Nat := 4983230072969 + 3 ^ 40 * 1165953 * 2
def baseEnd_1165953 : Nat := 399129539701187958150257

theorem tailTrace_1165953 : CollatzResearch.WordTrace tailWord_1165953 prefixEnd_1165953 399129539701187958150257 := by
  unfold tailWord_1165953
  simp only [CollatzResearch.WordTrace]
  refine ⟨42525799544958884764046513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28350533029972589842697675 42525799544958884764046513)
  ·
    refine ⟨31894349658719163573034885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42525799544958884764046513 31894349658719163573034885)
    ·
      refine ⟨5980190561009843169944041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31894349658719163573034885 5980190561009843169944041)
      ·
        refine ⟨4485142920757382377458031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5980190561009843169944041 4485142920757382377458031)
        ·
          refine ⟨6727714381136073566187047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4485142920757382377458031 6727714381136073566187047)
          ·
            refine ⟨10091571571704110349280571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6727714381136073566187047 10091571571704110349280571)
            ·
              refine ⟨15137357357556165523920857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10091571571704110349280571 15137357357556165523920857)
              ·
                refine ⟨11353018018167124142940643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15137357357556165523920857 11353018018167124142940643)
                ·
                  refine ⟨17029527027250686214410965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11353018018167124142940643 17029527027250686214410965)
                  ·
                    refine ⟨399129539701187958150257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17029527027250686214410965 399129539701187958150257)
                    ·
                      rfl

theorem cell22_1165953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1165953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165953 prefixEnd_1165953 := by exact prefixLift 1165953
  have htrace : WordTrace (prefixWord ++ tailWord_1165953) baseStart_1165953 baseEnd_1165953 := by
    simpa [prefixWord, tailWord_1165953, baseEnd_1165953] using wordTrace_append hprefix tailTrace_1165953
  have hstable : (prefixWord ++ tailWord_1165953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165953).length < 2 ^ (prefixWord ++ tailWord_1165953).sum := by decide
  have hdescent : baseEnd_1165953 < baseStart_1165953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165970 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1165970 : Nat := 118140960795 + 1165970 * 2 ^ 59
def prefixEnd_1165970 : Nat := 4983230072969 + 3 ^ 40 * 1165970 * 2
def baseEnd_1165970 : Nat := 399135359148605580475205

theorem tailTrace_1165970 : CollatzResearch.WordTrace tailWord_1165970 prefixEnd_1165970 399135359148605580475205 := by
  unfold tailWord_1165970
  simp only [CollatzResearch.WordTrace]
  refine ⟨10631604896474324166853841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28350946390598197778276909 10631604896474324166853841)
  ·
    refine ⟨7973703672355743125140381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10631604896474324166853841 7973703672355743125140381)
    ·
      refine ⟨2990138877133403671927643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7973703672355743125140381 2990138877133403671927643)
      ·
        refine ⟨4485208315700105507891465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2990138877133403671927643 4485208315700105507891465)
        ·
          refine ⟨3363906236775079130918599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4485208315700105507891465 3363906236775079130918599)
          ·
            refine ⟨5045859355162618696377899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3363906236775079130918599 5045859355162618696377899)
            ·
              refine ⟨7568789032743928044566849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5045859355162618696377899 7568789032743928044566849)
              ·
                refine ⟨5676591774557946033425137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7568789032743928044566849 5676591774557946033425137)
                ·
                  refine ⟨4257443830918459525068853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5676591774557946033425137 4257443830918459525068853)
                  ·
                    refine ⟨399135359148605580475205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4257443830918459525068853 399135359148605580475205)
                    ·
                      rfl

theorem cell22_1165970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1165970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165970 prefixEnd_1165970 := by exact prefixLift 1165970
  have htrace : WordTrace (prefixWord ++ tailWord_1165970) baseStart_1165970 baseEnd_1165970 := by
    simpa [prefixWord, tailWord_1165970, baseEnd_1165970] using wordTrace_append hprefix tailTrace_1165970
  have hstable : (prefixWord ++ tailWord_1165970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165970).length < 2 ^ (prefixWord ++ tailWord_1165970).sum := by decide
  have hdescent : baseEnd_1165970 < baseStart_1165970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1165972 : List Nat := [2, 4, 2, 2, 1, 1, 3, 2, 5]
def baseStart_1165972 : Nat := 118140960795 + 1165972 * 2 ^ 59
def prefixEnd_1165972 : Nat := 4983230072969 + 3 ^ 40 * 1165972 * 2
def baseEnd_1165972 : Nat := 133045347929826080641733

theorem tailTrace_1165972 : CollatzResearch.WordTrace tailWord_1165972 prefixEnd_1165972 133045347929826080641733 := by
  unfold tailWord_1165972
  simp only [CollatzResearch.WordTrace]
  refine ⟨21263246265945025504494085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28350995021260034005992113 21263246265945025504494085)
  ·
    refine ⟨3986858674864692282092641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21263246265945025504494085 3986858674864692282092641)
    ·
      refine ⟨2990144006148519211569481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3986858674864692282092641 2990144006148519211569481)
      ·
        refine ⟨2242608004611389408677111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2990144006148519211569481 2242608004611389408677111)
        ·
          refine ⟨3363912006917084113015667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2242608004611389408677111 3363912006917084113015667)
          ·
            refine ⟨5045868010375626169523501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3363912006917084113015667 5045868010375626169523501)
            ·
              refine ⟨1892200503890859813571313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5045868010375626169523501 1892200503890859813571313)
              ·
                refine ⟨1419150377918144860178485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1892200503890859813571313 1419150377918144860178485)
                ·
                  refine ⟨133045347929826080641733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1419150377918144860178485 133045347929826080641733)
                  ·
                    rfl

theorem cell22_1165972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_1165972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1165972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1165972 prefixEnd_1165972 := by exact prefixLift 1165972
  have htrace : WordTrace (prefixWord ++ tailWord_1165972) baseStart_1165972 baseEnd_1165972 := by
    simpa [prefixWord, tailWord_1165972, baseEnd_1165972] using wordTrace_append hprefix tailTrace_1165972
  have hstable : (prefixWord ++ tailWord_1165972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1165972).length < 2 ^ (prefixWord ++ tailWord_1165972).sum := by decide
  have hdescent : baseEnd_1165972 < baseStart_1165972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1165972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166015 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 4, 3]
def baseStart_1166015 : Nat := 118140960795 + 1166015 * 2 ^ 59
def prefixEnd_1166015 : Nat := 4983230072969 + 3 ^ 40 * 1166015 * 2
def baseEnd_1166015 : Nat := 399150763568240463100067

theorem tailTrace_1166015 : CollatzResearch.WordTrace tailWord_1166015 prefixEnd_1166015 399150763568240463100067 := by
  unfold tailWord_1166015
  simp only [CollatzResearch.WordTrace]
  refine ⟨42528060870734269352803499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28352040580489512901868999 42528060870734269352803499)
  ·
    refine ⟨63792091306101404029205249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42528060870734269352803499 63792091306101404029205249)
    ·
      refine ⟨47844068479576053021903937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63792091306101404029205249 47844068479576053021903937)
      ·
        refine ⟨35883051359682039766427953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47844068479576053021903937 35883051359682039766427953)
        ·
          refine ⟨26912288519761529824820965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35883051359682039766427953 26912288519761529824820965)
          ·
            refine ⟨5046054097455286842153931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26912288519761529824820965 5046054097455286842153931)
            ·
              refine ⟨7569081146182930263230897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5046054097455286842153931 7569081146182930263230897)
              ·
                refine ⟨5676810859637197697423173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7569081146182930263230897 5676810859637197697423173)
                ·
                  refine ⟨1064402036181974568266845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5676810859637197697423173 1064402036181974568266845)
                  ·
                    refine ⟨399150763568240463100067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1064402036181974568266845 399150763568240463100067)
                    ·
                      rfl

theorem cell22_1166015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 3].length) (baseStart_1166015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166015 prefixEnd_1166015 := by exact prefixLift 1166015
  have htrace : WordTrace (prefixWord ++ tailWord_1166015) baseStart_1166015 baseEnd_1166015 := by
    simpa [prefixWord, tailWord_1166015, baseEnd_1166015] using wordTrace_append hprefix tailTrace_1166015
  have hstable : (prefixWord ++ tailWord_1166015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166015).length < 2 ^ (prefixWord ++ tailWord_1166015).sum := by decide
  have hdescent : baseEnd_1166015 < baseStart_1166015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166030 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_1166030 : Nat := 118140960795 + 1166030 * 2 ^ 59
def prefixEnd_1166030 : Nat := 4983230072969 + 3 ^ 40 * 1166030 * 2
def baseEnd_1166030 : Nat := 399155898374785423975021

theorem tailTrace_1166030 : CollatzResearch.WordTrace tailWord_1166030 prefixEnd_1166030 399155898374785423975021 := by
  unfold tailWord_1166030
  simp only [CollatzResearch.WordTrace]
  refine ⟨5316075995709990864324943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28352405310453284609733029 5316075995709990864324943)
  ·
    refine ⟨7974113993564986296487415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5316075995709990864324943 7974113993564986296487415)
    ·
      refine ⟨11961170990347479444731123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7974113993564986296487415 11961170990347479444731123)
      ·
        refine ⟨17941756485521219167096685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11961170990347479444731123 17941756485521219167096685)
        ·
          refine ⟨6728158682070457187661257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17941756485521219167096685 6728158682070457187661257)
          ·
            refine ⟨5046119011552842890745943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6728158682070457187661257 5046119011552842890745943)
            ·
              refine ⟨7569178517329264336118915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5046119011552842890745943 7569178517329264336118915)
              ·
                refine ⟨11353767775993896504178373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7569178517329264336118915 11353767775993896504178373)
                ·
                  refine ⟨2128831457998855594533445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11353767775993896504178373 2128831457998855594533445)
                  ·
                    refine ⟨399155898374785423975021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2128831457998855594533445 399155898374785423975021)
                    ·
                      rfl

theorem cell22_1166030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_1166030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166030 prefixEnd_1166030 := by exact prefixLift 1166030
  have htrace : WordTrace (prefixWord ++ tailWord_1166030) baseStart_1166030 baseEnd_1166030 := by
    simpa [prefixWord, tailWord_1166030, baseEnd_1166030] using wordTrace_append hprefix tailTrace_1166030
  have hstable : (prefixWord ++ tailWord_1166030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166030).length < 2 ^ (prefixWord ++ tailWord_1166030).sum := by decide
  have hdescent : baseEnd_1166030 < baseStart_1166030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166034 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 6]
def baseStart_1166034 : Nat := 118140960795 + 1166034 * 2 ^ 59
def prefixEnd_1166034 : Nat := 4983230072969 + 3 ^ 40 * 1166034 * 2
def baseEnd_1166034 : Nat := 133052422552176915625003

theorem tailTrace_1166034 : CollatzResearch.WordTrace tailWord_1166034 prefixEnd_1166034 133052422552176915625003 := by
  unfold tailWord_1166034
  simp only [CollatzResearch.WordTrace]
  refine ⟨10632188464416358899436289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28352502571776957065163437 10632188464416358899436289)
  ·
    refine ⟨7974141348312269174577217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10632188464416358899436289 7974141348312269174577217)
    ·
      refine ⟨5980606011234201880932913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7974141348312269174577217 5980606011234201880932913)
      ·
        refine ⟨4485454508425651410699685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5980606011234201880932913 4485454508425651410699685)
        ·
          refine ⟨841022720329809639506191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4485454508425651410699685 841022720329809639506191)
          ·
            refine ⟨1261534080494714459259287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841022720329809639506191 1261534080494714459259287)
            ·
              refine ⟨1892301120742071688888931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1261534080494714459259287 1892301120742071688888931)
              ·
                refine ⟨2838451681113107533333397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1892301120742071688888931 2838451681113107533333397)
                ·
                  refine ⟨133052422552176915625003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2838451681113107533333397 133052422552176915625003)
                  ·
                    rfl

theorem cell22_1166034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_1166034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166034 prefixEnd_1166034 := by exact prefixLift 1166034
  have htrace : WordTrace (prefixWord ++ tailWord_1166034) baseStart_1166034 baseEnd_1166034 := by
    simpa [prefixWord, tailWord_1166034, baseEnd_1166034] using wordTrace_append hprefix tailTrace_1166034
  have hstable : (prefixWord ++ tailWord_1166034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166034).length < 2 ^ (prefixWord ++ tailWord_1166034).sum := by decide
  have hdescent : baseEnd_1166034 < baseStart_1166034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166049 : List Nat := [1, 2, 3, 1, 4, 1, 4, 1, 2, 3]
def baseStart_1166049 : Nat := 118140960795 + 1166049 * 2 ^ 59
def prefixEnd_1166049 : Nat := 4983230072969 + 3 ^ 40 * 1166049 * 2
def baseEnd_1166049 : Nat := 399162402463075707749963

theorem tailTrace_1166049 : CollatzResearch.WordTrace tailWord_1166049 prefixEnd_1166049 399162402463075707749963 := by
  unfold tailWord_1166049
  simp only [CollatzResearch.WordTrace]
  refine ⟨42529300952611093159541201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28352867301740728773027467 42529300952611093159541201)
  ·
    refine ⟨31896975714458319869655901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42529300952611093159541201 31896975714458319869655901)
    ·
      refine ⟨11961365892921869951120963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31896975714458319869655901 11961365892921869951120963)
      ·
        refine ⟨17942048839382804926681445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11961365892921869951120963 17942048839382804926681445)
        ·
          refine ⟨3364134157384275923752771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17942048839382804926681445 3364134157384275923752771)
          ·
            refine ⟨5046201236076413885629157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3364134157384275923752771 5046201236076413885629157)
            ·
              refine ⟨946162731764327603555467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5046201236076413885629157 946162731764327603555467)
              ·
                refine ⟨1419244097646491405333201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946162731764327603555467 1419244097646491405333201)
                ·
                  refine ⟨1064433073234868553999901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1419244097646491405333201 1064433073234868553999901)
                  ·
                    refine ⟨399162402463075707749963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1064433073234868553999901 399162402463075707749963)
                    ·
                      rfl

theorem cell22_1166049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_1166049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166049 prefixEnd_1166049 := by exact prefixLift 1166049
  have htrace : WordTrace (prefixWord ++ tailWord_1166049) baseStart_1166049 baseEnd_1166049 := by
    simpa [prefixWord, tailWord_1166049, baseEnd_1166049] using wordTrace_append hprefix tailTrace_1166049
  have hstable : (prefixWord ++ tailWord_1166049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166049).length < 2 ^ (prefixWord ++ tailWord_1166049).sum := by decide
  have hdescent : baseEnd_1166049 < baseStart_1166049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166060 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 5, 3]
def baseStart_1166060 : Nat := 118140960795 + 1166060 * 2 ^ 59
def prefixEnd_1166060 : Nat := 4983230072969 + 3 ^ 40 * 1166060 * 2
def baseEnd_1166060 : Nat := 399166167987875345724929

theorem tailTrace_1166060 : CollatzResearch.WordTrace tailWord_1166060 prefixEnd_1166060 399166167987875345724929 := by
  unfold tailWord_1166060
  simp only [CollatzResearch.WordTrace]
  refine ⟨21264851077785621019095817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28353134770380828025461089 21264851077785621019095817)
  ·
    refine ⟨15948638308339215764321863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21264851077785621019095817 15948638308339215764321863)
    ·
      refine ⟨23922957462508823646482795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15948638308339215764321863 23922957462508823646482795)
      ·
        refine ⟨35884436193763235469724193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23922957462508823646482795 35884436193763235469724193)
        ·
          refine ⟨26913327145322426602293145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35884436193763235469724193 26913327145322426602293145)
          ·
            refine ⟨20184995358991819951719859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26913327145322426602293145 20184995358991819951719859)
            ·
              refine ⟨30277493038487729927579789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20184995358991819951719859 30277493038487729927579789)
              ·
                refine ⟨11354059889432898722842421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30277493038487729927579789 11354059889432898722842421)
                ·
                  refine ⟨1064443114634334255266477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11354059889432898722842421 1064443114634334255266477)
                  ·
                    refine ⟨399166167987875345724929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1064443114634334255266477 399166167987875345724929)
                    ·
                      rfl

theorem cell22_1166060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_1166060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166060 prefixEnd_1166060 := by exact prefixLift 1166060
  have htrace : WordTrace (prefixWord ++ tailWord_1166060) baseStart_1166060 baseEnd_1166060 := by
    simpa [prefixWord, tailWord_1166060, baseEnd_1166060] using wordTrace_append hprefix tailTrace_1166060
  have hstable : (prefixWord ++ tailWord_1166060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166060).length < 2 ^ (prefixWord ++ tailWord_1166060).sum := by decide
  have hdescent : baseEnd_1166060 < baseStart_1166060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166073 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 9]
def baseStart_1166073 : Nat := 118140960795 + 1166073 * 2 ^ 59
def prefixEnd_1166073 : Nat := 4983230072969 + 3 ^ 40 * 1166073 * 2
def baseEnd_1166073 : Nat := 133056872717849215049963

theorem tailTrace_1166073 : CollatzResearch.WordTrace tailWord_1166073 prefixEnd_1166073 133056872717849215049963 := by
  unfold tailWord_1166073
  simp only [CollatzResearch.WordTrace]
  refine ⟨42530176304524145258414873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28353450869682763505609915 42530176304524145258414873)
  ·
    refine ⟨31897632228393108943811155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42530176304524145258414873 31897632228393108943811155)
    ·
      refine ⟨47846448342589663415716733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31897632228393108943811155 47846448342589663415716733)
      ·
        refine ⟨17942418128471123780893775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47846448342589663415716733 17942418128471123780893775)
        ·
          refine ⟨26913627192706685671340663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17942418128471123780893775 26913627192706685671340663)
          ·
            refine ⟨40370440789060028507010995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26913627192706685671340663 40370440789060028507010995)
            ·
              refine ⟨60555661183590042760516493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40370440789060028507010995 60555661183590042760516493)
              ·
                refine ⟨22708372943846266035193685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60555661183590042760516493 22708372943846266035193685)
                ·
                  refine ⟨133056872717849215049963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22708372943846266035193685 133056872717849215049963)
                  ·
                    rfl

theorem cell22_1166073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 9].length) (baseStart_1166073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166073 prefixEnd_1166073 := by exact prefixLift 1166073
  have htrace : WordTrace (prefixWord ++ tailWord_1166073) baseStart_1166073 baseEnd_1166073 := by
    simpa [prefixWord, tailWord_1166073, baseEnd_1166073] using wordTrace_append hprefix tailTrace_1166073
  have hstable : (prefixWord ++ tailWord_1166073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166073).length < 2 ^ (prefixWord ++ tailWord_1166073).sum := by decide
  have hdescent : baseEnd_1166073 < baseStart_1166073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166141 : List Nat := [1, 4, 1, 4, 3, 1, 1, 2, 5]
def baseStart_1166141 : Nat := 118140960795 + 1166141 * 2 ^ 59
def prefixEnd_1166141 : Nat := 4983230072969 + 3 ^ 40 * 1166141 * 2
def baseEnd_1166141 : Nat := 133064631981072711483227

theorem tailTrace_1166141 : CollatzResearch.WordTrace tailWord_1166141 prefixEnd_1166141 133064631981072711483227 := by
  unfold tailWord_1166141
  simp only [CollatzResearch.WordTrace]
  refine ⟨42532656468277792871890277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28355104312185195247926851 42532656468277792871890277)
  ·
    refine ⟨7974873087802086163479427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42532656468277792871890277 7974873087802086163479427)
    ·
      refine ⟨11962309631703129245219141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7974873087802086163479427 11962309631703129245219141)
      ·
        refine ⟨2242933055944336733478589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11962309631703129245219141 2242933055944336733478589)
        ·
          refine ⟨841099895979126275054471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2242933055944336733478589 841099895979126275054471)
          ·
            refine ⟨1261649843968689412581707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841099895979126275054471 1261649843968689412581707)
            ·
              refine ⟨1892474765953034118872561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1261649843968689412581707 1892474765953034118872561)
              ·
                refine ⟨1419356074464775589154421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1892474765953034118872561 1419356074464775589154421)
                ·
                  refine ⟨133064631981072711483227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1419356074464775589154421 133064631981072711483227)
                  ·
                    rfl

theorem cell22_1166141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_1166141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166141 prefixEnd_1166141 := by exact prefixLift 1166141
  have htrace : WordTrace (prefixWord ++ tailWord_1166141) baseStart_1166141 baseEnd_1166141 := by
    simpa [prefixWord, tailWord_1166141, baseEnd_1166141] using wordTrace_append hprefix tailTrace_1166141
  have hstable : (prefixWord ++ tailWord_1166141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166141).length < 2 ^ (prefixWord ++ tailWord_1166141).sum := by decide
  have hdescent : baseEnd_1166141 < baseStart_1166141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166152 : List Nat := [2, 1, 3, 1, 1, 3, 1, 6, 4]
def baseStart_1166152 : Nat := 118140960795 + 1166152 * 2 ^ 59
def prefixEnd_1166152 : Nat := 4983230072969 + 3 ^ 40 * 1166152 * 2
def baseEnd_1166152 : Nat := 133065887156005924141549

theorem tailTrace_1166152 : CollatzResearch.WordTrace tailWord_1166152 prefixEnd_1166152 133065887156005924141549 := by
  unfold tailWord_1166152
  simp only [CollatzResearch.WordTrace]
  refine ⟨21266528835618970875270355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28355371780825294500360473 21266528835618970875270355)
  ·
    refine ⟨31899793253428456312905533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21266528835618970875270355 31899793253428456312905533)
    ·
      refine ⟨11962422470035671117339575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31899793253428456312905533 11962422470035671117339575)
      ·
        refine ⟨17943633705053506676009363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11962422470035671117339575 17943633705053506676009363)
        ·
          refine ⟨26915450557580260014014045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17943633705053506676009363 26915450557580260014014045)
          ·
            refine ⟨10093293959092597505255267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26915450557580260014014045 10093293959092597505255267)
            ·
              refine ⟨15139940938638896257882901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10093293959092597505255267 15139940938638896257882901)
              ·
                refine ⟨709684731498698262088261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15139940938638896257882901 709684731498698262088261)
                ·
                  refine ⟨133065887156005924141549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 709684731498698262088261 133065887156005924141549)
                  ·
                    rfl

theorem cell22_1166152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 4].length) (baseStart_1166152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166152 prefixEnd_1166152 := by exact prefixLift 1166152
  have htrace : WordTrace (prefixWord ++ tailWord_1166152) baseStart_1166152 baseEnd_1166152 := by
    simpa [prefixWord, tailWord_1166152, baseEnd_1166152] using wordTrace_append hprefix tailTrace_1166152
  have hstable : (prefixWord ++ tailWord_1166152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166152).length < 2 ^ (prefixWord ++ tailWord_1166152).sum := by decide
  have hdescent : baseEnd_1166152 < baseStart_1166152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166165 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 3, 6]
def baseStart_1166165 : Nat := 118140960795 + 1166165 * 2 ^ 59
def prefixEnd_1166165 : Nat := 4983230072969 + 3 ^ 40 * 1166165 * 2
def baseEnd_1166165 : Nat := 399202111633690071849607

theorem tailTrace_1166165 : CollatzResearch.WordTrace tailWord_1166165 prefixEnd_1166165 399202111633690071849607 := by
  unfold tailWord_1166165
  simp only [CollatzResearch.WordTrace]
  refine ⟨42533531820190844970763949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28355687880127229980509299 42533531820190844970763949)
  ·
    refine ⟨15950074432571566864036481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42533531820190844970763949 15950074432571566864036481)
    ·
      refine ⟨11962555824428675148027361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15950074432571566864036481 11962555824428675148027361)
      ·
        refine ⟨8971916868321506361020521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11962555824428675148027361 8971916868321506361020521)
        ·
          refine ⟨6728937651241129770765391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8971916868321506361020521 6728937651241129770765391)
          ·
            refine ⟨10093406476861694656148087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6728937651241129770765391 10093406476861694656148087)
            ·
              refine ⟨15140109715292541984222131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10093406476861694656148087 15140109715292541984222131)
              ·
                refine ⟨22710164572938812976333197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15140109715292541984222131 22710164572938812976333197)
                ·
                  refine ⟨8516311714852054866124949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22710164572938812976333197 8516311714852054866124949)
                  ·
                    refine ⟨399202111633690071849607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8516311714852054866124949 399202111633690071849607)
                    ·
                      rfl

theorem cell22_1166165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_1166165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166165 prefixEnd_1166165 := by exact prefixLift 1166165
  have htrace : WordTrace (prefixWord ++ tailWord_1166165) baseStart_1166165 baseEnd_1166165 := by
    simpa [prefixWord, tailWord_1166165, baseEnd_1166165] using wordTrace_append hprefix tailTrace_1166165
  have hstable : (prefixWord ++ tailWord_1166165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166165).length < 2 ^ (prefixWord ++ tailWord_1166165).sum := by decide
  have hdescent : baseEnd_1166165 < baseStart_1166165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166167 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 1, 5]
def baseStart_1166167 : Nat := 118140960795 + 1166167 * 2 ^ 59
def prefixEnd_1166167 : Nat := 4983230072969 + 3 ^ 40 * 1166167 * 2
def baseEnd_1166167 : Nat := 399202796274562733299601

theorem tailTrace_1166167 : CollatzResearch.WordTrace tailWord_1166167 prefixEnd_1166167 399202796274562733299601 := by
  unfold tailWord_1166167
  simp only [CollatzResearch.WordTrace]
  refine ⟨42533604766183599312336755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28355736510789066208224503 42533604766183599312336755)
  ·
    refine ⟨63800407149275398968505133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42533604766183599312336755 63800407149275398968505133)
    ·
      refine ⟨23925152680978274613189425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63800407149275398968505133 23925152680978274613189425)
      ·
        refine ⟨17943864510733705959892069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23925152680978274613189425 17943864510733705959892069)
        ·
          refine ⟨3364474595762569867479763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17943864510733705959892069 3364474595762569867479763)
          ·
            refine ⟨5046711893643854801219645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3364474595762569867479763 5046711893643854801219645)
            ·
              refine ⟨1892516960116445550457367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5046711893643854801219645 1892516960116445550457367)
              ·
                refine ⟨2838775440174668325686051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1892516960116445550457367 2838775440174668325686051)
                ·
                  refine ⟨4258163160262002488529077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2838775440174668325686051 4258163160262002488529077)
                  ·
                    refine ⟨399202796274562733299601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4258163160262002488529077 399202796274562733299601)
                    ·
                      rfl

theorem cell22_1166167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_1166167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166167 prefixEnd_1166167 := by exact prefixLift 1166167
  have htrace : WordTrace (prefixWord ++ tailWord_1166167) baseStart_1166167 baseEnd_1166167 := by
    simpa [prefixWord, tailWord_1166167, baseEnd_1166167] using wordTrace_append hprefix tailTrace_1166167
  have hstable : (prefixWord ++ tailWord_1166167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166167).length < 2 ^ (prefixWord ++ tailWord_1166167).sum := by decide
  have hdescent : baseEnd_1166167 < baseStart_1166167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166197 : List Nat := [1, 3, 4, 1, 1, 4, 8]
def baseStart_1166197 : Nat := 118140960795 + 1166197 * 2 ^ 59
def prefixEnd_1166197 : Nat := 4983230072969 + 3 ^ 40 * 1166197 * 2
def baseEnd_1166197 : Nat := 14785669106950098335167

theorem tailTrace_1166197 : CollatzResearch.WordTrace tailWord_1166197 prefixEnd_1166197 14785669106950098335167 := by
  unfold tailWord_1166197
  simp only [CollatzResearch.WordTrace]
  refine ⟨42534698956074914435928845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28356465970716609623952563 42534698956074914435928845)
  ·
    refine ⟨15950512108528092913473317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42534698956074914435928845 15950512108528092913473317)
    ·
      refine ⟨2990721020349017421276247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15950512108528092913473317 2990721020349017421276247)
      ·
        refine ⟨4486081530523526131914371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2990721020349017421276247 4486081530523526131914371)
        ·
          refine ⟨6729122295785289197871557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4486081530523526131914371 6729122295785289197871557)
          ·
            refine ⟨1261710430459741724600917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6729122295785289197871557 1261710430459741724600917)
            ·
              refine ⟨14785669106950098335167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1261710430459741724600917 14785669106950098335167)
              ·
                rfl

theorem cell22_1166197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 8].length) (baseStart_1166197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166197 prefixEnd_1166197 := by exact prefixLift 1166197
  have htrace : WordTrace (prefixWord ++ tailWord_1166197) baseStart_1166197 baseEnd_1166197 := by
    simpa [prefixWord, tailWord_1166197, baseEnd_1166197] using wordTrace_append hprefix tailTrace_1166197
  have hstable : (prefixWord ++ tailWord_1166197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166197).length < 2 ^ (prefixWord ++ tailWord_1166197).sum := by decide
  have hdescent : baseEnd_1166197 < baseStart_1166197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166218 : List Nat := [3, 1, 2, 4, 1, 3, 2, 1, 2, 3]
def baseStart_1166218 : Nat := 118140960795 + 1166218 * 2 ^ 59
def prefixEnd_1166218 : Nat := 4983230072969 + 3 ^ 40 * 1166218 * 2
def baseEnd_1166218 : Nat := 399220254616815600274445

theorem tailTrace_1166218 : CollatzResearch.WordTrace tailWord_1166218 prefixEnd_1166218 399220254616815600274445 := by
  unfold tailWord_1166218
  simp only [CollatzResearch.WordTrace]
  refine ⟨10633866222249708755610827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28356976592665890014962205 10633866222249708755610827)
  ·
    refine ⟨15950799333374563133416241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10633866222249708755610827 15950799333374563133416241)
    ·
      refine ⟨11963099500030922350062181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15950799333374563133416241 11963099500030922350062181)
      ·
        refine ⟨2243081156255797940636659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11963099500030922350062181 2243081156255797940636659)
        ·
          refine ⟨3364621734383696910954989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2243081156255797940636659 3364621734383696910954989)
          ·
            refine ⟨1261733150393886341608121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3364621734383696910954989 1261733150393886341608121)
            ·
              refine ⟨946299862795414756206091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1261733150393886341608121 946299862795414756206091)
              ·
                refine ⟨1419449794193122134309137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 946299862795414756206091 1419449794193122134309137)
                ·
                  refine ⟨1064587345644841600731853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1419449794193122134309137 1064587345644841600731853)
                  ·
                    refine ⟨399220254616815600274445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1064587345644841600731853 399220254616815600274445)
                    ·
                      rfl

theorem cell22_1166218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_1166218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166218 prefixEnd_1166218 := by exact prefixLift 1166218
  have htrace : WordTrace (prefixWord ++ tailWord_1166218) baseStart_1166218 baseEnd_1166218 := by
    simpa [prefixWord, tailWord_1166218, baseEnd_1166218] using wordTrace_append hprefix tailTrace_1166218
  have hstable : (prefixWord ++ tailWord_1166218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166218).length < 2 ^ (prefixWord ++ tailWord_1166218).sum := by decide
  have hdescent : baseEnd_1166218 < baseStart_1166218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166272 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 3, 4]
def baseStart_1166272 : Nat := 118140960795 + 1166272 * 2 ^ 59
def prefixEnd_1166272 : Nat := 4983230072969 + 3 ^ 40 * 1166272 * 2
def baseEnd_1166272 : Nat := 399238739920377459424279

theorem tailTrace_1166272 : CollatzResearch.WordTrace tailWord_1166272 prefixEnd_1166272 399238739920377459424279 := by
  unfold tailWord_1166272
  simp only [CollatzResearch.WordTrace]
  refine ⟨21268717215401601122454535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28358289620535468163272713 21268717215401601122454535)
  ·
    refine ⟨31903075823102401683681803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21268717215401601122454535 31903075823102401683681803)
    ·
      refine ⟨47854613734653602525522705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31903075823102401683681803 47854613734653602525522705)
      ·
        refine ⟨35890960300990201894142029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47854613734653602525522705 35890960300990201894142029)
        ·
          refine ⟨13459110112871325710303261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35890960300990201894142029 13459110112871325710303261)
          ·
            refine ⟨5047166292326747141363723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13459110112871325710303261 5047166292326747141363723)
            ·
              refine ⟨7570749438490120712045585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5047166292326747141363723 7570749438490120712045585)
              ·
                refine ⟨5678062078867590534034189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7570749438490120712045585 5678062078867590534034189)
                ·
                  refine ⟨2129273279575346450262821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5678062078867590534034189 2129273279575346450262821)
                  ·
                    refine ⟨399238739920377459424279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2129273279575346450262821 399238739920377459424279)
                    ·
                      rfl

theorem cell22_1166272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_1166272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166272 prefixEnd_1166272 := by exact prefixLift 1166272
  have htrace : WordTrace (prefixWord ++ tailWord_1166272) baseStart_1166272 baseEnd_1166272 := by
    simpa [prefixWord, tailWord_1166272, baseEnd_1166272] using wordTrace_append hprefix tailTrace_1166272
  have hstable : (prefixWord ++ tailWord_1166272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166272).length < 2 ^ (prefixWord ++ tailWord_1166272).sum := by decide
  have hdescent : baseEnd_1166272 < baseStart_1166272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166287 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 6]
def baseStart_1166287 : Nat := 118140960795 + 1166287 * 2 ^ 59
def prefixEnd_1166287 : Nat := 4983230072969 + 3 ^ 40 * 1166287 * 2
def baseEnd_1166287 : Nat := 133081291575640806766411

theorem tailTrace_1166287 : CollatzResearch.WordTrace tailWord_1166287 prefixEnd_1166287 133081291575640806766411 := by
  unfold tailWord_1166287
  simp only [CollatzResearch.WordTrace]
  refine ⟨42537981525748859806705115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28358654350499239871136743 42537981525748859806705115)
  ·
    refine ⟨63806972288623289710057673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42537981525748859806705115 63806972288623289710057673)
    ·
      refine ⟨47855229216467467282543255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63806972288623289710057673 47855229216467467282543255)
      ·
        refine ⟨71782843824701200923814883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47855229216467467282543255 71782843824701200923814883)
        ·
          refine ⟨107674265737051801385722325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71782843824701200923814883 107674265737051801385722325)
          ·
            refine ⟨2523615603212151594977867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 107674265737051801385722325 2523615603212151594977867)
            ·
              refine ⟨3785423404818227392466801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2523615603212151594977867 3785423404818227392466801)
              ·
                refine ⟨2839067553613670544350101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3785423404818227392466801 2839067553613670544350101)
                ·
                  refine ⟨133081291575640806766411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2839067553613670544350101 133081291575640806766411)
                  ·
                    rfl

theorem cell22_1166287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 6].length) (baseStart_1166287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166287 prefixEnd_1166287 := by exact prefixLift 1166287
  have htrace : WordTrace (prefixWord ++ tailWord_1166287) baseStart_1166287 baseEnd_1166287 := by
    simpa [prefixWord, tailWord_1166287, baseEnd_1166287] using wordTrace_append hprefix tailTrace_1166287
  have hstable : (prefixWord ++ tailWord_1166287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166287).length < 2 ^ (prefixWord ++ tailWord_1166287).sum := by decide
  have hdescent : baseEnd_1166287 < baseStart_1166287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166319 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 4, 3]
def baseStart_1166319 : Nat := 118140960795 + 1166319 * 2 ^ 59
def prefixEnd_1166319 : Nat := 4983230072969 + 3 ^ 40 * 1166319 * 2
def baseEnd_1166319 : Nat := 399254828980885003499135

theorem tailTrace_1166319 : CollatzResearch.WordTrace tailWord_1166319 prefixEnd_1166319 399254828980885003499135 := by
  unfold tailWord_1166319
  simp only [CollatzResearch.WordTrace]
  refine ⟨42539148661632929271870011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28359432441088619514580007 42539148661632929271870011)
  ·
    refine ⟨63808722992449393907805017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42539148661632929271870011 63808722992449393907805017)
    ·
      refine ⟨47856542244337045430853763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63808722992449393907805017 47856542244337045430853763)
      ·
        refine ⟨71784813366505568146280645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47856542244337045430853763 71784813366505568146280645)
        ·
          refine ⟨13459652506219794027427621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71784813366505568146280645 13459652506219794027427621)
          ·
            refine ⟨2523684844916211380142679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13459652506219794027427621 2523684844916211380142679)
            ·
              refine ⟨3785527267374317070214019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2523684844916211380142679 3785527267374317070214019)
              ·
                refine ⟨5678290901061475605321029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3785527267374317070214019 5678290901061475605321029)
                ·
                  refine ⟨1064679543949026675997693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5678290901061475605321029 1064679543949026675997693)
                  ·
                    refine ⟨399254828980885003499135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1064679543949026675997693 399254828980885003499135)
                    ·
                      rfl

theorem cell22_1166319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 3].length) (baseStart_1166319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166319 prefixEnd_1166319 := by exact prefixLift 1166319
  have htrace : WordTrace (prefixWord ++ tailWord_1166319) baseStart_1166319 baseEnd_1166319 := by
    simpa [prefixWord, tailWord_1166319, baseEnd_1166319] using wordTrace_append hprefix tailTrace_1166319
  have hstable : (prefixWord ++ tailWord_1166319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166319).length < 2 ^ (prefixWord ++ tailWord_1166319).sum := by decide
  have hdescent : baseEnd_1166319 < baseStart_1166319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166488 : List Nat := [2, 1, 2, 4, 2, 1, 3, 2, 2, 3]
def baseStart_1166488 : Nat := 118140960795 + 1166488 * 2 ^ 59
def prefixEnd_1166488 : Nat := 4983230072969 + 3 ^ 40 * 1166488 * 2
def baseEnd_1166488 : Nat := 399312681134624896023617

theorem tailTrace_1166488 : CollatzResearch.WordTrace tailWord_1166488 prefixEnd_1166488 399312681134624896023617 := by
  unfold tailWord_1166488
  simp only [CollatzResearch.WordTrace]
  refine ⟨21272656299010335567386059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28363541732013780756514745 21272656299010335567386059)
  ·
    refine ⟨31908984448515503351079089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21272656299010335567386059 31908984448515503351079089)
    ·
      refine ⟨23931738336386627513309317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31908984448515503351079089 23931738336386627513309317)
      ·
        refine ⟨4487200938072492658745497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23931738336386627513309317 4487200938072492658745497)
        ·
          refine ⟨3365400703554369494059123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4487200938072492658745497 3365400703554369494059123)
          ·
            refine ⟨5048101055331554241088685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3365400703554369494059123 5048101055331554241088685)
            ·
              refine ⟨1893037895749332840408257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5048101055331554241088685 1893037895749332840408257)
              ·
                refine ⟨1419778421811999630306193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1893037895749332840408257 1419778421811999630306193)
                ·
                  refine ⟨1064833816358999722729645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1419778421811999630306193 1064833816358999722729645)
                  ·
                    refine ⟨399312681134624896023617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1064833816358999722729645 399312681134624896023617)
                    ·
                      rfl

theorem cell22_1166488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_1166488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166488 prefixEnd_1166488 := by exact prefixLift 1166488
  have htrace : WordTrace (prefixWord ++ tailWord_1166488) baseStart_1166488 baseEnd_1166488 := by
    simpa [prefixWord, tailWord_1166488, baseEnd_1166488] using wordTrace_append hprefix tailTrace_1166488
  have hstable : (prefixWord ++ tailWord_1166488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166488).length < 2 ^ (prefixWord ++ tailWord_1166488).sum := by decide
  have hdescent : baseEnd_1166488 < baseStart_1166488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166546 : List Nat := [3, 2, 2, 2, 1, 1, 2, 4, 5]
def baseStart_1166546 : Nat := 118140960795 + 1166546 * 2 ^ 59
def prefixEnd_1166546 : Nat := 4983230072969 + 3 ^ 40 * 1166546 * 2
def baseEnd_1166546 : Nat := 133110845239977359357813

theorem tailTrace_1166546 : CollatzResearch.WordTrace tailWord_1166546 prefixEnd_1166546 133110845239977359357813 := by
  unfold tailWord_1166546
  simp only [CollatzResearch.WordTrace]
  refine ⟨10636857007952636760095873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28364952021207031360255661 10636857007952636760095873)
  ·
    refine ⟨7977642755964477570071905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10636857007952636760095873 7977642755964477570071905)
    ·
      refine ⟨5983232066973358177553929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7977642755964477570071905 5983232066973358177553929)
      ·
        refine ⟨4487424050230018633165447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5983232066973358177553929 4487424050230018633165447)
        ·
          refine ⟨6731136075345027949748171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4487424050230018633165447 6731136075345027949748171)
          ·
            refine ⟨10096704113017541924622257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6731136075345027949748171 10096704113017541924622257)
            ·
              refine ⟨7572528084763156443466693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10096704113017541924622257 7572528084763156443466693)
              ·
                refine ⟨1419849015893091833150005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7572528084763156443466693 1419849015893091833150005)
                ·
                  refine ⟨133110845239977359357813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1419849015893091833150005 133110845239977359357813)
                  ·
                    rfl

theorem cell22_1166546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_1166546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166546 prefixEnd_1166546 := by exact prefixLift 1166546
  have htrace : WordTrace (prefixWord ++ tailWord_1166546) baseStart_1166546 baseEnd_1166546 := by
    simpa [prefixWord, tailWord_1166546, baseEnd_1166546] using wordTrace_append hprefix tailTrace_1166546
  have hstable : (prefixWord ++ tailWord_1166546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166546).length < 2 ^ (prefixWord ++ tailWord_1166546).sum := by decide
  have hdescent : baseEnd_1166546 < baseStart_1166546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166623 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 1, 5]
def baseStart_1166623 : Nat := 118140960795 + 1166623 * 2 ^ 59
def prefixEnd_1166623 : Nat := 4983230072969 + 3 ^ 40 * 1166623 * 2
def baseEnd_1166623 : Nat := 399358894393529543898203

theorem tailTrace_1166623 : CollatzResearch.WordTrace tailWord_1166623 prefixEnd_1166623 399358894393529543898203 := by
  unfold tailWord_1166623
  simp only [CollatzResearch.WordTrace]
  refine ⟨42550236452531589190936523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28366824301687726127291015 42550236452531589190936523)
  ·
    refine ⟨63825354678797383786404785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42550236452531589190936523 63825354678797383786404785)
    ·
      refine ⟨47869016009098037839803589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63825354678797383786404785 47869016009098037839803589)
      ·
        refine ⟨8975440501705882094963173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47869016009098037839803589 8975440501705882094963173)
        ·
          refine ⟨1682895094069852892805595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8975440501705882094963173 1682895094069852892805595)
          ·
            refine ⟨2524342641104779339208393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1682895094069852892805595 2524342641104779339208393)
            ·
              refine ⟨1893256980828584504406295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2524342641104779339208393 1893256980828584504406295)
              ·
                refine ⟨2839885471242876756609443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1893256980828584504406295 2839885471242876756609443)
                ·
                  refine ⟨4259828206864315134914165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2839885471242876756609443 4259828206864315134914165)
                  ·
                    refine ⟨399358894393529543898203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4259828206864315134914165 399358894393529543898203)
                    ·
                      rfl

theorem cell22_1166623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 5].length) (baseStart_1166623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166623 prefixEnd_1166623 := by exact prefixLift 1166623
  have htrace : WordTrace (prefixWord ++ tailWord_1166623) baseStart_1166623 baseEnd_1166623 := by
    simpa [prefixWord, tailWord_1166623, baseEnd_1166623] using wordTrace_append hprefix tailTrace_1166623
  have hstable : (prefixWord ++ tailWord_1166623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166623).length < 2 ^ (prefixWord ++ tailWord_1166623).sum := by decide
  have hdescent : baseEnd_1166623 < baseStart_1166623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166653 : List Nat := [1, 4, 1, 5, 1, 1, 9]
def baseStart_1166653 : Nat := 118140960795 + 1166653 * 2 ^ 59
def prefixEnd_1166653 : Nat := 4983230072969 + 3 ^ 40 * 1166653 * 2
def baseEnd_1166653 : Nat := 14791450518763683912893

theorem tailTrace_1166653 : CollatzResearch.WordTrace tailWord_1166653 prefixEnd_1166653 14791450518763683912893 := by
  unfold tailWord_1166653
  simp only [CollatzResearch.WordTrace]
  refine ⟨42551330642422904314528613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28367553761615269543019075 42551330642422904314528613)
  ·
    refine ⟨7978374495454294558974115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42551330642422904314528613 7978374495454294558974115)
    ·
      refine ⟨11967561743181441838461173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7978374495454294558974115 11967561743181441838461173)
      ·
        refine ⟨1121958913423260172355735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11967561743181441838461173 1121958913423260172355735)
        ·
          refine ⟨1682938370134890258533603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1121958913423260172355735 1682938370134890258533603)
          ·
            refine ⟨2524407555202335387800405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1682938370134890258533603 2524407555202335387800405)
            ·
              refine ⟨14791450518763683912893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2524407555202335387800405 14791450518763683912893)
              ·
                rfl

theorem cell22_1166653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 9].length) (baseStart_1166653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166653 prefixEnd_1166653 := by exact prefixLift 1166653
  have htrace : WordTrace (prefixWord ++ tailWord_1166653) baseStart_1166653 baseEnd_1166653 := by
    simpa [prefixWord, tailWord_1166653, baseEnd_1166653] using wordTrace_append hprefix tailTrace_1166653
  have hstable : (prefixWord ++ tailWord_1166653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166653).length < 2 ^ (prefixWord ++ tailWord_1166653).sum := by decide
  have hdescent : baseEnd_1166653 < baseStart_1166653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166657 : List Nat := [1, 2, 5, 2, 1, 3, 1, 2, 2, 3]
def baseStart_1166657 : Nat := 118140960795 + 1166657 * 2 ^ 59
def prefixEnd_1166657 : Nat := 4983230072969 + 3 ^ 40 * 1166657 * 2
def baseEnd_1166657 : Nat := 399370533288364788548099

theorem tailTrace_1166657 : CollatzResearch.WordTrace tailWord_1166657 prefixEnd_1166657 399370533288364788548099 := by
  unfold tailWord_1166657
  simp only [CollatzResearch.WordTrace]
  refine ⟨42551476534408412997674225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28367651022938941998449483 42551476534408412997674225)
  ·
    refine ⟨31913607400806309748255669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42551476534408412997674225 31913607400806309748255669)
    ·
      refine ⟨2991900693825591538898969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31913607400806309748255669 2991900693825591538898969)
      ·
        refine ⟨2243925520369193654174227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2991900693825591538898969 2243925520369193654174227)
        ·
          refine ⟨3365888280553790481261341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2243925520369193654174227 3365888280553790481261341)
          ·
            refine ⟨1262208105207671430473003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3365888280553790481261341 1262208105207671430473003)
            ·
              refine ⟨1893312157811507145709505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262208105207671430473003 1893312157811507145709505)
              ·
                refine ⟨1419984118358630359282129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1893312157811507145709505 1419984118358630359282129)
                ·
                  refine ⟨1064988088768972769461597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1419984118358630359282129 1064988088768972769461597)
                  ·
                    refine ⟨399370533288364788548099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1064988088768972769461597 399370533288364788548099)
                    ·
                      rfl

theorem cell22_1166657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_1166657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166657 prefixEnd_1166657 := by exact prefixLift 1166657
  have htrace : WordTrace (prefixWord ++ tailWord_1166657) baseStart_1166657 baseEnd_1166657 := by
    simpa [prefixWord, tailWord_1166657, baseEnd_1166657] using wordTrace_append hprefix tailTrace_1166657
  have hstable : (prefixWord ++ tailWord_1166657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166657).length < 2 ^ (prefixWord ++ tailWord_1166657).sum := by decide
  have hdescent : baseEnd_1166657 < baseStart_1166657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166668 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 3, 3]
def baseStart_1166668 : Nat := 118140960795 + 1166668 * 2 ^ 59
def prefixEnd_1166668 : Nat := 4983230072969 + 3 ^ 40 * 1166668 * 2
def baseEnd_1166668 : Nat := 399374298813164426523065

theorem tailTrace_1166668 : CollatzResearch.WordTrace tailWord_1166668 prefixEnd_1166668 399374298813164426523065 := by
  unfold tailWord_1166668
  simp only [CollatzResearch.WordTrace]
  refine ⟨21275938868684280938162329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28367918491579041250883105 21275938868684280938162329)
  ·
    refine ⟨15956954151513210703621747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21275938868684280938162329 15956954151513210703621747)
    ·
      refine ⟨23935431227269816055432621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15956954151513210703621747 23935431227269816055432621)
      ·
        refine ⟨8975786710226181020787233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23935431227269816055432621 8975786710226181020787233)
        ·
          refine ⟨6731840032669635765590425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8975786710226181020787233 6731840032669635765590425)
          ·
            refine ⟨5048880024502226824192819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6731840032669635765590425 5048880024502226824192819)
            ·
              refine ⟨7573320036753340236289229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5048880024502226824192819 7573320036753340236289229)
              ·
                refine ⟨2839995013782502588608461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7573320036753340236289229 2839995013782502588608461)
                ·
                  refine ⟨1064998130168438470728173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2839995013782502588608461 1064998130168438470728173)
                  ·
                    refine ⟨399374298813164426523065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1064998130168438470728173 399374298813164426523065)
                    ·
                      rfl

theorem cell22_1166668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_1166668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166668 prefixEnd_1166668 := by exact prefixLift 1166668
  have htrace : WordTrace (prefixWord ++ tailWord_1166668) baseStart_1166668 baseEnd_1166668 := by
    simpa [prefixWord, tailWord_1166668, baseEnd_1166668] using wordTrace_append hprefix tailTrace_1166668
  have hstable : (prefixWord ++ tailWord_1166668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166668).length < 2 ^ (prefixWord ++ tailWord_1166668).sum := by decide
  have hdescent : baseEnd_1166668 < baseStart_1166668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166681 : List Nat := [1, 2, 1, 2, 2, 2, 2, 5, 5]
def baseStart_1166681 : Nat := 118140960795 + 1166681 * 2 ^ 59
def prefixEnd_1166681 : Nat := 4983230072969 + 3 ^ 40 * 1166681 * 2
def baseEnd_1166681 : Nat := 133126249659612241982675

theorem tailTrace_1166681 : CollatzResearch.WordTrace tailWord_1166681 prefixEnd_1166681 133126249659612241982675 := by
  unfold tailWord_1166681
  simp only [CollatzResearch.WordTrace]
  refine ⟨42552351886321465096547897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28368234590880976731031931 42552351886321465096547897)
  ·
    refine ⟨31914263914741098822410923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42552351886321465096547897 31914263914741098822410923)
    ·
      refine ⟨47871395872111648233616385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31914263914741098822410923 47871395872111648233616385)
      ·
        refine ⟨35903546904083736175212289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47871395872111648233616385 35903546904083736175212289)
        ·
          refine ⟨26927660178062802131409217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35903546904083736175212289 26927660178062802131409217)
          ·
            refine ⟨20195745133547101598556913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26927660178062802131409217 20195745133547101598556913)
            ·
              refine ⟨15146808850160326198917685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20195745133547101598556913 15146808850160326198917685)
              ·
                refine ⟨1420013329702530581148533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15146808850160326198917685 1420013329702530581148533)
                ·
                  refine ⟨133126249659612241982675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1420013329702530581148533 133126249659612241982675)
                  ·
                    rfl

theorem cell22_1166681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 5].length) (baseStart_1166681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166681 prefixEnd_1166681 := by exact prefixLift 1166681
  have htrace : WordTrace (prefixWord ++ tailWord_1166681) baseStart_1166681 baseEnd_1166681 := by
    simpa [prefixWord, tailWord_1166681, baseEnd_1166681] using wordTrace_append hprefix tailTrace_1166681
  have hstable : (prefixWord ++ tailWord_1166681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166681).length < 2 ^ (prefixWord ++ tailWord_1166681).sum := by decide
  have hdescent : baseEnd_1166681 < baseStart_1166681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166745 : List Nat := [1, 2, 1, 2, 1, 7, 1, 2, 1, 4]
def baseStart_1166745 : Nat := 118140960795 + 1166745 * 2 ^ 59
def prefixEnd_1166745 : Nat := 4983230072969 + 3 ^ 40 * 1166745 * 2
def baseEnd_1166745 : Nat := 399400657486761892347829

theorem tailTrace_1166745 : CollatzResearch.WordTrace tailWord_1166745 prefixEnd_1166745 399400657486761892347829 := by
  unfold tailWord_1166745
  simp only [CollatzResearch.WordTrace]
  refine ⟨42554686158089604026877689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28369790772059736017918459 42554686158089604026877689)
  ·
    refine ⟨31916014618567203020158267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42554686158089604026877689 31916014618567203020158267)
    ·
      refine ⟨47874021927850804530237401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31916014618567203020158267 47874021927850804530237401)
      ·
        refine ⟨35905516445888103397678051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47874021927850804530237401 35905516445888103397678051)
        ·
          refine ⟨53858274668832155096517077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35905516445888103397678051 53858274668832155096517077)
          ·
            refine ⟨1262303312550753635074619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 53858274668832155096517077 1262303312550753635074619)
            ·
              refine ⟨1893454968826130452611929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262303312550753635074619 1893454968826130452611929)
              ·
                refine ⟨1420091226619597839458947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1893454968826130452611929 1420091226619597839458947)
                ·
                  refine ⟨2130136839929396759188421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420091226619597839458947 2130136839929396759188421)
                  ·
                    refine ⟨399400657486761892347829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2130136839929396759188421 399400657486761892347829)
                    ·
                      rfl

theorem cell22_1166745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 4].length) (baseStart_1166745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166745 prefixEnd_1166745 := by exact prefixLift 1166745
  have htrace : WordTrace (prefixWord ++ tailWord_1166745) baseStart_1166745 baseEnd_1166745 := by
    simpa [prefixWord, tailWord_1166745, baseEnd_1166745] using wordTrace_append hprefix tailTrace_1166745
  have hstable : (prefixWord ++ tailWord_1166745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166745).length < 2 ^ (prefixWord ++ tailWord_1166745).sum := by decide
  have hdescent : baseEnd_1166745 < baseStart_1166745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166775 : List Nat := [1, 1, 3, 1, 3, 2, 4, 2, 2, 3]
def baseStart_1166775 : Nat := 118140960795 + 1166775 * 2 ^ 59
def prefixEnd_1166775 : Nat := 4983230072969 + 3 ^ 40 * 1166775 * 2
def baseEnd_1166775 : Nat := 399410927099851814097737

theorem tailTrace_1166775 : CollatzResearch.WordTrace tailWord_1166775 prefixEnd_1166775 399410927099851814097737 := by
  unfold tailWord_1166775
  simp only [CollatzResearch.WordTrace]
  refine ⟨42555780347980919150469779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28370520231987279433646519 42555780347980919150469779)
  ·
    refine ⟨63833670521971378725704669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42555780347980919150469779 63833670521971378725704669)
    ·
      refine ⟨23937626445739267022139251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63833670521971378725704669 23937626445739267022139251)
      ·
        refine ⟨35906439668608900533208877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23937626445739267022139251 35906439668608900533208877)
        ·
          refine ⟨13464914875728337699953329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35906439668608900533208877 13464914875728337699953329)
          ·
            refine ⟨10098686156796253274964997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13464914875728337699953329 10098686156796253274964997)
            ·
              refine ⟨1893503654399297489055937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10098686156796253274964997 1893503654399297489055937)
              ·
                refine ⟨1420127740799473116791953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1893503654399297489055937 1420127740799473116791953)
                ·
                  refine ⟨1065095805599604837593965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1420127740799473116791953 1065095805599604837593965)
                  ·
                    refine ⟨399410927099851814097737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1065095805599604837593965 399410927099851814097737)
                    ·
                      rfl

theorem cell22_1166775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_1166775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166775 prefixEnd_1166775 := by exact prefixLift 1166775
  have htrace : WordTrace (prefixWord ++ tailWord_1166775) baseStart_1166775 baseEnd_1166775 := by
    simpa [prefixWord, tailWord_1166775, baseEnd_1166775] using wordTrace_append hprefix tailTrace_1166775
  have hstable : (prefixWord ++ tailWord_1166775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166775).length < 2 ^ (prefixWord ++ tailWord_1166775).sum := by decide
  have hdescent : baseEnd_1166775 < baseStart_1166775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166833 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 7]
def baseStart_1166833 : Nat := 118140960795 + 1166833 * 2 ^ 59
def prefixEnd_1166833 : Nat := 4983230072969 + 3 ^ 40 * 1166833 * 2
def baseEnd_1166833 : Nat := 133143593895052998715853

theorem tailTrace_1166833 : CollatzResearch.WordTrace tailWord_1166833 prefixEnd_1166833 133143593895052998715853 := by
  unfold tailWord_1166833
  simp only [CollatzResearch.WordTrace]
  refine ⟨42557895781770795056081153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28371930521180530037387435 42557895781770795056081153)
  ·
    refine ⟨31918421836328096292060865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42557895781770795056081153 31918421836328096292060865)
    ·
      refine ⟨23938816377246072219045649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31918421836328096292060865 23938816377246072219045649)
      ·
        refine ⟨17954112282934554164284237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23938816377246072219045649 17954112282934554164284237)
        ·
          refine ⟨6732792106100457811606589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17954112282934554164284237 6732792106100457811606589)
          ·
            refine ⟨2524797039787671679352471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6732792106100457811606589 2524797039787671679352471)
            ·
              refine ⟨3787195559681507519028707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2524797039787671679352471 3787195559681507519028707)
              ·
                refine ⟨5680793339522261278543061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3787195559681507519028707 5680793339522261278543061)
                ·
                  refine ⟨133143593895052998715853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5680793339522261278543061 133143593895052998715853)
                  ·
                    rfl

theorem cell22_1166833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 7].length) (baseStart_1166833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166833 prefixEnd_1166833 := by exact prefixLift 1166833
  have htrace : WordTrace (prefixWord ++ tailWord_1166833) baseStart_1166833 baseEnd_1166833 := by
    simpa [prefixWord, tailWord_1166833, baseEnd_1166833] using wordTrace_append hprefix tailTrace_1166833
  have hstable : (prefixWord ++ tailWord_1166833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166833).length < 2 ^ (prefixWord ++ tailWord_1166833).sum := by decide
  have hdescent : baseEnd_1166833 < baseStart_1166833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166837 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1166837 : Nat := 118140960795 + 1166837 * 2 ^ 59
def prefixEnd_1166837 : Nat := 4983230072969 + 3 ^ 40 * 1166837 * 2
def baseEnd_1166837 : Nat := 399432150966904319047547

theorem tailTrace_1166837 : CollatzResearch.WordTrace tailWord_1166837 prefixEnd_1166837 399432150966904319047547 := by
  unfold tailWord_1166837
  simp only [CollatzResearch.WordTrace]
  refine ⟨42558041673756303739226765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28372027782504202492817843 42558041673756303739226765)
  ·
    refine ⟨15959265627658613902210037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42558041673756303739226765 15959265627658613902210037)
    ·
      refine ⟨1496181152592995053332191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15959265627658613902210037 1496181152592995053332191)
      ·
        refine ⟨2244271728889492579998287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1496181152592995053332191 2244271728889492579998287)
        ·
          refine ⟨3366407593334238869997431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2244271728889492579998287 3366407593334238869997431)
          ·
            refine ⟨5049611390001358304996147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3366407593334238869997431 5049611390001358304996147)
            ·
              refine ⟨7574417085002037457494221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5049611390001358304996147 7574417085002037457494221)
              ·
                refine ⟨2840406406875764046560333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7574417085002037457494221 2840406406875764046560333)
                ·
                  refine ⟨1065152402578411517460125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2840406406875764046560333 1065152402578411517460125)
                  ·
                    refine ⟨399432150966904319047547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1065152402578411517460125 399432150966904319047547)
                    ·
                      rfl

theorem cell22_1166837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1166837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166837 prefixEnd_1166837 := by exact prefixLift 1166837
  have htrace : WordTrace (prefixWord ++ tailWord_1166837) baseStart_1166837 baseEnd_1166837 := by
    simpa [prefixWord, tailWord_1166837, baseEnd_1166837] using wordTrace_append hprefix tailTrace_1166837
  have hstable : (prefixWord ++ tailWord_1166837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166837).length < 2 ^ (prefixWord ++ tailWord_1166837).sum := by decide
  have hdescent : baseEnd_1166837 < baseStart_1166837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166953 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 2, 6]
def baseStart_1166953 : Nat := 118140960795 + 1166953 * 2 ^ 59
def prefixEnd_1166953 : Nat := 4983230072969 + 3 ^ 40 * 1166953 * 2
def baseEnd_1166953 : Nat := 399471860137518683147191

theorem tailTrace_1166953 : CollatzResearch.WordTrace tailWord_1166953 prefixEnd_1166953 399471860137518683147191 := by
  unfold tailWord_1166953
  simp only [CollatzResearch.WordTrace]
  refine ⟨42562272541336055550449513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28374848360890703700299675 42562272541336055550449513)
  ·
    refine ⟨31921704406002041662837135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42562272541336055550449513 31921704406002041662837135)
    ·
      refine ⟨47882556609003062494255703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31921704406002041662837135 47882556609003062494255703)
      ·
        refine ⟨71823834913504593741383555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47882556609003062494255703 71823834913504593741383555)
        ·
          refine ⟨107735752370256890612075333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71823834913504593741383555 107735752370256890612075333)
          ·
            refine ⟨20200453569423166989764125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107735752370256890612075333 20200453569423166989764125)
            ·
              refine ⟨7575170088533687621161547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20200453569423166989764125 7575170088533687621161547)
              ·
                refine ⟨11362755132800531431742321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7575170088533687621161547 11362755132800531431742321)
                ·
                  refine ⟨8522066349600398573806741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11362755132800531431742321 8522066349600398573806741)
                  ·
                    refine ⟨399471860137518683147191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8522066349600398573806741 399471860137518683147191)
                    ·
                      rfl

theorem cell22_1166953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_1166953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166953 prefixEnd_1166953 := by exact prefixLift 1166953
  have htrace : WordTrace (prefixWord ++ tailWord_1166953) baseStart_1166953 baseEnd_1166953 := by
    simpa [prefixWord, tailWord_1166953, baseEnd_1166953] using wordTrace_append hprefix tailTrace_1166953
  have hstable : (prefixWord ++ tailWord_1166953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166953).length < 2 ^ (prefixWord ++ tailWord_1166953).sum := by decide
  have hdescent : baseEnd_1166953 < baseStart_1166953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1166957 : List Nat := [1, 5, 1, 1, 4, 2, 1, 7]
def baseStart_1166957 : Nat := 118140960795 + 1166957 * 2 ^ 59
def prefixEnd_1166957 : Nat := 4983230072969 + 3 ^ 40 * 1166957 * 2
def baseEnd_1166957 : Nat := 44385914379918222894131

theorem tailTrace_1166957 : CollatzResearch.WordTrace tailWord_1166957 prefixEnd_1166957 44385914379918222894131 := by
  unfold tailWord_1166957
  simp only [CollatzResearch.WordTrace]
  refine ⟨42562418433321564233595125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28374945622214376155730083 42562418433321564233595125)
  ·
    refine ⟨3990226728123896646899543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42562418433321564233595125 3990226728123896646899543)
    ·
      refine ⟨5985340092185844970349315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3990226728123896646899543 5985340092185844970349315)
      ·
        refine ⟨8978010138278767455523973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5985340092185844970349315 8978010138278767455523973)
        ·
          refine ⟨1683376900927268897910745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8978010138278767455523973 1683376900927268897910745)
          ·
            refine ⟨1262532675695451673433059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1683376900927268897910745 1262532675695451673433059)
            ·
              refine ⟨1893799013543177510149589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262532675695451673433059 1893799013543177510149589)
              ·
                refine ⟨44385914379918222894131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1893799013543177510149589 44385914379918222894131)
                ·
                  rfl

theorem cell22_1166957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 7].length) (baseStart_1166957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1166957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1166957 prefixEnd_1166957 := by exact prefixLift 1166957
  have htrace : WordTrace (prefixWord ++ tailWord_1166957) baseStart_1166957 baseEnd_1166957 := by
    simpa [prefixWord, tailWord_1166957, baseEnd_1166957] using wordTrace_append hprefix tailTrace_1166957
  have hstable : (prefixWord ++ tailWord_1166957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1166957).length < 2 ^ (prefixWord ++ tailWord_1166957).sum := by decide
  have hdescent : baseEnd_1166957 < baseStart_1166957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1166957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167000 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 2, 5]
def baseStart_1167000 : Nat := 118140960795 + 1167000 * 2 ^ 59
def prefixEnd_1167000 : Nat := 4983230072969 + 3 ^ 40 * 1167000 * 2
def baseEnd_1167000 : Nat := 399487949198026227222047

theorem tailTrace_1167000 : CollatzResearch.WordTrace tailWord_1167000 prefixEnd_1167000 399487949198026227222047 := by
  unfold tailWord_1167000
  simp only [CollatzResearch.WordTrace]
  refine ⟨21281993386082891288705227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28375991181443855051606969 21281993386082891288705227)
  ·
    refine ⟨31922990079124336933057841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21281993386082891288705227 31922990079124336933057841)
    ·
      refine ⟨23942242559343252699793381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31922990079124336933057841 23942242559343252699793381)
      ·
        refine ⟨4489170479876859881211259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23942242559343252699793381 4489170479876859881211259)
        ·
          refine ⟨6733755719815289821816889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4489170479876859881211259 6733755719815289821816889)
          ·
            refine ⟨5050316789861467366362667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6733755719815289821816889 5050316789861467366362667)
            ·
              refine ⟨7575475184792201049544001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5050316789861467366362667 7575475184792201049544001)
              ·
                refine ⟨5681606388594150787158001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7575475184792201049544001 5681606388594150787158001)
                ·
                  refine ⟨4261204791445613090368501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5681606388594150787158001 4261204791445613090368501)
                  ·
                    refine ⟨399487949198026227222047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4261204791445613090368501 399487949198026227222047)
                    ·
                      rfl

theorem cell22_1167000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_1167000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167000 prefixEnd_1167000 := by exact prefixLift 1167000
  have htrace : WordTrace (prefixWord ++ tailWord_1167000) baseStart_1167000 baseEnd_1167000 := by
    simpa [prefixWord, tailWord_1167000, baseEnd_1167000] using wordTrace_append hprefix tailTrace_1167000
  have hstable : (prefixWord ++ tailWord_1167000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167000).length < 2 ^ (prefixWord ++ tailWord_1167000).sum := by decide
  have hdescent : baseEnd_1167000 < baseStart_1167000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167006 : List Nat := [4, 3, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_1167006 : Nat := 118140960795 + 1167006 * 2 ^ 59
def prefixEnd_1167006 : Nat := 4983230072969 + 3 ^ 40 * 1167006 * 2
def baseEnd_1167006 : Nat := 399490003120644211572029

theorem tailTrace_1167006 : CollatzResearch.WordTrace tailWord_1167006 prefixEnd_1167006 399490003120644211572029 := by
  unfold tailWord_1167006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5320525701268005700266109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28376137073429363734752581 5320525701268005700266109)
  ·
    refine ⟨1995197137975502137599791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5320525701268005700266109 1995197137975502137599791)
    ·
      refine ⟨2992795706963253206399687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1995197137975502137599791 2992795706963253206399687)
      ·
        refine ⟨4489193560444879809599531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2992795706963253206399687 4489193560444879809599531)
        ·
          refine ⟨6733790340667319714399297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4489193560444879809599531 6733790340667319714399297)
          ·
            refine ⟨5050342755500489785799473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6733790340667319714399297 5050342755500489785799473)
            ·
              refine ⟨3787757066625367339349605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5050342755500489785799473 3787757066625367339349605)
              ·
                refine ⟨710204449992256376128051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3787757066625367339349605 710204449992256376128051)
                ·
                  refine ⟨1065306674988384564192077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 710204449992256376128051 1065306674988384564192077)
                  ·
                    refine ⟨399490003120644211572029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1065306674988384564192077 399490003120644211572029)
                    ·
                      rfl

theorem cell22_1167006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_1167006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167006 prefixEnd_1167006 := by exact prefixLift 1167006
  have htrace : WordTrace (prefixWord ++ tailWord_1167006) baseStart_1167006 baseEnd_1167006 := by
    simpa [prefixWord, tailWord_1167006, baseEnd_1167006] using wordTrace_append hprefix tailTrace_1167006
  have hstable : (prefixWord ++ tailWord_1167006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167006).length < 2 ^ (prefixWord ++ tailWord_1167006).sum := by decide
  have hdescent : baseEnd_1167006 < baseStart_1167006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167064 : List Nat := [2, 1, 2, 2, 3, 1, 5, 2, 4]
def baseStart_1167064 : Nat := 118140960795 + 1167064 * 2 ^ 59
def prefixEnd_1167064 : Nat := 4983230072969 + 3 ^ 40 * 1167064 * 2
def baseEnd_1167064 : Nat := 133169952568650464540617

theorem tailTrace_1167064 : CollatzResearch.WordTrace tailWord_1167064 prefixEnd_1167064 133169952568650464540617 := by
  unfold tailWord_1167064
  simp only [CollatzResearch.WordTrace]
  refine ⟨21283160521966960753870123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28377547362622614338493497 21283160521966960753870123)
  ·
    refine ⟨31924740782950441130805185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21283160521966960753870123 31924740782950441130805185)
    ·
      refine ⟨23943555587212830848103889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31924740782950441130805185 23943555587212830848103889)
      ·
        refine ⟨17957666690409623136077917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23943555587212830848103889 17957666690409623136077917)
        ·
          refine ⟨6734125008903608676029219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17957666690409623136077917 6734125008903608676029219)
          ·
            refine ⟨10101187513355413014043829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6734125008903608676029219 10101187513355413014043829)
            ·
              refine ⟨946986329377069970066609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10101187513355413014043829 946986329377069970066609)
              ·
                refine ⟨710239747032802477549957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 946986329377069970066609 710239747032802477549957)
                ·
                  refine ⟨133169952568650464540617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 710239747032802477549957 133169952568650464540617)
                  ·
                    rfl

theorem cell22_1167064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 4].length) (baseStart_1167064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167064 prefixEnd_1167064 := by exact prefixLift 1167064
  have htrace : WordTrace (prefixWord ++ tailWord_1167064) baseStart_1167064 baseEnd_1167064 := by
    simpa [prefixWord, tailWord_1167064, baseEnd_1167064] using wordTrace_append hprefix tailTrace_1167064
  have hstable : (prefixWord ++ tailWord_1167064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167064).length < 2 ^ (prefixWord ++ tailWord_1167064).sum := by decide
  have hdescent : baseEnd_1167064 < baseStart_1167064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167094 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_1167094 : Nat := 118140960795 + 1167094 * 2 ^ 59
def prefixEnd_1167094 : Nat := 4983230072969 + 3 ^ 40 * 1167094 * 2
def baseEnd_1167094 : Nat := 399520127319041315371759

theorem tailTrace_1167094 : CollatzResearch.WordTrace tailWord_1167094 prefixEnd_1167094 399520127319041315371759 := by
  unfold tailWord_1167094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2660463452114077289458271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28378276822550157754221557 2660463452114077289458271)
  ·
    refine ⟨3990695178171115934187407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2660463452114077289458271 3990695178171115934187407)
    ·
      refine ⟨5986042767256673901281111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3990695178171115934187407 5986042767256673901281111)
      ·
        refine ⟨8979064150885010851921667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5986042767256673901281111 8979064150885010851921667)
        ·
          refine ⟨13468596226327516277882501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8979064150885010851921667 13468596226327516277882501)
          ·
            refine ⟨2525361792436409302102969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13468596226327516277882501 2525361792436409302102969)
            ·
              refine ⟨1894021344327306976577227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2525361792436409302102969 1894021344327306976577227)
              ·
                refine ⟨2841032016490960464865841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894021344327306976577227 2841032016490960464865841)
                ·
                  refine ⟨2130774012368220348649381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2841032016490960464865841 2130774012368220348649381)
                  ·
                    refine ⟨399520127319041315371759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2130774012368220348649381 399520127319041315371759)
                    ·
                      rfl

theorem cell22_1167094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_1167094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167094 prefixEnd_1167094 := by exact prefixLift 1167094
  have htrace : WordTrace (prefixWord ++ tailWord_1167094) baseStart_1167094 baseEnd_1167094 := by
    simpa [prefixWord, tailWord_1167094, baseEnd_1167094] using wordTrace_append hprefix tailTrace_1167094
  have hstable : (prefixWord ++ tailWord_1167094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167094).length < 2 ^ (prefixWord ++ tailWord_1167094).sum := by decide
  have hdescent : baseEnd_1167094 < baseStart_1167094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167137 : List Nat := [1, 2, 3, 2, 1, 3, 2, 3, 5]
def baseStart_1167137 : Nat := 118140960795 + 1167137 * 2 ^ 59
def prefixEnd_1167137 : Nat := 4983230072969 + 3 ^ 40 * 1167137 * 2
def baseEnd_1167137 : Nat := 133178282365934512182209

theorem tailTrace_1167137 : CollatzResearch.WordTrace tailWord_1167137 prefixEnd_1167137 133178282365934512182209 := by
  unfold tailWord_1167137
  simp only [CollatzResearch.WordTrace]
  refine ⟨42568983572669454975147665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28379322381779636650098443 42568983572669454975147665)
  ·
    refine ⟨31926737679502091231360749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42568983572669454975147665 31926737679502091231360749)
    ·
      refine ⟨11972526629813284211760281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31926737679502091231360749 11972526629813284211760281)
      ·
        refine ⟨8979394972359963158820211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11972526629813284211760281 8979394972359963158820211)
        ·
          refine ⟨13469092458539944738230317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8979394972359963158820211 13469092458539944738230317)
          ·
            refine ⟨5050909671952479276836369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13469092458539944738230317 5050909671952479276836369)
            ·
              refine ⟨3788182253964359457627277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5050909671952479276836369 3788182253964359457627277)
              ·
                refine ⟨1420568345236634796610229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3788182253964359457627277 1420568345236634796610229)
                ·
                  refine ⟨133178282365934512182209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1420568345236634796610229 133178282365934512182209)
                  ·
                    rfl

theorem cell22_1167137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 5].length) (baseStart_1167137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167137 prefixEnd_1167137 := by exact prefixLift 1167137
  have htrace : WordTrace (prefixWord ++ tailWord_1167137) baseStart_1167137 baseEnd_1167137 := by
    simpa [prefixWord, tailWord_1167137, baseEnd_1167137] using wordTrace_append hprefix tailTrace_1167137
  have hstable : (prefixWord ++ tailWord_1167137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167137).length < 2 ^ (prefixWord ++ tailWord_1167137).sum := by decide
  have hdescent : baseEnd_1167137 < baseStart_1167137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167158 : List Nat := [5, 1, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_1167158 : Nat := 118140960795 + 1167158 * 2 ^ 59
def prefixEnd_1167158 : Nat := 4983230072969 + 3 ^ 40 * 1167158 * 2
def baseEnd_1167158 : Nat := 399542035826966481771563

theorem tailTrace_1167158 : CollatzResearch.WordTrace tailWord_1167158 prefixEnd_1167158 399542035826966481771563 := by
  unfold tailWord_1167158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2660609344099585972603883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28379833003728917041108085 2660609344099585972603883)
  ·
    refine ⟨3990914016149378958905825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2660609344099585972603883 3990914016149378958905825)
    ·
      refine ⟨2993185512112034219179369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3990914016149378958905825 2993185512112034219179369)
      ·
        refine ⟨2244889134084025664384527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2993185512112034219179369 2244889134084025664384527)
        ·
          refine ⟨3367333701126038496576791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2244889134084025664384527 3367333701126038496576791)
          ·
            refine ⟨5051000551689057744865187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3367333701126038496576791 5051000551689057744865187)
            ·
              refine ⟨7576500827533586617297781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5051000551689057744865187 7576500827533586617297781)
              ·
                refine ⟨710296952581273745371667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7576500827533586617297781 710296952581273745371667)
                ·
                  refine ⟨1065445428871910618057501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 710296952581273745371667 1065445428871910618057501)
                  ·
                    refine ⟨399542035826966481771563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1065445428871910618057501 399542035826966481771563)
                    ·
                      rfl

theorem cell22_1167158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_1167158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167158 prefixEnd_1167158 := by exact prefixLift 1167158
  have htrace : WordTrace (prefixWord ++ tailWord_1167158) baseStart_1167158 baseEnd_1167158 := by
    simpa [prefixWord, tailWord_1167158, baseEnd_1167158] using wordTrace_append hprefix tailTrace_1167158
  have hstable : (prefixWord ++ tailWord_1167158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167158).length < 2 ^ (prefixWord ++ tailWord_1167158).sum := by decide
  have hdescent : baseEnd_1167158 < baseStart_1167158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167212 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 1, 6]
def baseStart_1167212 : Nat := 118140960795 + 1167212 * 2 ^ 59
def prefixEnd_1167212 : Nat := 4983230072969 + 3 ^ 40 * 1167212 * 2
def baseEnd_1167212 : Nat := 399560521130528340921397

theorem tailTrace_1167212 : CollatzResearch.WordTrace tailWord_1167212 prefixEnd_1167212 399560521130528340921397 := by
  unfold tailWord_1167212
  simp only [CollatzResearch.WordTrace]
  refine ⟨21285859523698871392063945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28381146031598495189418593 21285859523698871392063945)
  ·
    refine ⟨15964394642774153544047959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21285859523698871392063945 15964394642774153544047959)
    ·
      refine ⟨23946591964161230316071939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15964394642774153544047959 23946591964161230316071939)
      ·
        refine ⟨35919887946241845474107909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23946591964161230316071939 35919887946241845474107909)
        ·
          refine ⟨6734978989920346026395233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35919887946241845474107909 6734978989920346026395233)
          ·
            refine ⟨5051234242440259519796425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6734978989920346026395233 5051234242440259519796425)
            ·
              refine ⟨3788425681830194639847319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5051234242440259519796425 3788425681830194639847319)
              ·
                refine ⟨5682638522745291959770979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3788425681830194639847319 5682638522745291959770979)
                ·
                  refine ⟨8523957784117937939656469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5682638522745291959770979 8523957784117937939656469)
                  ·
                    refine ⟨399560521130528340921397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8523957784117937939656469 399560521130528340921397)
                    ·
                      rfl

theorem cell22_1167212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_1167212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167212 prefixEnd_1167212 := by exact prefixLift 1167212
  have htrace : WordTrace (prefixWord ++ tailWord_1167212) baseStart_1167212 baseEnd_1167212 := by
    simpa [prefixWord, tailWord_1167212, baseEnd_1167212] using wordTrace_append hprefix tailTrace_1167212
  have hstable : (prefixWord ++ tailWord_1167212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167212).length < 2 ^ (prefixWord ++ tailWord_1167212).sum := by decide
  have hdescent : baseEnd_1167212 < baseStart_1167212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167233 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 6]
def baseStart_1167233 : Nat := 118140960795 + 1167233 * 2 ^ 59
def prefixEnd_1167233 : Nat := 4983230072969 + 3 ^ 40 * 1167233 * 2
def baseEnd_1167233 : Nat := 133189236619897095382111

theorem tailTrace_1167233 : CollatzResearch.WordTrace tailWord_1167233 prefixEnd_1167233 133189236619897095382111 := by
  unfold tailWord_1167233
  simp only [CollatzResearch.WordTrace]
  refine ⟨42572484980321663370642353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28381656653547775580428235 42572484980321663370642353)
  ·
    refine ⟨31929363735241247527981765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42572484980321663370642353 31929363735241247527981765)
    ·
      refine ⟨5986755700357733911496581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31929363735241247527981765 5986755700357733911496581)
      ·
        refine ⟨1122516693817075108405609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5986755700357733911496581 1122516693817075108405609)
        ·
          refine ⟨841887520362806331304207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1122516693817075108405609 841887520362806331304207)
          ·
            refine ⟨1262831280544209496956311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841887520362806331304207 1262831280544209496956311)
            ·
              refine ⟨1894246920816314245434467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262831280544209496956311 1894246920816314245434467)
              ·
                refine ⟨2841370381224471368151701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894246920816314245434467 2841370381224471368151701)
                ·
                  refine ⟨133189236619897095382111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2841370381224471368151701 133189236619897095382111)
                  ·
                    rfl

theorem cell22_1167233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 6].length) (baseStart_1167233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167233 prefixEnd_1167233 := by exact prefixLift 1167233
  have htrace : WordTrace (prefixWord ++ tailWord_1167233) baseStart_1167233 baseEnd_1167233 := by
    simpa [prefixWord, tailWord_1167233, baseEnd_1167233] using wordTrace_append hprefix tailTrace_1167233
  have hstable : (prefixWord ++ tailWord_1167233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167233).length < 2 ^ (prefixWord ++ tailWord_1167233).sum := by decide
  have hdescent : baseEnd_1167233 < baseStart_1167233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167278 : List Nat := [4, 1, 5, 1, 2, 9]
def baseStart_1167278 : Nat := 118140960795 + 1167278 * 2 ^ 59
def prefixEnd_1167278 : Nat := 4983230072969 + 3 ^ 40 * 1167278 * 2
def baseEnd_1167278 : Nat := 4933124867646002083595

theorem tailTrace_1167278 : CollatzResearch.WordTrace tailWord_1167278 prefixEnd_1167278 4933124867646002083595 := by
  unfold tailWord_1167278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5321765783144829507003811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28382750843439090704020325 5321765783144829507003811)
  ·
    refine ⟨7982648674717244260505717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5321765783144829507003811 7982648674717244260505717)
    ·
      refine ⟨748373313254741649422411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7982648674717244260505717 748373313254741649422411)
      ·
        refine ⟨1122559969882112474133617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748373313254741649422411 1122559969882112474133617)
        ·
          refine ⟨841919977411584355600213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1122559969882112474133617 841919977411584355600213)
          ·
            refine ⟨4933124867646002083595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 841919977411584355600213 4933124867646002083595)
            ·
              rfl

theorem cell22_1167278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 9].length) (baseStart_1167278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167278 prefixEnd_1167278 := by exact prefixLift 1167278
  have htrace : WordTrace (prefixWord ++ tailWord_1167278) baseStart_1167278 baseEnd_1167278 := by
    simpa [prefixWord, tailWord_1167278, baseEnd_1167278] using wordTrace_append hprefix tailTrace_1167278
  have hstable : (prefixWord ++ tailWord_1167278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167278).length < 2 ^ (prefixWord ++ tailWord_1167278).sum := by decide
  have hdescent : baseEnd_1167278 < baseStart_1167278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167287 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 2, 5]
def baseStart_1167287 : Nat := 118140960795 + 1167287 * 2 ^ 59
def prefixEnd_1167287 : Nat := 4983230072969 + 3 ^ 40 * 1167287 * 2
def baseEnd_1167287 : Nat := 399586195163253145296167

theorem tailTrace_1167287 : CollatzResearch.WordTrace tailWord_1167287 prefixEnd_1167287 399586195163253145296167 := by
  unfold tailWord_1167287
  simp only [CollatzResearch.WordTrace]
  refine ⟨42574454522126030593108115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28382969681417353728738743 42574454522126030593108115)
  ·
    refine ⟨63861681783189045889662173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42574454522126030593108115 63861681783189045889662173)
    ·
      refine ⟨23948130668695892208623315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63861681783189045889662173 23948130668695892208623315)
      ·
        refine ⟨35922196003043838312934973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23948130668695892208623315 35922196003043838312934973)
        ·
          refine ⟨13470823501141439367350615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35922196003043838312934973 13470823501141439367350615)
          ·
            refine ⟨20206235251712159051025923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13470823501141439367350615 20206235251712159051025923)
            ·
              refine ⟨30309352877568238576538885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20206235251712159051025923 30309352877568238576538885)
              ·
                refine ⟨5683003664544044733101041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30309352877568238576538885 5683003664544044733101041)
                ·
                  refine ⟨4262252748408033549825781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5683003664544044733101041 4262252748408033549825781)
                  ·
                    refine ⟨399586195163253145296167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4262252748408033549825781 399586195163253145296167)
                    ·
                      rfl

theorem cell22_1167287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_1167287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167287 prefixEnd_1167287 := by exact prefixLift 1167287
  have htrace : WordTrace (prefixWord ++ tailWord_1167287) baseStart_1167287 baseEnd_1167287 := by
    simpa [prefixWord, tailWord_1167287, baseEnd_1167287] using wordTrace_append hprefix tailTrace_1167287
  have hstable : (prefixWord ++ tailWord_1167287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167287).length < 2 ^ (prefixWord ++ tailWord_1167287).sum := by decide
  have hdescent : baseEnd_1167287 < baseStart_1167287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167289 : List Nat := [1, 2, 1, 4, 2, 1, 4, 2, 5]
def baseStart_1167289 : Nat := 118140960795 + 1167289 * 2 ^ 59
def prefixEnd_1167289 : Nat := 4983230072969 + 3 ^ 40 * 1167289 * 2
def baseEnd_1167289 : Nat := 133195626601375268915387

theorem tailTrace_1167289 : CollatzResearch.WordTrace tailWord_1167289 prefixEnd_1167289 133195626601375268915387 := by
  unfold tailWord_1167289
  simp only [CollatzResearch.WordTrace]
  refine ⟨42574527468118784934680921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28383018312079189956453947 42574527468118784934680921)
  ·
    refine ⟨31930895601089088701010691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42574527468118784934680921 31930895601089088701010691)
    ·
      refine ⟨47896343401633633051516037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31930895601089088701010691 47896343401633633051516037)
      ·
        refine ⟨8980564387806306197159257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47896343401633633051516037 8980564387806306197159257)
        ·
          refine ⟨6735423290854729647869443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8980564387806306197159257 6735423290854729647869443)
          ·
            refine ⟨10103134936282094471804165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6735423290854729647869443 10103134936282094471804165)
            ·
              refine ⟨1894337800552892713463281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10103134936282094471804165 1894337800552892713463281)
              ·
                refine ⟨1420753350414669535097461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1894337800552892713463281 1420753350414669535097461)
                ·
                  refine ⟨133195626601375268915387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1420753350414669535097461 133195626601375268915387)
                  ·
                    rfl

theorem cell22_1167289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 5].length) (baseStart_1167289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167289 prefixEnd_1167289 := by exact prefixLift 1167289
  have htrace : WordTrace (prefixWord ++ tailWord_1167289) baseStart_1167289 baseEnd_1167289 := by
    simpa [prefixWord, tailWord_1167289, baseEnd_1167289] using wordTrace_append hprefix tailTrace_1167289
  have hstable : (prefixWord ++ tailWord_1167289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167289).length < 2 ^ (prefixWord ++ tailWord_1167289).sum := by decide
  have hdescent : baseEnd_1167289 < baseStart_1167289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167293 : List Nat := [1, 4, 1, 2, 3, 2, 1, 4, 1, 3]
def baseStart_1167293 : Nat := 118140960795 + 1167293 * 2 ^ 59
def prefixEnd_1167293 : Nat := 4983230072969 + 3 ^ 40 * 1167293 * 2
def baseEnd_1167293 : Nat := 399588249085871129646149

theorem tailTrace_1167293 : CollatzResearch.WordTrace tailWord_1167293 prefixEnd_1167293 399588249085871129646149 := by
  unfold tailWord_1167293
  simp only [CollatzResearch.WordTrace]
  refine ⟨42574673360104293617826533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28383115573402862411884355 42574673360104293617826533)
  ·
    refine ⟨7982751255019555053342475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42574673360104293617826533 7982751255019555053342475)
    ·
      refine ⟨11974126882529332580013713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7982751255019555053342475 11974126882529332580013713)
      ·
        refine ⟨8980595161896999435010285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11974126882529332580013713 8980595161896999435010285)
        ·
          refine ⟨3367723185711374788128857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8980595161896999435010285 3367723185711374788128857)
          ·
            refine ⟨2525792389283531091096643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3367723185711374788128857 2525792389283531091096643)
            ·
              refine ⟨3788688583925296636644965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525792389283531091096643 3788688583925296636644965)
              ·
                refine ⟨710379109485993119370931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3788688583925296636644965 710379109485993119370931)
                ·
                  refine ⟨1065568664228989679056397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 710379109485993119370931 1065568664228989679056397)
                  ·
                    refine ⟨399588249085871129646149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1065568664228989679056397 399588249085871129646149)
                    ·
                      rfl

theorem cell22_1167293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_1167293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167293 prefixEnd_1167293 := by exact prefixLift 1167293
  have htrace : WordTrace (prefixWord ++ tailWord_1167293) baseStart_1167293 baseEnd_1167293 := by
    simpa [prefixWord, tailWord_1167293, baseEnd_1167293] using wordTrace_append hprefix tailTrace_1167293
  have hstable : (prefixWord ++ tailWord_1167293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167293).length < 2 ^ (prefixWord ++ tailWord_1167293).sum := by decide
  have hdescent : baseEnd_1167293 < baseStart_1167293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167304 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 2, 5]
def baseStart_1167304 : Nat := 118140960795 + 1167304 * 2 ^ 59
def prefixEnd_1167304 : Nat := 4983230072969 + 3 ^ 40 * 1167304 * 2
def baseEnd_1167304 : Nat := 399592014610670767621115

theorem tailTrace_1167304 : CollatzResearch.WordTrace tailWord_1167304 prefixEnd_1167304 399592014610670767621115 := by
  unfold tailWord_1167304
  simp only [CollatzResearch.WordTrace]
  refine ⟨21287537281532221248238483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28383383042042961664317977 21287537281532221248238483)
  ·
    refine ⟨31931305922298331872357725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21287537281532221248238483 31931305922298331872357725)
    ·
      refine ⟨11974239720861874452134147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31931305922298331872357725 11974239720861874452134147)
      ·
        refine ⟨17961359581292811678201221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11974239720861874452134147 17961359581292811678201221)
        ·
          refine ⟨3367754921492402189662729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17961359581292811678201221 3367754921492402189662729)
          ·
            refine ⟨2525816191119301642247047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3367754921492402189662729 2525816191119301642247047)
            ·
              refine ⟨3788724286678952463370571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525816191119301642247047 3788724286678952463370571)
              ·
                refine ⟨5683086430018428695055857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3788724286678952463370571 5683086430018428695055857)
                ·
                  refine ⟨4262314822513821521291893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5683086430018428695055857 4262314822513821521291893)
                  ·
                    refine ⟨399592014610670767621115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4262314822513821521291893 399592014610670767621115)
                    ·
                      rfl

theorem cell22_1167304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_1167304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167304 prefixEnd_1167304 := by exact prefixLift 1167304
  have htrace : WordTrace (prefixWord ++ tailWord_1167304) baseStart_1167304 baseEnd_1167304 := by
    simpa [prefixWord, tailWord_1167304, baseEnd_1167304] using wordTrace_append hprefix tailTrace_1167304
  have hstable : (prefixWord ++ tailWord_1167304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167304).length < 2 ^ (prefixWord ++ tailWord_1167304).sum := by decide
  have hdescent : baseEnd_1167304 < baseStart_1167304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167319 : List Nat := [1, 1, 3, 2, 1, 1, 4, 4, 1, 4]
def baseStart_1167319 : Nat := 118140960795 + 1167319 * 2 ^ 59
def prefixEnd_1167319 : Nat := 4983230072969 + 3 ^ 40 * 1167319 * 2
def baseEnd_1167319 : Nat := 399597149417215728496069

theorem tailTrace_1167319 : CollatzResearch.WordTrace tailWord_1167319 prefixEnd_1167319 399597149417215728496069 := by
  unfold tailWord_1167319
  simp only [CollatzResearch.WordTrace]
  refine ⟨42575621658010100058273011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28383747772006733372182007 42575621658010100058273011)
  ·
    refine ⟨63863432487015150087409517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42575621658010100058273011 63863432487015150087409517)
    ·
      refine ⟨23948787182630681282778569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63863432487015150087409517 23948787182630681282778569)
      ·
        refine ⟨17961590386973010962083927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23948787182630681282778569 17961590386973010962083927)
        ·
          refine ⟨26942385580459516443125891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17961590386973010962083927 26942385580459516443125891)
          ·
            refine ⟨40413578370689274664688837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26942385580459516443125891 40413578370689274664688837)
            ·
              refine ⟨7577545944504238999629157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40413578370689274664688837 7577545944504238999629157)
              ·
                refine ⟨1420789864594544812430467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7577545944504238999629157 1420789864594544812430467)
                ·
                  refine ⟨2131184796891817218645701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420789864594544812430467 2131184796891817218645701)
                  ·
                    refine ⟨399597149417215728496069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2131184796891817218645701 399597149417215728496069)
                    ·
                      rfl

theorem cell22_1167319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_1167319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167319 prefixEnd_1167319 := by exact prefixLift 1167319
  have htrace : WordTrace (prefixWord ++ tailWord_1167319) baseStart_1167319 baseEnd_1167319 := by
    simpa [prefixWord, tailWord_1167319, baseEnd_1167319] using wordTrace_append hprefix tailTrace_1167319
  have hstable : (prefixWord ++ tailWord_1167319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167319).length < 2 ^ (prefixWord ++ tailWord_1167319).sum := by decide
  have hdescent : baseEnd_1167319 < baseStart_1167319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167379 : List Nat := [1, 1, 1, 2, 1, 4, 6, 6]
def baseStart_1167379 : Nat := 118140960795 + 1167379 * 2 ^ 59
def prefixEnd_1167379 : Nat := 4983230072969 + 3 ^ 40 * 1167379 * 2
def baseEnd_1167379 : Nat := 44401965404821730221765

theorem tailTrace_1167379 : CollatzResearch.WordTrace tailWord_1167379 prefixEnd_1167379 44401965404821730221765 := by
  unfold tailWord_1167379
  simp only [CollatzResearch.WordTrace]
  refine ⟨42577810037792730305457191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28385206691861820203638127 42577810037792730305457191)
  ·
    refine ⟨63866715056689095458185787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42577810037792730305457191 63866715056689095458185787)
    ·
      refine ⟨95800072585033643187278681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63866715056689095458185787 95800072585033643187278681)
      ·
        refine ⟨71850054438775232390459011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95800072585033643187278681 71850054438775232390459011)
        ·
          refine ⟨107775081658162848585688517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71850054438775232390459011 107775081658162848585688517)
          ·
            refine ⟨20207827810905534109816597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107775081658162848585688517 20207827810905534109816597)
            ·
              refine ⟨947241928636196911397653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20207827810905534109816597 947241928636196911397653)
              ·
                refine ⟨44401965404821730221765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 947241928636196911397653 44401965404821730221765)
                ·
                  rfl

theorem cell22_1167379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 6].length) (baseStart_1167379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167379 prefixEnd_1167379 := by exact prefixLift 1167379
  have htrace : WordTrace (prefixWord ++ tailWord_1167379) baseStart_1167379 baseEnd_1167379 := by
    simpa [prefixWord, tailWord_1167379, baseEnd_1167379] using wordTrace_append hprefix tailTrace_1167379
  have hstable : (prefixWord ++ tailWord_1167379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167379).length < 2 ^ (prefixWord ++ tailWord_1167379).sum := by decide
  have hdescent : baseEnd_1167379 < baseStart_1167379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167396 : List Nat := [2, 3, 1, 4, 2, 2, 8]
def baseStart_1167396 : Nat := 118140960795 + 1167396 * 2 ^ 59
def prefixEnd_1167396 : Nat := 4983230072969 + 3 ^ 40 * 1167396 * 2
def baseEnd_1167396 : Nat := 14800870670030118308179

theorem tailTrace_1167396 : CollatzResearch.WordTrace tailWord_1167396 prefixEnd_1167396 14800870670030118308179 := by
  unfold tailWord_1167396
  simp only [CollatzResearch.WordTrace]
  refine ⟨21289215039365571104413021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28385620052487428139217361 21289215039365571104413021)
  ·
    refine ⟨7983455639762089164154883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21289215039365571104413021 7983455639762089164154883)
    ·
      refine ⟨11975183459643133746232325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7983455639762089164154883 11975183459643133746232325)
      ·
        refine ⟨2245346898683087577418561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11975183459643133746232325 2245346898683087577418561)
        ·
          refine ⟨1684010174012315683063921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2245346898683087577418561 1684010174012315683063921)
          ·
            refine ⟨1263007630509236762297941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1684010174012315683063921 1263007630509236762297941)
            ·
              refine ⟨14800870670030118308179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1263007630509236762297941 14800870670030118308179)
              ·
                rfl

theorem cell22_1167396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 8].length) (baseStart_1167396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167396 prefixEnd_1167396 := by exact prefixLift 1167396
  have htrace : WordTrace (prefixWord ++ tailWord_1167396) baseStart_1167396 baseEnd_1167396 := by
    simpa [prefixWord, tailWord_1167396, baseEnd_1167396] using wordTrace_append hprefix tailTrace_1167396
  have hstable : (prefixWord ++ tailWord_1167396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167396).length < 2 ^ (prefixWord ++ tailWord_1167396).sum := by decide
  have hdescent : baseEnd_1167396 < baseStart_1167396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167411 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 3, 3]
def baseStart_1167411 : Nat := 118140960795 + 1167411 * 2 ^ 59
def prefixEnd_1167411 : Nat := 4983230072969 + 3 ^ 40 * 1167411 * 2
def baseEnd_1167411 : Nat := 399628642897358155195787

theorem tailTrace_1167411 : CollatzResearch.WordTrace tailWord_1167411 prefixEnd_1167411 399628642897358155195787 := by
  unfold tailWord_1167411
  simp only [CollatzResearch.WordTrace]
  refine ⟨42578977173676799770622087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28385984782451199847081391 42578977173676799770622087)
  ·
    refine ⟨63868465760515199655933131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42578977173676799770622087 63868465760515199655933131)
    ·
      refine ⟨95802698640772799483899697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63868465760515199655933131 95802698640772799483899697)
      ·
        refine ⟨71852023980579599612924773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95802698640772799483899697 71852023980579599612924773)
        ·
          refine ⟨13472254496358674927423395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71852023980579599612924773 13472254496358674927423395)
          ·
            refine ⟨20208381744538012391135093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13472254496358674927423395 20208381744538012391135093)
            ·
              refine ⟨1894535788550438661668915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20208381744538012391135093 1894535788550438661668915)
              ·
                refine ⟨2841803682825657992503373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894535788550438661668915 2841803682825657992503373)
                ·
                  refine ⟨1065676381059621747188765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2841803682825657992503373 1065676381059621747188765)
                  ·
                    refine ⟨399628642897358155195787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1065676381059621747188765 399628642897358155195787)
                    ·
                      rfl

theorem cell22_1167411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 3].length) (baseStart_1167411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167411 prefixEnd_1167411 := by exact prefixLift 1167411
  have htrace : WordTrace (prefixWord ++ tailWord_1167411) baseStart_1167411 baseEnd_1167411 := by
    simpa [prefixWord, tailWord_1167411, baseEnd_1167411] using wordTrace_append hprefix tailTrace_1167411
  have hstable : (prefixWord ++ tailWord_1167411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167411).length < 2 ^ (prefixWord ++ tailWord_1167411).sum := by decide
  have hdescent : baseEnd_1167411 < baseStart_1167411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167417 : List Nat := [1, 2, 1, 5, 4, 1, 2, 1, 2, 3]
def baseStart_1167417 : Nat := 118140960795 + 1167417 * 2 ^ 59
def prefixEnd_1167417 : Nat := 4983230072969 + 3 ^ 40 * 1167417 * 2
def baseEnd_1167417 : Nat := 399630696819976139545769

theorem tailTrace_1167417 : CollatzResearch.WordTrace tailWord_1167417 prefixEnd_1167417 399630696819976139545769 := by
  unfold tailWord_1167417
  simp only [CollatzResearch.WordTrace]
  refine ⟨42579196011655062795340505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28386130674436708530227003 42579196011655062795340505)
  ·
    refine ⟨31934397008741297096505379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42579196011655062795340505 31934397008741297096505379)
    ·
      refine ⟨47901595513111945644758069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31934397008741297096505379 47901595513111945644758069)
      ·
        refine ⟨4490774579354244904196069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47901595513111945644758069 4490774579354244904196069)
        ·
          refine ⟨842020233628920919536763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4490774579354244904196069 842020233628920919536763)
          ·
            refine ⟨1263030350443381379305145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842020233628920919536763 1263030350443381379305145)
            ·
              refine ⟨947272762832536034478859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1263030350443381379305145 947272762832536034478859)
              ·
                refine ⟨1420909144248804051718289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 947272762832536034478859 1420909144248804051718289)
                ·
                  refine ⟨1065681858186603038788717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1420909144248804051718289 1065681858186603038788717)
                  ·
                    refine ⟨399630696819976139545769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1065681858186603038788717 399630696819976139545769)
                    ·
                      rfl

theorem cell22_1167417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 2, 3].length) (baseStart_1167417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167417 prefixEnd_1167417 := by exact prefixLift 1167417
  have htrace : WordTrace (prefixWord ++ tailWord_1167417) baseStart_1167417 baseEnd_1167417 := by
    simpa [prefixWord, tailWord_1167417, baseEnd_1167417] using wordTrace_append hprefix tailTrace_1167417
  have hstable : (prefixWord ++ tailWord_1167417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167417).length < 2 ^ (prefixWord ++ tailWord_1167417).sum := by decide
  have hdescent : baseEnd_1167417 < baseStart_1167417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167516 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 4, 4]
def baseStart_1167516 : Nat := 118140960795 + 1167516 * 2 ^ 59
def prefixEnd_1167516 : Nat := 4983230072969 + 3 ^ 40 * 1167516 * 2
def baseEnd_1167516 : Nat := 399664586543172881320465

theorem tailTrace_1167516 : CollatzResearch.WordTrace tailWord_1167516 prefixEnd_1167516 399664586543172881320465 := by
  unfold tailWord_1167516
  simp only [CollatzResearch.WordTrace]
  refine ⟨21291403419148201351597201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28388537892197601802129601 21291403419148201351597201)
  ·
    refine ⟨15968552564361151013697901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21291403419148201351597201 15968552564361151013697901)
    ·
      refine ⟨5988207211635431630136713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15968552564361151013697901 5988207211635431630136713)
      ·
        refine ⟨4491155408726573722602535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5988207211635431630136713 4491155408726573722602535)
        ·
          refine ⟨6736733113089860583903803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4491155408726573722602535 6736733113089860583903803)
          ·
            refine ⟨10105099669634790875855705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6736733113089860583903803 10105099669634790875855705)
            ·
              refine ⟨7578824752226093156891779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10105099669634790875855705 7578824752226093156891779)
              ·
                refine ⟨11368237128339139735337669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7578824752226093156891779 11368237128339139735337669)
                ·
                  refine ⟨2131544461563588700375813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11368237128339139735337669 2131544461563588700375813)
                  ·
                    refine ⟨399664586543172881320465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2131544461563588700375813 399664586543172881320465)
                    ·
                      rfl

theorem cell22_1167516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_1167516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167516 prefixEnd_1167516 := by exact prefixLift 1167516
  have htrace : WordTrace (prefixWord ++ tailWord_1167516) baseStart_1167516 baseEnd_1167516 := by
    simpa [prefixWord, tailWord_1167516, baseEnd_1167516] using wordTrace_append hprefix tailTrace_1167516
  have hstable : (prefixWord ++ tailWord_1167516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167516).length < 2 ^ (prefixWord ++ tailWord_1167516).sum := by decide
  have hdescent : baseEnd_1167516 < baseStart_1167516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167554 : List Nat := [3, 5, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1167554 : Nat := 118140960795 + 1167554 * 2 ^ 59
def prefixEnd_1167554 : Nat := 4983230072969 + 3 ^ 40 * 1167554 * 2
def baseEnd_1167554 : Nat := 133225864906584482956783

theorem tailTrace_1167554 : CollatzResearch.WordTrace tailWord_1167554 prefixEnd_1167554 133225864906584482956783 := by
  unfold tailWord_1167554
  simp only [CollatzResearch.WordTrace]
  refine ⟨10646048203039683798269429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28389461874772490128718477 10646048203039683798269429)
  ·
    refine ⟨998067019034970356087759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10646048203039683798269429 998067019034970356087759)
    ·
      refine ⟨1497100528552455534131639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 998067019034970356087759 1497100528552455534131639)
      ·
        refine ⟨2245650792828683301197459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1497100528552455534131639 2245650792828683301197459)
        ·
          refine ⟨3368476189243024951796189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2245650792828683301197459 3368476189243024951796189)
          ·
            refine ⟨1263178570966134356923571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3368476189243024951796189 1263178570966134356923571)
            ·
              refine ⟨1894767856449201535385357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263178570966134356923571 1894767856449201535385357)
              ·
                refine ⟨710537946168450575769509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1894767856449201535385357 710537946168450575769509)
                ·
                  refine ⟨133225864906584482956783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 710537946168450575769509 133225864906584482956783)
                  ·
                    rfl

theorem cell22_1167554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1167554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167554 prefixEnd_1167554 := by exact prefixLift 1167554
  have htrace : WordTrace (prefixWord ++ tailWord_1167554) baseStart_1167554 baseEnd_1167554 := by
    simpa [prefixWord, tailWord_1167554, baseEnd_1167554] using wordTrace_append hprefix tailTrace_1167554
  have hstable : (prefixWord ++ tailWord_1167554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167554).length < 2 ^ (prefixWord ++ tailWord_1167554).sum := by decide
  have hdescent : baseEnd_1167554 < baseStart_1167554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167576 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 7]
def baseStart_1167576 : Nat := 118140960795 + 1167576 * 2 ^ 59
def prefixEnd_1167576 : Nat := 4983230072969 + 3 ^ 40 * 1167576 * 2
def baseEnd_1167576 : Nat := 133228375256450908273427

theorem tailTrace_1167576 : CollatzResearch.WordTrace tailWord_1167576 prefixEnd_1167576 133228375256450908273427 := by
  unfold tailWord_1167576
  simp only [CollatzResearch.WordTrace]
  refine ⟨21292497609039516475189291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28389996812052688633585721 21292497609039516475189291)
  ·
    refine ⟨31938746413559274712783937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21292497609039516475189291 31938746413559274712783937)
    ·
      refine ⟨23954059810169456034587953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31938746413559274712783937 23954059810169456034587953)
      ·
        refine ⟨17965544857627092025940965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23954059810169456034587953 17965544857627092025940965)
        ·
          refine ⟨3368539660805079754863931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17965544857627092025940965 3368539660805079754863931)
          ·
            refine ⟨5052809491207619632295897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3368539660805079754863931 5052809491207619632295897)
            ·
              refine ⟨3789607118405714724221923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5052809491207619632295897 3789607118405714724221923)
              ·
                refine ⟨5684410677608572086332885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3789607118405714724221923 5684410677608572086332885)
                ·
                  refine ⟨133228375256450908273427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5684410677608572086332885 133228375256450908273427)
                  ·
                    rfl

theorem cell22_1167576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 7].length) (baseStart_1167576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167576 prefixEnd_1167576 := by exact prefixLift 1167576
  have htrace : WordTrace (prefixWord ++ tailWord_1167576) baseStart_1167576 baseEnd_1167576 := by
    simpa [prefixWord, tailWord_1167576, baseEnd_1167576] using wordTrace_append hprefix tailTrace_1167576
  have hstable : (prefixWord ++ tailWord_1167576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167576).length < 2 ^ (prefixWord ++ tailWord_1167576).sum := by decide
  have hdescent : baseEnd_1167576 < baseStart_1167576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167651 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 1, 6]
def baseStart_1167651 : Nat := 118140960795 + 1167651 * 2 ^ 59
def prefixEnd_1167651 : Nat := 4983230072969 + 3 ^ 40 * 1167651 * 2
def baseEnd_1167651 : Nat := 399710799802077529195051

theorem tailTrace_1167651 : CollatzResearch.WordTrace tailWord_1167651 prefixEnd_1167651 399710799802077529195051 := by
  unfold tailWord_1167651
  simp only [CollatzResearch.WordTrace]
  refine ⟨42587730692807320759358807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28391820461871547172905871 42587730692807320759358807)
  ·
    refine ⟨63881596039210981139038211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42587730692807320759358807 63881596039210981139038211)
    ·
      refine ⟨95822394058816471708557317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63881596039210981139038211 95822394058816471708557317)
      ·
        refine ⟨17966698886028088445354497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95822394058816471708557317 17966698886028088445354497)
        ·
          refine ⟨13475024164521066334015873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17966698886028088445354497 13475024164521066334015873)
          ·
            refine ⟨10106268123390799750511905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13475024164521066334015873 10106268123390799750511905)
            ·
              refine ⟨7579701092543099812883929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10106268123390799750511905 7579701092543099812883929)
              ·
                refine ⟨5684775819407324859662947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7579701092543099812883929 5684775819407324859662947)
                ·
                  refine ⟨8527163729110987289494421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5684775819407324859662947 8527163729110987289494421)
                  ·
                    refine ⟨399710799802077529195051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8527163729110987289494421 399710799802077529195051)
                    ·
                      rfl

theorem cell22_1167651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 6].length) (baseStart_1167651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167651 prefixEnd_1167651 := by exact prefixLift 1167651
  have htrace : WordTrace (prefixWord ++ tailWord_1167651) baseStart_1167651 baseEnd_1167651 := by
    simpa [prefixWord, tailWord_1167651, baseEnd_1167651] using wordTrace_append hprefix tailTrace_1167651
  have hstable : (prefixWord ++ tailWord_1167651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167651).length < 2 ^ (prefixWord ++ tailWord_1167651).sum := by decide
  have hdescent : baseEnd_1167651 < baseStart_1167651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167901 : List Nat := [1, 4, 2, 2, 1, 4, 1, 3, 1, 3]
def baseStart_1167901 : Nat := 118140960795 + 1167901 * 2 ^ 59
def prefixEnd_1167901 : Nat := 4983230072969 + 3 ^ 40 * 1167901 * 2
def baseEnd_1167901 : Nat := 399796379911160210444285

theorem tailTrace_1167901 : CollatzResearch.WordTrace tailWord_1167901 prefixEnd_1167901 399796379911160210444285 := by
  unfold tailWord_1167901
  simp only [CollatzResearch.WordTrace]
  refine ⟨42596848941901613455959557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28397899294601075637306371 42596848941901613455959557)
  ·
    refine ⟨7986909176606552522992417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42596848941901613455959557 7986909176606552522992417)
    ·
      refine ⟨5990181882454914392244313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7986909176606552522992417 5990181882454914392244313)
      ·
        refine ⟨4492636411841185794183235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5990181882454914392244313 4492636411841185794183235)
        ·
          refine ⟨6738954617761778691274853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4492636411841185794183235 6738954617761778691274853)
          ·
            refine ⟨1263553990830333504614035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6738954617761778691274853 1263553990830333504614035)
            ·
              refine ⟨1895330986245500256921053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1263553990830333504614035 1895330986245500256921053)
              ·
                refine ⟨710749119842062596345395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1895330986245500256921053 710749119842062596345395)
                ·
                  refine ⟨1066123679763093894518093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 710749119842062596345395 1066123679763093894518093)
                  ·
                    refine ⟨399796379911160210444285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1066123679763093894518093 399796379911160210444285)
                    ·
                      rfl

theorem cell22_1167901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_1167901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167901 prefixEnd_1167901 := by exact prefixLift 1167901
  have htrace : WordTrace (prefixWord ++ tailWord_1167901) baseStart_1167901 baseEnd_1167901 := by
    simpa [prefixWord, tailWord_1167901, baseEnd_1167901] using wordTrace_append hprefix tailTrace_1167901
  have hstable : (prefixWord ++ tailWord_1167901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167901).length < 2 ^ (prefixWord ++ tailWord_1167901).sum := by decide
  have hdescent : baseEnd_1167901 < baseStart_1167901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1167918 : List Nat := [4, 1, 3, 1, 3, 1, 3, 2, 1, 3]
def baseStart_1167918 : Nat := 118140960795 + 1167918 * 2 ^ 59
def prefixEnd_1167918 : Nat := 4983230072969 + 3 ^ 40 * 1167918 * 2
def baseEnd_1167918 : Nat := 399802199358577832769233

theorem tailTrace_1167918 : CollatzResearch.WordTrace tailWord_1167918 prefixEnd_1167918 399802199358577832769233 := by
  unfold tailWord_1167918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5324683622855003169916051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28398312655226683572885605 5324683622855003169916051)
  ·
    refine ⟨7987025434282504754874077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5324683622855003169916051 7987025434282504754874077)
    ·
      refine ⟨2995134537855939283077779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7987025434282504754874077 2995134537855939283077779)
      ·
        refine ⟨4492701806783908924616669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2995134537855939283077779 4492701806783908924616669)
        ·
          refine ⟨1684763177543965846731251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4492701806783908924616669 1684763177543965846731251)
          ·
            refine ⟨2527144766315948770096877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1684763177543965846731251 2527144766315948770096877)
            ·
              refine ⟨947679287368480788786329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2527144766315948770096877 947679287368480788786329)
              ·
                refine ⟨710759465526360591589747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 947679287368480788786329 710759465526360591589747)
                ·
                  refine ⟨1066139198289540887384621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 710759465526360591589747 1066139198289540887384621)
                  ·
                    refine ⟨399802199358577832769233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1066139198289540887384621 399802199358577832769233)
                    ·
                      rfl

theorem cell22_1167918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_1167918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1167918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1167918 prefixEnd_1167918 := by exact prefixLift 1167918
  have htrace : WordTrace (prefixWord ++ tailWord_1167918) baseStart_1167918 baseEnd_1167918 := by
    simpa [prefixWord, tailWord_1167918, baseEnd_1167918] using wordTrace_append hprefix tailTrace_1167918
  have hstable : (prefixWord ++ tailWord_1167918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1167918).length < 2 ^ (prefixWord ++ tailWord_1167918).sum := by decide
  have hdescent : baseEnd_1167918 < baseStart_1167918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1167918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168032 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 7]
def baseStart_1168032 : Nat := 118140960795 + 1168032 * 2 ^ 59
def prefixEnd_1168032 : Nat := 4983230072969 + 3 ^ 40 * 1168032 * 2
def baseEnd_1168032 : Nat := 133280407962773178472961

theorem tailTrace_1168032 : CollatzResearch.WordTrace tailWord_1168032 prefixEnd_1168032 133280407962773178472961 := by
  unfold tailWord_1168032
  simp only [CollatzResearch.WordTrace]
  refine ⟨21300813452213511414489175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28401084602951348552652233 21300813452213511414489175)
  ·
    refine ⟨31951220178320267121733763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21300813452213511414489175 31951220178320267121733763)
    ·
      refine ⟨47926830267480400682600645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31951220178320267121733763 47926830267480400682600645)
      ·
        refine ⟨8986280675152575127987621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47926830267480400682600645 8986280675152575127987621)
        ·
          refine ⟨1684927626591107836497679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8986280675152575127987621 1684927626591107836497679)
          ·
            refine ⟨2527391439886661754746519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1684927626591107836497679 2527391439886661754746519)
            ·
              refine ⟨3791087159829992632119779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2527391439886661754746519 3791087159829992632119779)
              ·
                refine ⟨5686630739744988948179669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3791087159829992632119779 5686630739744988948179669)
                ·
                  refine ⟨133280407962773178472961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5686630739744988948179669 133280407962773178472961)
                  ·
                    rfl

theorem cell22_1168032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 7].length) (baseStart_1168032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168032 prefixEnd_1168032 := by exact prefixLift 1168032
  have htrace : WordTrace (prefixWord ++ tailWord_1168032) baseStart_1168032 baseEnd_1168032 := by
    simpa [prefixWord, tailWord_1168032, baseEnd_1168032] using wordTrace_append hprefix tailTrace_1168032
  have hstable : (prefixWord ++ tailWord_1168032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168032).length < 2 ^ (prefixWord ++ tailWord_1168032).sum := by decide
  have hdescent : baseEnd_1168032 < baseStart_1168032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168105 : List Nat := [1, 2, 1, 1, 1, 2, 5, 9]
def baseStart_1168105 : Nat := 118140960795 + 1168105 * 2 ^ 59
def prefixEnd_1168105 : Nat := 4983230072969 + 3 ^ 40 * 1168105 * 2
def baseEnd_1168105 : Nat := 44429579253352408704851

theorem tailTrace_1168105 : CollatzResearch.WordTrace tailWord_1168105 prefixEnd_1168105 44429579253352408704851 := by
  unfold tailWord_1168105
  simp only [CollatzResearch.WordTrace]
  refine ⟨42604289433162556296385769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28402859622108370864257179 42604289433162556296385769)
  ·
    refine ⟨31953217074871917222289327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42604289433162556296385769 31953217074871917222289327)
    ·
      refine ⟨47929825612307875833433991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31953217074871917222289327 47929825612307875833433991)
      ·
        refine ⟨71894738418461813750150987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47929825612307875833433991 71894738418461813750150987)
        ·
          refine ⟨107842107627692720625226481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71894738418461813750150987 107842107627692720625226481)
          ·
            refine ⟨80881580720769540468919861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107842107627692720625226481 80881580720769540468919861)
            ·
              refine ⟨7582648192572144418961237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80881580720769540468919861 7582648192572144418961237)
              ·
                refine ⟨44429579253352408704851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7582648192572144418961237 44429579253352408704851)
                ·
                  rfl

theorem cell22_1168105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 9].length) (baseStart_1168105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168105 prefixEnd_1168105 := by exact prefixLift 1168105
  have htrace : WordTrace (prefixWord ++ tailWord_1168105) baseStart_1168105 baseEnd_1168105 := by
    simpa [prefixWord, tailWord_1168105, baseEnd_1168105] using wordTrace_append hprefix tailTrace_1168105
  have hstable : (prefixWord ++ tailWord_1168105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168105).length < 2 ^ (prefixWord ++ tailWord_1168105).sum := by decide
  have hdescent : baseEnd_1168105 < baseStart_1168105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168124 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 2, 4]
def baseStart_1168124 : Nat := 118140960795 + 1168124 * 2 ^ 59
def prefixEnd_1168124 : Nat := 4983230072969 + 3 ^ 40 * 1168124 * 2
def baseEnd_1168124 : Nat := 399872717368461962118601

theorem tailTrace_1168124 : CollatzResearch.WordTrace tailWord_1168124 prefixEnd_1168124 399872717368461962118601 := by
  unfold tailWord_1168124
  simp only [CollatzResearch.WordTrace]
  refine ⟨21302491210046861270663713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28403321613395815027551617 21302491210046861270663713)
  ·
    refine ⟨15976868407535145952997785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21302491210046861270663713 15976868407535145952997785)
    ·
      refine ⟨11982651305651359464748339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15976868407535145952997785 11982651305651359464748339)
      ·
        refine ⟨17973976958477039197122509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11982651305651359464748339 17973976958477039197122509)
        ·
          refine ⟨6740241359428889698920941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17973976958477039197122509 6740241359428889698920941)
          ·
            refine ⟨2527590509785833637095353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6740241359428889698920941 2527590509785833637095353)
            ·
              refine ⟨1895692882339375227821515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2527590509785833637095353 1895692882339375227821515)
              ·
                refine ⟨2843539323509062841732273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1895692882339375227821515 2843539323509062841732273)
                ·
                  refine ⟨2132654492631797131299205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2843539323509062841732273 2132654492631797131299205)
                  ·
                    refine ⟨399872717368461962118601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2132654492631797131299205 399872717368461962118601)
                    ·
                      rfl

theorem cell22_1168124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_1168124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168124 prefixEnd_1168124 := by exact prefixLift 1168124
  have htrace : WordTrace (prefixWord ++ tailWord_1168124) baseStart_1168124 baseEnd_1168124 := by
    simpa [prefixWord, tailWord_1168124, baseEnd_1168124] using wordTrace_append hprefix tailTrace_1168124
  have hstable : (prefixWord ++ tailWord_1168124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168124).length < 2 ^ (prefixWord ++ tailWord_1168124).sum := by decide
  have hdescent : baseEnd_1168124 < baseStart_1168124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168154 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 3, 3]
def baseStart_1168154 : Nat := 118140960795 + 1168154 * 2 ^ 59
def prefixEnd_1168154 : Nat := 4983230072969 + 3 ^ 40 * 1168154 * 2
def baseEnd_1168154 : Nat := 399882986981551883868509

theorem tailTrace_1168154 : CollatzResearch.WordTrace tailWord_1168154 prefixEnd_1168154 399882986981551883868509 := by
  unfold tailWord_1168154
  simp only [CollatzResearch.WordTrace]
  refine ⟨10651519152496259416229879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28404051073323358443279677 10651519152496259416229879)
  ·
    refine ⟨15977278728744389124344819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10651519152496259416229879 15977278728744389124344819)
    ·
      refine ⟨23965918093116583686517229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15977278728744389124344819 23965918093116583686517229)
      ·
        refine ⟨8987219284918718882443961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23965918093116583686517229 8987219284918718882443961)
        ·
          refine ⟨6740414463689039161832971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8987219284918718882443961 6740414463689039161832971)
          ·
            refine ⟨10110621695533558742749457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6740414463689039161832971 10110621695533558742749457)
            ·
              refine ⟨7582966271650169057062093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10110621695533558742749457 7582966271650169057062093)
              ·
                refine ⟨2843612351868813396398285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7582966271650169057062093 2843612351868813396398285)
                ·
                  refine ⟨1066354631950805023649357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2843612351868813396398285 1066354631950805023649357)
                  ·
                    refine ⟨399882986981551883868509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1066354631950805023649357 399882986981551883868509)
                    ·
                      rfl

theorem cell22_1168154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_1168154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168154 prefixEnd_1168154 := by exact prefixLift 1168154
  have htrace : WordTrace (prefixWord ++ tailWord_1168154) baseStart_1168154 baseEnd_1168154 := by
    simpa [prefixWord, tailWord_1168154, baseEnd_1168154] using wordTrace_append hprefix tailTrace_1168154
  have hstable : (prefixWord ++ tailWord_1168154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168154).length < 2 ^ (prefixWord ++ tailWord_1168154).sum := by decide
  have hdescent : baseEnd_1168154 < baseStart_1168154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168173 : List Nat := [1, 5, 3, 2, 1, 1, 3, 6]
def baseStart_1168173 : Nat := 118140960795 + 1168173 * 2 ^ 59
def prefixEnd_1168173 : Nat := 4983230072969 + 3 ^ 40 * 1168173 * 2
def baseEnd_1168173 : Nat := 44432165674426907515939

theorem tailTrace_1168173 : CollatzResearch.WordTrace tailWord_1168173 prefixEnd_1168173 44432165674426907515939 := by
  unfold tailWord_1168173
  simp only [CollatzResearch.WordTrace]
  refine ⟨42606769596916203909861173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28404513064610802606574115 42606769596916203909861173)
  ·
    refine ⟨3994384649710894116549485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42606769596916203909861173 3994384649710894116549485)
    ·
      refine ⟨1497894243641585293706057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3994384649710894116549485 1497894243641585293706057)
      ·
        refine ⟨1123420682731188970279543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1497894243641585293706057 1123420682731188970279543)
        ·
          refine ⟨1685131024096783455419315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1123420682731188970279543 1685131024096783455419315)
          ·
            refine ⟨2527696536145175183128973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1685131024096783455419315 2527696536145175183128973)
            ·
              refine ⟨947886201054440693673365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2527696536145175183128973 947886201054440693673365)
              ·
                refine ⟨44432165674426907515939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 947886201054440693673365 44432165674426907515939)
                ·
                  rfl

theorem cell22_1168173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 6].length) (baseStart_1168173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168173 prefixEnd_1168173 := by exact prefixLift 1168173
  have htrace : WordTrace (prefixWord ++ tailWord_1168173) baseStart_1168173 baseEnd_1168173 := by
    simpa [prefixWord, tailWord_1168173, baseEnd_1168173] using wordTrace_append hprefix tailTrace_1168173
  have hstable : (prefixWord ++ tailWord_1168173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168173).length < 2 ^ (prefixWord ++ tailWord_1168173).sum := by decide
  have hdescent : baseEnd_1168173 < baseStart_1168173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168197 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 5, 4]
def baseStart_1168197 : Nat := 118140960795 + 1168197 * 2 ^ 59
def prefixEnd_1168197 : Nat := 4983230072969 + 3 ^ 40 * 1168197 * 2
def baseEnd_1168197 : Nat := 399897706760314105043377

theorem tailTrace_1168197 : CollatzResearch.WordTrace tailWord_1168197 prefixEnd_1168197 399897706760314105043377 := by
  unfold tailWord_1168197
  simp only [CollatzResearch.WordTrace]
  refine ⟨42607644948829256008734845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28405096632552837339156563 42607644948829256008734845)
  ·
    refine ⟨15977866855810971003275567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42607644948829256008734845 15977866855810971003275567)
    ·
      refine ⟨23966800283716456504913351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15977866855810971003275567 23966800283716456504913351)
      ·
        refine ⟨35950200425574684757370027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23966800283716456504913351 35950200425574684757370027)
        ·
          refine ⟨53925300638362027136055041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35950200425574684757370027 53925300638362027136055041)
          ·
            refine ⟨40443975478771520352041281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53925300638362027136055041 40443975478771520352041281)
            ·
              refine ⟨30332981609078640264030961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40443975478771520352041281 30332981609078640264030961)
              ·
                refine ⟨22749736206808980198023221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30332981609078640264030961 22749736206808980198023221)
                ·
                  refine ⟨2132787769388341893564677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22749736206808980198023221 2132787769388341893564677)
                  ·
                    refine ⟨399897706760314105043377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2132787769388341893564677 399897706760314105043377)
                    ·
                      rfl

theorem cell22_1168197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_1168197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168197 prefixEnd_1168197 := by exact prefixLift 1168197
  have htrace : WordTrace (prefixWord ++ tailWord_1168197) baseStart_1168197 baseEnd_1168197 := by
    simpa [prefixWord, tailWord_1168197, baseEnd_1168197] using wordTrace_append hprefix tailTrace_1168197
  have hstable : (prefixWord ++ tailWord_1168197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168197).length < 2 ^ (prefixWord ++ tailWord_1168197).sum := by decide
  have hdescent : baseEnd_1168197 < baseStart_1168197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168231 : List Nat := [1, 1, 5, 1, 2, 3, 2, 2, 1, 4]
def baseStart_1168231 : Nat := 118140960795 + 1168231 * 2 ^ 59
def prefixEnd_1168231 : Nat := 4983230072969 + 3 ^ 40 * 1168231 * 2
def baseEnd_1168231 : Nat := 399909345655149349693273

theorem tailTrace_1168231 : CollatzResearch.WordTrace tailWord_1168231 prefixEnd_1168231 399909345655149349693273 := by
  unfold tailWord_1168231
  simp only [CollatzResearch.WordTrace]
  refine ⟨42608885030706079815472547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28405923353804053210315031 42608885030706079815472547)
  ·
    refine ⟨63913327546059119723208821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42608885030706079815472547 63913327546059119723208821)
    ·
      refine ⟨5991874457443042474050827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63913327546059119723208821 5991874457443042474050827)
      ·
        refine ⟨8987811686164563711076241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5991874457443042474050827 8987811686164563711076241)
        ·
          refine ⟨6740858764623422783307181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8987811686164563711076241 6740858764623422783307181)
          ·
            refine ⟨2527822036733783543740193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6740858764623422783307181 2527822036733783543740193)
            ·
              refine ⟨1895866527550337657805145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2527822036733783543740193 1895866527550337657805145)
              ·
                refine ⟨1421899895662753243353859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1895866527550337657805145 1421899895662753243353859)
                ·
                  refine ⟨2132849843494129865030789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421899895662753243353859 2132849843494129865030789)
                  ·
                    refine ⟨399909345655149349693273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2132849843494129865030789 399909345655149349693273)
                    ·
                      rfl

theorem cell22_1168231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_1168231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168231 prefixEnd_1168231 := by exact prefixLift 1168231
  have htrace : WordTrace (prefixWord ++ tailWord_1168231) baseStart_1168231 baseEnd_1168231 := by
    simpa [prefixWord, tailWord_1168231, baseEnd_1168231] using wordTrace_append hprefix tailTrace_1168231
  have hstable : (prefixWord ++ tailWord_1168231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168231).length < 2 ^ (prefixWord ++ tailWord_1168231).sum := by decide
  have hdescent : baseEnd_1168231 < baseStart_1168231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168259 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 2, 4]
def baseStart_1168259 : Nat := 118140960795 + 1168259 * 2 ^ 59
def prefixEnd_1168259 : Nat := 4983230072969 + 3 ^ 40 * 1168259 * 2
def baseEnd_1168259 : Nat := 399918930627366609993187

theorem tailTrace_1168259 : CollatzResearch.WordTrace tailWord_1168259 prefixEnd_1168259 399918930627366609993187 := by
  unfold tailWord_1168259
  simp only [CollatzResearch.WordTrace]
  refine ⟨42609906274604640597491831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28406604183069760398327887 42609906274604640597491831)
  ·
    refine ⟨63914859411906960896237747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42609906274604640597491831 63914859411906960896237747)
    ·
      refine ⟨95872289117860441344356621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63914859411906960896237747 95872289117860441344356621)
      ·
        refine ⟨35952108419197665504133733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95872289117860441344356621 35952108419197665504133733)
        ·
          refine ⟨6741020328599562282025075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35952108419197665504133733 6741020328599562282025075)
          ·
            refine ⟨10111530492899343423037613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6741020328599562282025075 10111530492899343423037613)
            ·
              refine ⟨3791823934837253783639105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10111530492899343423037613 3791823934837253783639105)
              ·
                refine ⟨2843867951127940337729329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3791823934837253783639105 2843867951127940337729329)
                ·
                  refine ⟨2132900963345955253296997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2843867951127940337729329 2132900963345955253296997)
                  ·
                    refine ⟨399918930627366609993187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2132900963345955253296997 399918930627366609993187)
                    ·
                      rfl

theorem cell22_1168259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 4].length) (baseStart_1168259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168259 prefixEnd_1168259 := by exact prefixLift 1168259
  have htrace : WordTrace (prefixWord ++ tailWord_1168259) baseStart_1168259 baseEnd_1168259 := by
    simpa [prefixWord, tailWord_1168259, baseEnd_1168259] using wordTrace_append hprefix tailTrace_1168259
  have hstable : (prefixWord ++ tailWord_1168259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168259).length < 2 ^ (prefixWord ++ tailWord_1168259).sum := by decide
  have hdescent : baseEnd_1168259 < baseStart_1168259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168263 : List Nat := [1, 1, 4, 2, 3, 2, 3, 2, 4]
def baseStart_1168263 : Nat := 118140960795 + 1168263 * 2 ^ 59
def prefixEnd_1168263 : Nat := 4983230072969 + 3 ^ 40 * 1168263 * 2
def baseEnd_1168263 : Nat := 133306766636370644297725

theorem tailTrace_1168263 : CollatzResearch.WordTrace tailWord_1168263 prefixEnd_1168263 133306766636370644297725 := by
  unfold tailWord_1168263
  simp only [CollatzResearch.WordTrace]
  refine ⟨42610052166590149280637443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28406701444393432853758295 42610052166590149280637443)
  ·
    refine ⟨63915078249885223920956165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42610052166590149280637443 63915078249885223920956165)
    ·
      refine ⟨11984077171853479485179281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63915078249885223920956165 11984077171853479485179281)
      ·
        refine ⟨8988057878890109613884461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11984077171853479485179281 8988057878890109613884461)
        ·
          refine ⟨3370521704583791105206673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8988057878890109613884461 3370521704583791105206673)
          ·
            refine ⟨2527891278437843328905005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3370521704583791105206673 2527891278437843328905005)
            ·
              refine ⟨947959229414191248339377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2527891278437843328905005 947959229414191248339377)
              ·
                refine ⟨710969422060643436254533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 947959229414191248339377 710969422060643436254533)
                ·
                  refine ⟨133306766636370644297725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 710969422060643436254533 133306766636370644297725)
                  ·
                    rfl

theorem cell22_1168263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 4].length) (baseStart_1168263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168263 prefixEnd_1168263 := by exact prefixLift 1168263
  have htrace : WordTrace (prefixWord ++ tailWord_1168263) baseStart_1168263 baseEnd_1168263 := by
    simpa [prefixWord, tailWord_1168263, baseEnd_1168263] using wordTrace_append hprefix tailTrace_1168263
  have hstable : (prefixWord ++ tailWord_1168263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168263).length < 2 ^ (prefixWord ++ tailWord_1168263).sum := by decide
  have hdescent : baseEnd_1168263 < baseStart_1168263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168334 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_1168334 : Nat := 118140960795 + 1168334 * 2 ^ 59
def prefixEnd_1168334 : Nat := 4983230072969 + 3 ^ 40 * 1168334 * 2
def baseEnd_1168334 : Nat := 399944604660091414367957

theorem tailTrace_1168334 : CollatzResearch.WordTrace tailWord_1168334 prefixEnd_1168334 399944604660091414367957 := by
  unfold tailWord_1168334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5326580218666616050809007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28408427832888618937648037 5326580218666616050809007)
  ·
    refine ⟨7989870327999924076213511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5326580218666616050809007 7989870327999924076213511)
    ·
      refine ⟨11984805491999886114320267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7989870327999924076213511 11984805491999886114320267)
      ·
        refine ⟨17977208237999829171480401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11984805491999886114320267 17977208237999829171480401)
        ·
          refine ⟨13482906178499871878610301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17977208237999829171480401 13482906178499871878610301)
          ·
            refine ⟨5056089816937451954478863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13482906178499871878610301 5056089816937451954478863)
            ·
              refine ⟨7584134725406177931718295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5056089816937451954478863 7584134725406177931718295)
              ·
                refine ⟨11376202088109266897577443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7584134725406177931718295 11376202088109266897577443)
                ·
                  refine ⟨17064303132163900346366165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11376202088109266897577443 17064303132163900346366165)
                  ·
                    refine ⟨399944604660091414367957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17064303132163900346366165 399944604660091414367957)
                    ·
                      rfl

theorem cell22_1168334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_1168334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168334 prefixEnd_1168334 := by exact prefixLift 1168334
  have htrace : WordTrace (prefixWord ++ tailWord_1168334) baseStart_1168334 baseEnd_1168334 := by
    simpa [prefixWord, tailWord_1168334, baseEnd_1168334] using wordTrace_append hprefix tailTrace_1168334
  have hstable : (prefixWord ++ tailWord_1168334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168334).length < 2 ^ (prefixWord ++ tailWord_1168334).sum := by decide
  have hdescent : baseEnd_1168334 < baseStart_1168334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168357 : List Nat := [1, 3, 1, 6, 1, 1, 2, 3, 1, 3]
def baseStart_1168357 : Nat := 118140960795 + 1168357 * 2 ^ 59
def prefixEnd_1168357 : Nat := 4983230072969 + 3 ^ 40 * 1168357 * 2
def baseEnd_1168357 : Nat := 399952478030127021042887

theorem tailTrace_1168357 : CollatzResearch.WordTrace tailWord_1168357 prefixEnd_1168357 399952478030127021042887 := by
  unfold tailWord_1168357
  simp only [CollatzResearch.WordTrace]
  refine ⟨42613480628249603334559325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28408987085499735556372883 42613480628249603334559325)
  ·
    refine ⟨15980055235593601250459747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42613480628249603334559325 15980055235593601250459747)
    ·
      refine ⟨23970082853390401875689621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15980055235593601250459747 23970082853390401875689621)
      ·
        refine ⟨1123597633752675087922951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23970082853390401875689621 1123597633752675087922951)
        ·
          refine ⟨1685396450629012631884427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1123597633752675087922951 1685396450629012631884427)
          ·
            refine ⟨2528094675943518947826641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1685396450629012631884427 2528094675943518947826641)
            ·
              refine ⟨1896071006957639210869981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2528094675943518947826641 1896071006957639210869981)
              ·
                refine ⟨711026627609114704076243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1896071006957639210869981 711026627609114704076243)
                ·
                  refine ⟨1066539941413672056114365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711026627609114704076243 1066539941413672056114365)
                  ·
                    refine ⟨399952478030127021042887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1066539941413672056114365 399952478030127021042887)
                    ·
                      rfl

theorem cell22_1168357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 1, 3].length) (baseStart_1168357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168357 prefixEnd_1168357 := by exact prefixLift 1168357
  have htrace : WordTrace (prefixWord ++ tailWord_1168357) baseStart_1168357 baseEnd_1168357 := by
    simpa [prefixWord, tailWord_1168357, baseEnd_1168357] using wordTrace_append hprefix tailTrace_1168357
  have hstable : (prefixWord ++ tailWord_1168357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168357).length < 2 ^ (prefixWord ++ tailWord_1168357).sum := by decide
  have hdescent : baseEnd_1168357 < baseStart_1168357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168370 : List Nat := [3, 2, 1, 5, 1, 2, 1, 2, 5]
def baseStart_1168370 : Nat := 118140960795 + 1168370 * 2 ^ 59
def prefixEnd_1168370 : Nat := 4983230072969 + 3 ^ 40 * 1168370 * 2
def baseEnd_1168370 : Nat := 133318976065266440155949

theorem tailTrace_1168370 : CollatzResearch.WordTrace tailWord_1168370 prefixEnd_1168370 133318976065266440155949 := by
  unfold tailWord_1168370
  simp only [CollatzResearch.WordTrace]
  refine ⟨10653488694300626638695641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28409303184801671036521709 10653488694300626638695641)
  ·
    refine ⟨7990116520725469979021731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10653488694300626638695641 7990116520725469979021731)
    ·
      refine ⟨11985174781088204968532597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7990116520725469979021731 11985174781088204968532597)
      ·
        refine ⟨1123610135727019215799931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11985174781088204968532597 1123610135727019215799931)
        ·
          refine ⟨1685415203590528823699897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1123610135727019215799931 1685415203590528823699897)
          ·
            refine ⟨1264061402692896617774923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1685415203590528823699897 1264061402692896617774923)
            ·
              refine ⟨1896092104039344926662385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264061402692896617774923 1896092104039344926662385)
              ·
                refine ⟨1422069078029508694996789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1896092104039344926662385 1422069078029508694996789)
                ·
                  refine ⟨133318976065266440155949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1422069078029508694996789 133318976065266440155949)
                  ·
                    rfl

theorem cell22_1168370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_1168370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168370 prefixEnd_1168370 := by exact prefixLift 1168370
  have htrace : WordTrace (prefixWord ++ tailWord_1168370) baseStart_1168370 baseEnd_1168370 := by
    simpa [prefixWord, tailWord_1168370, baseEnd_1168370] using wordTrace_append hprefix tailTrace_1168370
  have hstable : (prefixWord ++ tailWord_1168370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168370).length < 2 ^ (prefixWord ++ tailWord_1168370).sum := by decide
  have hdescent : baseEnd_1168370 < baseStart_1168370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168396 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 1, 5]
def baseStart_1168396 : Nat := 118140960795 + 1168396 * 2 ^ 59
def prefixEnd_1168396 : Nat := 4983230072969 + 3 ^ 40 * 1168396 * 2
def baseEnd_1168396 : Nat := 399965828527143919317767

theorem tailTrace_1168396 : CollatzResearch.WordTrace tailWord_1168396 prefixEnd_1168396 399965828527143919317767 := by
  unfold tailWord_1168396
  simp only [CollatzResearch.WordTrace]
  refine ⟨21307451537554156497614521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28409935383405541996819361 21307451537554156497614521)
  ·
    refine ⟨15980588653165617373210891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21307451537554156497614521 15980588653165617373210891)
    ·
      refine ⟨23970882979748426059816337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15980588653165617373210891 23970882979748426059816337)
      ·
        refine ⟨17978162234811319544862253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23970882979748426059816337 17978162234811319544862253)
        ·
          refine ⟨6741810838054244829323345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17978162234811319544862253 6741810838054244829323345)
          ·
            refine ⟨5056358128540683621992509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6741810838054244829323345 5056358128540683621992509)
            ·
              refine ⟨1896134298202756358247191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5056358128540683621992509 1896134298202756358247191)
              ·
                refine ⟨2844201447304134537370787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896134298202756358247191 2844201447304134537370787)
                ·
                  refine ⟨4266302170956201806056181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844201447304134537370787 4266302170956201806056181)
                  ·
                    refine ⟨399965828527143919317767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4266302170956201806056181 399965828527143919317767)
                    ·
                      rfl

theorem cell22_1168396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_1168396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168396 prefixEnd_1168396 := by exact prefixLift 1168396
  have htrace : WordTrace (prefixWord ++ tailWord_1168396) baseStart_1168396 baseEnd_1168396 := by
    simpa [prefixWord, tailWord_1168396, baseEnd_1168396] using wordTrace_append hprefix tailTrace_1168396
  have hstable : (prefixWord ++ tailWord_1168396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168396).length < 2 ^ (prefixWord ++ tailWord_1168396).sum := by decide
  have hdescent : baseEnd_1168396 < baseStart_1168396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168439 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 2, 6]
def baseStart_1168439 : Nat := 118140960795 + 1168439 * 2 ^ 59
def prefixEnd_1168439 : Nat := 4983230072969 + 3 ^ 40 * 1168439 * 2
def baseEnd_1168439 : Nat := 399980548305906140492635

theorem tailTrace_1168439 : CollatzResearch.WordTrace tailWord_1168439 prefixEnd_1168439 399980548305906140492635 := by
  unfold tailWord_1168439
  simp only [CollatzResearch.WordTrace]
  refine ⟨42616471413952531339044371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28410980942635020892696247 42616471413952531339044371)
  ·
    refine ⟨63924707120928797008566557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42616471413952531339044371 63924707120928797008566557)
    ·
      refine ⟨23971765170348298878212459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63924707120928797008566557 23971765170348298878212459)
      ·
        refine ⟨35957647755522448317318689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23971765170348298878212459 35957647755522448317318689)
        ·
          refine ⟨26968235816641836237989017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35957647755522448317318689 26968235816641836237989017)
          ·
            refine ⟨20226176862481377178491763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26968235816641836237989017 20226176862481377178491763)
            ·
              refine ⟨30339265293722065767737645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20226176862481377178491763 30339265293722065767737645)
              ·
                refine ⟨11377224485145774662901617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30339265293722065767737645 11377224485145774662901617)
                ·
                  refine ⟨8532918363859330997176213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11377224485145774662901617 8532918363859330997176213)
                  ·
                    refine ⟨399980548305906140492635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8532918363859330997176213 399980548305906140492635)
                    ·
                      rfl

theorem cell22_1168439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_1168439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168439 prefixEnd_1168439 := by exact prefixLift 1168439
  have htrace : WordTrace (prefixWord ++ tailWord_1168439) baseStart_1168439 baseEnd_1168439 := by
    simpa [prefixWord, tailWord_1168439, baseEnd_1168439] using wordTrace_append hprefix tailTrace_1168439
  have hstable : (prefixWord ++ tailWord_1168439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168439).length < 2 ^ (prefixWord ++ tailWord_1168439).sum := by decide
  have hdescent : baseEnd_1168439 < baseStart_1168439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168499 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 12]
def baseStart_1168499 : Nat := 118140960795 + 1168499 * 2 ^ 59
def prefixEnd_1168499 : Nat := 4983230072969 + 3 ^ 40 * 1168499 * 2
def baseEnd_1168499 : Nat := 133333695844028661330817

theorem tailTrace_1168499 : CollatzResearch.WordTrace tailWord_1168499 prefixEnd_1168499 133333695844028661330817 := by
  unfold tailWord_1168499
  simp only [CollatzResearch.WordTrace]
  refine ⟨42618659793735161586228551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28412439862490107724152367 42618659793735161586228551)
  ·
    refine ⟨63927989690602742379342827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42618659793735161586228551 63927989690602742379342827)
    ·
      refine ⟨95891984535904113569014241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63927989690602742379342827 95891984535904113569014241)
      ·
        refine ⟨71918988401928085176760681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95891984535904113569014241 71918988401928085176760681)
        ·
          refine ⟨53939241301446063882570511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71918988401928085176760681 53939241301446063882570511)
          ·
            refine ⟨80908861952169095823855767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53939241301446063882570511 80908861952169095823855767)
            ·
              refine ⟨121363292928253643735783651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80908861952169095823855767 121363292928253643735783651)
              ·
                refine ⟨182044939392380465603675477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121363292928253643735783651 182044939392380465603675477)
                ·
                  refine ⟨133333695844028661330817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 182044939392380465603675477 133333695844028661330817)
                  ·
                    rfl

theorem cell22_1168499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 12].length) (baseStart_1168499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168499 prefixEnd_1168499 := by exact prefixLift 1168499
  have htrace : WordTrace (prefixWord ++ tailWord_1168499) baseStart_1168499 baseEnd_1168499 := by
    simpa [prefixWord, tailWord_1168499, baseEnd_1168499] using wordTrace_append hprefix tailTrace_1168499
  have hstable : (prefixWord ++ tailWord_1168499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168499).length < 2 ^ (prefixWord ++ tailWord_1168499).sum := by decide
  have hdescent : baseEnd_1168499 < baseStart_1168499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168516 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 8]
def baseStart_1168516 : Nat := 118140960795 + 1168516 * 2 ^ 59
def prefixEnd_1168516 : Nat := 4983230072969 + 3 ^ 40 * 1168516 * 2
def baseEnd_1168516 : Nat := 133335635659834535439133

theorem tailTrace_1168516 : CollatzResearch.WordTrace tailWord_1168516 prefixEnd_1168516 133335635659834535439133 := by
  unfold tailWord_1168516
  simp only [CollatzResearch.WordTrace]
  refine ⟨21309639917336786744798701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28412853223115715659731601 21309639917336786744798701)
  ·
    refine ⟨7991114969001295029299513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21309639917336786744798701 7991114969001295029299513)
    ·
      refine ⟨5993336226750971271974635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7991114969001295029299513 5993336226750971271974635)
      ·
        refine ⟨8990004340126456907961953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5993336226750971271974635 8990004340126456907961953)
        ·
          refine ⟨6742503255094842680971465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8990004340126456907961953 6742503255094842680971465)
          ·
            refine ⟨5056877441321132010728599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6742503255094842680971465 5056877441321132010728599)
            ·
              refine ⟨7585316161981698016092899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5056877441321132010728599 7585316161981698016092899)
              ·
                refine ⟨11377974242972547024139349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7585316161981698016092899 11377974242972547024139349)
                ·
                  refine ⟨133335635659834535439133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11377974242972547024139349 133335635659834535439133)
                  ·
                    rfl

theorem cell22_1168516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_1168516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168516 prefixEnd_1168516 := by exact prefixLift 1168516
  have htrace : WordTrace (prefixWord ++ tailWord_1168516) baseStart_1168516 baseEnd_1168516 := by
    simpa [prefixWord, tailWord_1168516, baseEnd_1168516] using wordTrace_append hprefix tailTrace_1168516
  have hstable : (prefixWord ++ tailWord_1168516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168516).length < 2 ^ (prefixWord ++ tailWord_1168516).sum := by decide
  have hdescent : baseEnd_1168516 < baseStart_1168516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168531 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 1, 5]
def baseStart_1168531 : Nat := 118140960795 + 1168531 * 2 ^ 59
def prefixEnd_1168531 : Nat := 4983230072969 + 3 ^ 40 * 1168531 * 2
def baseEnd_1168531 : Nat := 400012041786048567192353

theorem tailTrace_1168531 : CollatzResearch.WordTrace tailWord_1168531 prefixEnd_1168531 400012041786048567192353 := by
  unfold tailWord_1168531
  simp only [CollatzResearch.WordTrace]
  refine ⟨42619826929619231051393447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28413217953079487367595631 42619826929619231051393447)
  ·
    refine ⟨63929740394428846577090171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42619826929619231051393447 63929740394428846577090171)
    ·
      refine ⟨95894610591643269865635257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63929740394428846577090171 95894610591643269865635257)
      ·
        refine ⟨71920957943732452399226443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95894610591643269865635257 71920957943732452399226443)
        ·
          refine ⟨107881436915598678598839665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71920957943732452399226443 107881436915598678598839665)
          ·
            refine ⟨80911077686699008949129749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107881436915598678598839665 80911077686699008949129749)
            ·
              refine ⟨3792706766564016044490457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80911077686699008949129749 3792706766564016044490457)
              ·
                refine ⟨2844530074923012033367843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3792706766564016044490457 2844530074923012033367843)
                ·
                  refine ⟨4266795112384518050051765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844530074923012033367843 4266795112384518050051765)
                  ·
                    refine ⟨400012041786048567192353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4266795112384518050051765 400012041786048567192353)
                    ·
                      rfl

theorem cell22_1168531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 5].length) (baseStart_1168531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168531 prefixEnd_1168531 := by exact prefixLift 1168531
  have htrace : WordTrace (prefixWord ++ tailWord_1168531) baseStart_1168531 baseEnd_1168531 := by
    simpa [prefixWord, tailWord_1168531, baseEnd_1168531] using wordTrace_append hprefix tailTrace_1168531
  have hstable : (prefixWord ++ tailWord_1168531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168531).length < 2 ^ (prefixWord ++ tailWord_1168531).sum := by decide
  have hdescent : baseEnd_1168531 < baseStart_1168531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168535 : List Nat := [1, 1, 3, 3, 3, 1, 4, 1, 1, 4]
def baseStart_1168535 : Nat := 118140960795 + 1168535 * 2 ^ 59
def prefixEnd_1168535 : Nat := 4983230072969 + 3 ^ 40 * 1168535 * 2
def baseEnd_1168535 : Nat := 400013411067793890092341

theorem tailTrace_1168535 : CollatzResearch.WordTrace tailWord_1168535 prefixEnd_1168535 400013411067793890092341 := by
  unfold tailWord_1168535
  simp only [CollatzResearch.WordTrace]
  refine ⟨42619972821604739734539059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28413315214403159823026039 42619972821604739734539059)
  ·
    refine ⟨63929959232407109601808589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42619972821604739734539059 63929959232407109601808589)
    ·
      refine ⟨23973734712152666100678221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63929959232407109601808589 23973734712152666100678221)
      ·
        refine ⟨8990150517057249787754333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23973734712152666100678221 8990150517057249787754333)
        ·
          refine ⟨3371306443896468670407875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8990150517057249787754333 3371306443896468670407875)
          ·
            refine ⟨5056959665844703005611813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3371306443896468670407875 5056959665844703005611813)
            ·
              refine ⟨948179937345881813552215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5056959665844703005611813 948179937345881813552215)
              ·
                refine ⟨1422269906018822720328323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 948179937345881813552215 1422269906018822720328323)
                ·
                  refine ⟨2133404859028234080492485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1422269906018822720328323 2133404859028234080492485)
                  ·
                    refine ⟨400013411067793890092341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2133404859028234080492485 400013411067793890092341)
                    ·
                      rfl

theorem cell22_1168535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_1168535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168535 prefixEnd_1168535 := by exact prefixLift 1168535
  have htrace : WordTrace (prefixWord ++ tailWord_1168535) baseStart_1168535 baseEnd_1168535 := by
    simpa [prefixWord, tailWord_1168535, baseEnd_1168535] using wordTrace_append hprefix tailTrace_1168535
  have hstable : (prefixWord ++ tailWord_1168535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168535).length < 2 ^ (prefixWord ++ tailWord_1168535).sum := by decide
  have hdescent : baseEnd_1168535 < baseStart_1168535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168681 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 2, 10]
def baseStart_1168681 : Nat := 118140960795 + 1168681 * 2 ^ 59
def prefixEnd_1168681 : Nat := 4983230072969 + 3 ^ 40 * 1168681 * 2
def baseEnd_1168681 : Nat := 400063389851498175941893

theorem tailTrace_1168681 : CollatzResearch.WordTrace tailWord_1168681 prefixEnd_1168681 400063389851498175941893 := by
  unfold tailWord_1168681
  simp only [CollatzResearch.WordTrace]
  refine ⟨42625297879075806669353897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28416865252717204446235931 42625297879075806669353897)
  ·
    refine ⟨31968973409306855002015423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42625297879075806669353897 31968973409306855002015423)
    ·
      refine ⟨47953460113960282503023135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31968973409306855002015423 47953460113960282503023135)
      ·
        refine ⟨71930190170940423754534703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47953460113960282503023135 71930190170940423754534703)
        ·
          refine ⟨107895285256410635631802055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71930190170940423754534703 107895285256410635631802055)
          ·
            refine ⟨161842927884615953447703083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107895285256410635631802055 161842927884615953447703083)
            ·
              refine ⟨242764391826923930171554625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161842927884615953447703083 242764391826923930171554625)
              ·
                refine ⟨182073293870192947628665969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242764391826923930171554625 182073293870192947628665969)
                ·
                  refine ⟨136554970402644710721499477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182073293870192947628665969 136554970402644710721499477)
                  ·
                    refine ⟨400063389851498175941893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 136554970402644710721499477 400063389851498175941893)
                    ·
                      rfl

theorem cell22_1168681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_1168681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168681 prefixEnd_1168681 := by exact prefixLift 1168681
  have htrace : WordTrace (prefixWord ++ tailWord_1168681) baseStart_1168681 baseEnd_1168681 := by
    simpa [prefixWord, tailWord_1168681, baseEnd_1168681] using wordTrace_append hprefix tailTrace_1168681
  have hstable : (prefixWord ++ tailWord_1168681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168681).length < 2 ^ (prefixWord ++ tailWord_1168681).sum := by decide
  have hdescent : baseEnd_1168681 < baseStart_1168681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168685 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 8]
def baseStart_1168685 : Nat := 118140960795 + 1168685 * 2 ^ 59
def prefixEnd_1168685 : Nat := 4983230072969 + 3 ^ 40 * 1168685 * 2
def baseEnd_1168685 : Nat := 133354919711081166280627

theorem tailTrace_1168685 : CollatzResearch.WordTrace tailWord_1168685 prefixEnd_1168685 133354919711081166280627 := by
  unfold tailWord_1168685
  simp only [CollatzResearch.WordTrace]
  refine ⟨42625443771061315352499509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28416962514040876901666339 42625443771061315352499509)
  ·
    refine ⟨3996135353536998314296829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42625443771061315352499509 3996135353536998314296829)
    ·
      refine ⟨1498550757576374367861311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3996135353536998314296829 1498550757576374367861311)
      ·
        refine ⟨2247826136364561551791967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1498550757576374367861311 2247826136364561551791967)
        ·
          refine ⟨3371739204546842327687951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2247826136364561551791967 3371739204546842327687951)
          ·
            refine ⟨5057608806820263491531927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3371739204546842327687951 5057608806820263491531927)
            ·
              refine ⟨7586413210230395237297891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5057608806820263491531927 7586413210230395237297891)
              ·
                refine ⟨11379619815345592855946837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7586413210230395237297891 11379619815345592855946837)
                ·
                  refine ⟨133354919711081166280627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11379619815345592855946837 133354919711081166280627)
                  ·
                    rfl

theorem cell22_1168685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_1168685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168685 prefixEnd_1168685 := by exact prefixLift 1168685
  have htrace : WordTrace (prefixWord ++ tailWord_1168685) baseStart_1168685 baseEnd_1168685 := by
    simpa [prefixWord, tailWord_1168685, baseEnd_1168685] using wordTrace_append hprefix tailTrace_1168685
  have hstable : (prefixWord ++ tailWord_1168685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168685).length < 2 ^ (prefixWord ++ tailWord_1168685).sum := by decide
  have hdescent : baseEnd_1168685 < baseStart_1168685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168698 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 1, 6]
def baseStart_1168698 : Nat := 118140960795 + 1168698 * 2 ^ 59
def prefixEnd_1168698 : Nat := 4983230072969 + 3 ^ 40 * 1168698 * 2
def baseEnd_1168698 : Nat := 400069209298915798266841

theorem tailTrace_1168698 : CollatzResearch.WordTrace tailWord_1168698 prefixEnd_1168698 400069209298915798266841 := by
  unfold tailWord_1168698
  simp only [CollatzResearch.WordTrace]
  refine ⟨10656479480003554643180687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28417278613342812381815165 10656479480003554643180687)
  ·
    refine ⟨15984719220005331964771031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10656479480003554643180687 15984719220005331964771031)
    ·
      refine ⟨23977078830007997947156547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15984719220005331964771031 23977078830007997947156547)
      ·
        refine ⟨35965618245011996920734821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23977078830007997947156547 35965618245011996920734821)
        ·
          refine ⟨6743553420939749422637779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35965618245011996920734821 6743553420939749422637779)
          ·
            refine ⟨10115330131409624133956669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6743553420939749422637779 10115330131409624133956669)
            ·
              refine ⟨3793248799278609050233751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10115330131409624133956669 3793248799278609050233751)
              ·
                refine ⟨5689873198917913575350627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3793248799278609050233751 5689873198917913575350627)
                ·
                  refine ⟨8534809798376870363025941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5689873198917913575350627 8534809798376870363025941)
                  ·
                    refine ⟨400069209298915798266841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8534809798376870363025941 400069209298915798266841)
                    ·
                      rfl

theorem cell22_1168698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_1168698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168698 prefixEnd_1168698 := by exact prefixLift 1168698
  have htrace : WordTrace (prefixWord ++ tailWord_1168698) baseStart_1168698 baseEnd_1168698 := by
    simpa [prefixWord, tailWord_1168698, baseEnd_1168698] using wordTrace_append hprefix tailTrace_1168698
  have hstable : (prefixWord ++ tailWord_1168698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168698).length < 2 ^ (prefixWord ++ tailWord_1168698).sum := by decide
  have hdescent : baseEnd_1168698 < baseStart_1168698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168702 : List Nat := [4, 2, 1, 2, 1, 1, 4, 3, 4]
def baseStart_1168702 : Nat := 118140960795 + 1168702 * 2 ^ 59
def prefixEnd_1168702 : Nat := 4983230072969 + 3 ^ 40 * 1168702 * 2
def baseEnd_1168702 : Nat := 133356859526887040388943

theorem tailTrace_1168702 : CollatzResearch.WordTrace tailWord_1168702 prefixEnd_1168702 133356859526887040388943 := by
  unfold tailWord_1168702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5328257976499965906983545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28417375874666484837245573 5328257976499965906983545)
  ·
    refine ⟨3996193482374974430237659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5328257976499965906983545 3996193482374974430237659)
    ·
      refine ⟨5994290223562461645356489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3996193482374974430237659 5994290223562461645356489)
      ·
        refine ⟨4495717667671846234017367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5994290223562461645356489 4495717667671846234017367)
        ·
          refine ⟨6743576501507769351026051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4495717667671846234017367 6743576501507769351026051)
          ·
            refine ⟨10115364752261654026539077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6743576501507769351026051 10115364752261654026539077)
            ·
              refine ⟨1896630891049060129976077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10115364752261654026539077 1896630891049060129976077)
              ·
                refine ⟨711236584143397548741029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1896630891049060129976077 711236584143397548741029)
                ·
                  refine ⟨133356859526887040388943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 711236584143397548741029 133356859526887040388943)
                  ·
                    rfl

theorem cell22_1168702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_1168702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168702 prefixEnd_1168702 := by exact prefixLift 1168702
  have htrace : WordTrace (prefixWord ++ tailWord_1168702) baseStart_1168702 baseEnd_1168702 := by
    simpa [prefixWord, tailWord_1168702, baseEnd_1168702] using wordTrace_append hprefix tailTrace_1168702
  have hstable : (prefixWord ++ tailWord_1168702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168702).length < 2 ^ (prefixWord ++ tailWord_1168702).sum := by decide
  have hdescent : baseEnd_1168702 < baseStart_1168702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168773 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 4, 5]
def baseStart_1168773 : Nat := 118140960795 + 1168773 * 2 ^ 59
def prefixEnd_1168773 : Nat := 4983230072969 + 3 ^ 40 * 1168773 * 2
def baseEnd_1168773 : Nat := 400094883331640602641611

theorem tailTrace_1168773 : CollatzResearch.WordTrace tailWord_1168773 prefixEnd_1168773 400094883331640602641611 := by
  unfold tailWord_1168773
  simp only [CollatzResearch.WordTrace]
  refine ⟨42628653394742506381702973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28419102263161670921135315 42628653394742506381702973)
  ·
    refine ⟨15985745023028439893138615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42628653394742506381702973 15985745023028439893138615)
    ·
      refine ⟨23978617534542659839707923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15985745023028439893138615 23978617534542659839707923)
      ·
        refine ⟨35967926301813989759561885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23978617534542659839707923 35967926301813989759561885)
        ·
          refine ⟨13487972363180246159835707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35967926301813989759561885 13487972363180246159835707)
          ·
            refine ⟨20231958544770369239753561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13487972363180246159835707 20231958544770369239753561)
            ·
              refine ⟨15173968908577776929815171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20231958544770369239753561 15173968908577776929815171)
              ·
                refine ⟨22760953362866665394722757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15173968908577776929815171 22760953362866665394722757)
                ·
                  refine ⟨4267678755537499761510517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22760953362866665394722757 4267678755537499761510517)
                  ·
                    refine ⟨400094883331640602641611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4267678755537499761510517 400094883331640602641611)
                    ·
                      rfl

theorem cell22_1168773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_1168773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168773 prefixEnd_1168773 := by exact prefixLift 1168773
  have htrace : WordTrace (prefixWord ++ tailWord_1168773) baseStart_1168773 baseEnd_1168773 := by
    simpa [prefixWord, tailWord_1168773, baseEnd_1168773] using wordTrace_append hprefix tailTrace_1168773
  have hstable : (prefixWord ++ tailWord_1168773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168773).length < 2 ^ (prefixWord ++ tailWord_1168773).sum := by decide
  have hdescent : baseEnd_1168773 < baseStart_1168773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168779 : List Nat := [1, 1, 1, 1, 4, 3, 5, 2, 1, 3]
def baseStart_1168779 : Nat := 118140960795 + 1168779 * 2 ^ 59
def prefixEnd_1168779 : Nat := 4983230072969 + 3 ^ 40 * 1168779 * 2
def baseEnd_1168779 : Nat := 400096937254258586991593

theorem tailTrace_1168779 : CollatzResearch.WordTrace tailWord_1168779 prefixEnd_1168779 400096937254258586991593 := by
  unfold tailWord_1168779
  simp only [CollatzResearch.WordTrace]
  refine ⟨42628872232720769406421391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28419248155147179604280927 42628872232720769406421391)
  ·
    refine ⟨63943308349081154109632087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42628872232720769406421391 63943308349081154109632087)
    ·
      refine ⟨95914962523621731164448131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63943308349081154109632087 95914962523621731164448131)
      ·
        refine ⟨143872443785432596746672197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95914962523621731164448131 143872443785432596746672197)
        ·
          refine ⟨26976083209768611890001037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143872443785432596746672197 26976083209768611890001037)
          ·
            refine ⟨10116031203663229458750389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26976083209768611890001037 10116031203663229458750389)
            ·
              refine ⟨948377925343427761757849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10116031203663229458750389 948377925343427761757849)
              ·
                refine ⟨711283444007570821318387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 948377925343427761757849 711283444007570821318387)
                ·
                  refine ⟨1066925166011356231977581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711283444007570821318387 1066925166011356231977581)
                  ·
                    refine ⟨400096937254258586991593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1066925166011356231977581 400096937254258586991593)
                    ·
                      rfl

theorem cell22_1168779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 1, 3].length) (baseStart_1168779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168779 prefixEnd_1168779 := by exact prefixLift 1168779
  have htrace : WordTrace (prefixWord ++ tailWord_1168779) baseStart_1168779 baseEnd_1168779 := by
    simpa [prefixWord, tailWord_1168779, baseEnd_1168779] using wordTrace_append hprefix tailTrace_1168779
  have hstable : (prefixWord ++ tailWord_1168779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168779).length < 2 ^ (prefixWord ++ tailWord_1168779).sum := by decide
  have hdescent : baseEnd_1168779 < baseStart_1168779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168792 : List Nat := [2, 1, 2, 5, 2, 1, 1, 3, 5]
def baseStart_1168792 : Nat := 118140960795 + 1168792 * 2 ^ 59
def prefixEnd_1168792 : Nat := 4983230072969 + 3 ^ 40 * 1168792 * 2
def baseEnd_1168792 : Nat := 133367129139976962138851

theorem tailTrace_1168792 : CollatzResearch.WordTrace tailWord_1168792 prefixEnd_1168792 133367129139976962138851 := by
  unfold tailWord_1168792
  simp only [CollatzResearch.WordTrace]
  refine ⟨21314673190836836313322315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28419564254449115084429753 21314673190836836313322315)
  ·
    refine ⟨31972009786255254469983473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21314673190836836313322315 31972009786255254469983473)
    ·
      refine ⟨23979007339691440852487605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31972009786255254469983473 23979007339691440852487605)
      ·
        refine ⟨2248031938096072579920713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23979007339691440852487605 2248031938096072579920713)
        ·
          refine ⟨1686023953572054434940535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2248031938096072579920713 1686023953572054434940535)
          ·
            refine ⟨2529035930358081652410803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686023953572054434940535 2529035930358081652410803)
            ·
              refine ⟨3793553895537122478616205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529035930358081652410803 3793553895537122478616205)
              ·
                refine ⟨1422582710826420929481077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3793553895537122478616205 1422582710826420929481077)
                ·
                  refine ⟨133367129139976962138851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1422582710826420929481077 133367129139976962138851)
                  ·
                    rfl

theorem cell22_1168792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 5].length) (baseStart_1168792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168792 prefixEnd_1168792 := by exact prefixLift 1168792
  have htrace : WordTrace (prefixWord ++ tailWord_1168792) baseStart_1168792 baseEnd_1168792 := by
    simpa [prefixWord, tailWord_1168792, baseEnd_1168792] using wordTrace_append hprefix tailTrace_1168792
  have hstable : (prefixWord ++ tailWord_1168792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168792).length < 2 ^ (prefixWord ++ tailWord_1168792).sum := by decide
  have hdescent : baseEnd_1168792 < baseStart_1168792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168803 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 8]
def baseStart_1168803 : Nat := 118140960795 + 1168803 * 2 ^ 59
def prefixEnd_1168803 : Nat := 4983230072969 + 3 ^ 40 * 1168803 * 2
def baseEnd_1168803 : Nat := 133368384314910174797173

theorem tailTrace_1168803 : CollatzResearch.WordTrace tailWord_1168803 prefixEnd_1168803 133368384314910174797173 := by
  unfold tailWord_1168803
  simp only [CollatzResearch.WordTrace]
  refine ⟨42629747584633821505295063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28419831723089214336863375 42629747584633821505295063)
  ·
    refine ⟨63944621376950732257942595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42629747584633821505295063 63944621376950732257942595)
    ·
      refine ⟨95916932065426098386913893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63944621376950732257942595 95916932065426098386913893)
      ·
        refine ⟨17984424762267393447546355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95916932065426098386913893 17984424762267393447546355)
        ·
          refine ⟨26976637143401090171319533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17984424762267393447546355 26976637143401090171319533)
          ·
            refine ⟨10116238928775408814244825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26976637143401090171319533 10116238928775408814244825)
            ·
              refine ⟨7587179196581556610683619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10116238928775408814244825 7587179196581556610683619)
              ·
                refine ⟨11380768794872334916025429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7587179196581556610683619 11380768794872334916025429)
                ·
                  refine ⟨133368384314910174797173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11380768794872334916025429 133368384314910174797173)
                  ·
                    rfl

theorem cell22_1168803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 8].length) (baseStart_1168803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168803 prefixEnd_1168803 := by exact prefixLift 1168803
  have htrace : WordTrace (prefixWord ++ tailWord_1168803) baseStart_1168803 baseEnd_1168803 := by
    simpa [prefixWord, tailWord_1168803, baseEnd_1168803] using wordTrace_append hprefix tailTrace_1168803
  have hstable : (prefixWord ++ tailWord_1168803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168803).length < 2 ^ (prefixWord ++ tailWord_1168803).sum := by decide
  have hdescent : baseEnd_1168803 < baseStart_1168803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168805 : List Nat := [1, 3, 1, 2, 1, 1, 2, 6, 1, 4]
def baseStart_1168805 : Nat := 118140960795 + 1168805 * 2 ^ 59
def prefixEnd_1168805 : Nat := 4983230072969 + 3 ^ 40 * 1168805 * 2
def baseEnd_1168805 : Nat := 400105837585603185841513

theorem tailTrace_1168805 : CollatzResearch.WordTrace tailWord_1168805 prefixEnd_1168805 400105837585603185841513 := by
  unfold tailWord_1168805
  simp only [CollatzResearch.WordTrace]
  refine ⟨42629820530626575846867869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28419880353751050564578579 42629820530626575846867869)
  ·
    refine ⟨15986182698984965942575451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42629820530626575846867869 15986182698984965942575451)
    ·
      refine ⟨23979274048477448913863177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15986182698984965942575451 23979274048477448913863177)
      ·
        refine ⟨17984455536358086685397383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23979274048477448913863177 17984455536358086685397383)
        ·
          refine ⟨26976683304537130028096075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17984455536358086685397383 26976683304537130028096075)
          ·
            refine ⟨40465024956805695042144113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26976683304537130028096075 40465024956805695042144113)
            ·
              refine ⟨30348768717604271281608085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40465024956805695042144113 30348768717604271281608085)
              ·
                refine ⟨1422598533637700216325379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30348768717604271281608085 1422598533637700216325379)
                ·
                  refine ⟨2133897800456550324488069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1422598533637700216325379 2133897800456550324488069)
                  ·
                    refine ⟨400105837585603185841513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2133897800456550324488069 400105837585603185841513)
                    ·
                      rfl

theorem cell22_1168805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_1168805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168805 prefixEnd_1168805 := by exact prefixLift 1168805
  have htrace : WordTrace (prefixWord ++ tailWord_1168805) baseStart_1168805 baseEnd_1168805 := by
    simpa [prefixWord, tailWord_1168805, baseEnd_1168805] using wordTrace_append hprefix tailTrace_1168805
  have hstable : (prefixWord ++ tailWord_1168805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168805).length < 2 ^ (prefixWord ++ tailWord_1168805).sum := by decide
  have hdescent : baseEnd_1168805 < baseStart_1168805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168835 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 4, 3]
def baseStart_1168835 : Nat := 118140960795 + 1168835 * 2 ^ 59
def prefixEnd_1168835 : Nat := 4983230072969 + 3 ^ 40 * 1168835 * 2
def baseEnd_1168835 : Nat := 400116107198693107591421

theorem tailTrace_1168835 : CollatzResearch.WordTrace tailWord_1168835 prefixEnd_1168835 400116107198693107591421 := by
  unfold tailWord_1168835
  simp only [CollatzResearch.WordTrace]
  refine ⟨42630914720517890970459959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28420609813678593980306639 42630914720517890970459959)
  ·
    refine ⟨63946372080776836455689939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42630914720517890970459959 63946372080776836455689939)
    ·
      refine ⟨95919558121165254683534909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63946372080776836455689939 95919558121165254683534909)
      ·
        refine ⟨35969834295436970506325591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95919558121165254683534909 35969834295436970506325591)
        ·
          refine ⟨53954751443155455759488387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35969834295436970506325591 53954751443155455759488387)
          ·
            refine ⟨80932127164733183639232581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53954751443155455759488387 80932127164733183639232581)
            ·
              refine ⟨15174773843387471932356109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80932127164733183639232581 15174773843387471932356109)
              ·
                refine ⟨5690540191270301974633541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15174773843387471932356109 5690540191270301974633541)
                ·
                  refine ⟨1066976285863181620243789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5690540191270301974633541 1066976285863181620243789)
                  ·
                    refine ⟨400116107198693107591421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1066976285863181620243789 400116107198693107591421)
                    ·
                      rfl

theorem cell22_1168835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 3].length) (baseStart_1168835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168835 prefixEnd_1168835 := by exact prefixLift 1168835
  have htrace : WordTrace (prefixWord ++ tailWord_1168835) baseStart_1168835 baseEnd_1168835 := by
    simpa [prefixWord, tailWord_1168835, baseEnd_1168835] using wordTrace_append hprefix tailTrace_1168835
  have hstable : (prefixWord ++ tailWord_1168835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168835).length < 2 ^ (prefixWord ++ tailWord_1168835).sum := by decide
  have hdescent : baseEnd_1168835 < baseStart_1168835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168867 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 2, 4]
def baseStart_1168867 : Nat := 118140960795 + 1168867 * 2 ^ 59
def prefixEnd_1168867 : Nat := 4983230072969 + 3 ^ 40 * 1168867 * 2
def baseEnd_1168867 : Nat := 400127061452655690791323

theorem tailTrace_1168867 : CollatzResearch.WordTrace tailWord_1168867 prefixEnd_1168867 400127061452655690791323 := by
  unfold tailWord_1168867
  simp only [CollatzResearch.WordTrace]
  refine ⟨42632081856401960435624855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28421387904267973623749903 42632081856401960435624855)
  ·
    refine ⟨63948122784602940653437283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42632081856401960435624855 63948122784602940653437283)
    ·
      refine ⟨95922184176904410980155925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63948122784602940653437283 95922184176904410980155925)
      ·
        refine ⟨4496352383292394264694809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 95922184176904410980155925 4496352383292394264694809)
        ·
          refine ⟨3372264287469295698521107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4496352383292394264694809 3372264287469295698521107)
          ·
            refine ⟨5058396431203943547781661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3372264287469295698521107 5058396431203943547781661)
            ·
              refine ⟨1896898661701478830418123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5058396431203943547781661 1896898661701478830418123)
              ·
                refine ⟨2845347992552218245627185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896898661701478830418123 2845347992552218245627185)
                ·
                  refine ⟨2134010994414163684220389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2845347992552218245627185 2134010994414163684220389)
                  ·
                    refine ⟨400127061452655690791323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2134010994414163684220389 400127061452655690791323)
                    ·
                      rfl

theorem cell22_1168867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 4].length) (baseStart_1168867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168867 prefixEnd_1168867 := by exact prefixLift 1168867
  have htrace : WordTrace (prefixWord ++ tailWord_1168867) baseStart_1168867 baseEnd_1168867 := by
    simpa [prefixWord, tailWord_1168867, baseEnd_1168867] using wordTrace_append hprefix tailTrace_1168867
  have hstable : (prefixWord ++ tailWord_1168867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168867).length < 2 ^ (prefixWord ++ tailWord_1168867).sum := by decide
  have hdescent : baseEnd_1168867 < baseStart_1168867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168886 : List Nat := [5, 1, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_1168886 : Nat := 118140960795 + 1168886 * 2 ^ 59
def prefixEnd_1168886 : Nat := 4983230072969 + 3 ^ 40 * 1168886 * 2
def baseEnd_1168886 : Nat := 400133565540945974566265

theorem tailTrace_1168886 : CollatzResearch.WordTrace tailWord_1168886 prefixEnd_1168886 400133565540945974566265 := by
  unfold tailWord_1168886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2664548427708320417535407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28421849895555417787044341 2664548427708320417535407)
  ·
    refine ⟨3996822641562480626303111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2664548427708320417535407 3996822641562480626303111)
    ·
      refine ⟨5995233962343720939454667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3996822641562480626303111 5995233962343720939454667)
      ·
        refine ⟨8992850943515581409182001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5995233962343720939454667 8992850943515581409182001)
        ·
          refine ⟨6744638207636686056886501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8992850943515581409182001 6744638207636686056886501)
          ·
            refine ⟨1264619663931878635666219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6744638207636686056886501 1264619663931878635666219)
            ·
              refine ⟨1896929495897817953499329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264619663931878635666219 1896929495897817953499329)
              ·
                refine ⟨1422697121923363465124497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1896929495897817953499329 1422697121923363465124497)
                ·
                  refine ⟨1067022841442522598843373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1422697121923363465124497 1067022841442522598843373)
                  ·
                    refine ⟨400133565540945974566265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1067022841442522598843373 400133565540945974566265)
                    ·
                      rfl

theorem cell22_1168886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_1168886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168886 prefixEnd_1168886 := by exact prefixLift 1168886
  have htrace : WordTrace (prefixWord ++ tailWord_1168886) baseStart_1168886 baseEnd_1168886 := by
    simpa [prefixWord, tailWord_1168886, baseEnd_1168886] using wordTrace_append hprefix tailTrace_1168886
  have hstable : (prefixWord ++ tailWord_1168886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168886).length < 2 ^ (prefixWord ++ tailWord_1168886).sum := by decide
  have hdescent : baseEnd_1168886 < baseStart_1168886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168916 : List Nat := [2, 4, 3, 1, 2, 2, 2, 6]
def baseStart_1168916 : Nat := 118140960795 + 1168916 * 2 ^ 59
def prefixEnd_1168916 : Nat := 4983230072969 + 3 ^ 40 * 1168916 * 2
def baseEnd_1168916 : Nat := 44460426128226210701797

theorem tailTrace_1168916 : CollatzResearch.WordTrace tailWord_1168916 prefixEnd_1168916 44460426128226210701797 := by
  unfold tailWord_1168916
  simp only [CollatzResearch.WordTrace]
  refine ⟨21316934516612220902079301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28422579355482961202772401 21316934516612220902079301)
  ·
    refine ⟨3996925221864791419139869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21316934516612220902079301 3996925221864791419139869)
    ·
      refine ⟨1498846958199296782177451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3996925221864791419139869 1498846958199296782177451)
      ·
        refine ⟨2248270437298945173266177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1498846958199296782177451 2248270437298945173266177)
        ·
          refine ⟨1686202827974208879949633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2248270437298945173266177 1686202827974208879949633)
          ·
            refine ⟨1264652120980656659962225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1686202827974208879949633 1264652120980656659962225)
            ·
              refine ⟨948489090735492494971669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1264652120980656659962225 948489090735492494971669)
              ·
                refine ⟨44460426128226210701797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 948489090735492494971669 44460426128226210701797)
                ·
                  rfl

theorem cell22_1168916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 6].length) (baseStart_1168916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168916 prefixEnd_1168916 := by exact prefixLift 1168916
  have htrace : WordTrace (prefixWord ++ tailWord_1168916) baseStart_1168916 baseEnd_1168916 := by
    simpa [prefixWord, tailWord_1168916, baseEnd_1168916] using wordTrace_append hprefix tailTrace_1168916
  have hstable : (prefixWord ++ tailWord_1168916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168916).length < 2 ^ (prefixWord ++ tailWord_1168916).sum := by decide
  have hdescent : baseEnd_1168916 < baseStart_1168916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168940 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 7, 4]
def baseStart_1168940 : Nat := 118140960795 + 1168940 * 2 ^ 59
def prefixEnd_1168940 : Nat := 4983230072969 + 3 ^ 40 * 1168940 * 2
def baseEnd_1168940 : Nat := 400152050844507833716099

theorem tailTrace_1168940 : CollatzResearch.WordTrace tailWord_1168940 prefixEnd_1168940 400152050844507833716099 := by
  unfold tailWord_1168940
  simp only [CollatzResearch.WordTrace]
  refine ⟨21317372192568746951516137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28423162923424995935354849 21317372192568746951516137)
  ·
    refine ⟨15988029144426560213637103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21317372192568746951516137 15988029144426560213637103)
    ·
      refine ⟨23982043716639840320455655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15988029144426560213637103 23982043716639840320455655)
      ·
        refine ⟨35973065574959760480683483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23982043716639840320455655 35973065574959760480683483)
        ·
          refine ⟨53959598362439640721025225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35973065574959760480683483 53959598362439640721025225)
          ·
            refine ⟨40469698771829730540768919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53959598362439640721025225 40469698771829730540768919)
            ·
              refine ⟨60704548157744595811153379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40469698771829730540768919 60704548157744595811153379)
              ·
                refine ⟨91056822236616893716730069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60704548157744595811153379 91056822236616893716730069)
                ·
                  refine ⟨2134144271170708446485861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 91056822236616893716730069 2134144271170708446485861)
                  ·
                    refine ⟨400152050844507833716099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2134144271170708446485861 400152050844507833716099)
                    ·
                      rfl

theorem cell22_1168940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_1168940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168940 prefixEnd_1168940 := by exact prefixLift 1168940
  have htrace : WordTrace (prefixWord ++ tailWord_1168940) baseStart_1168940 baseEnd_1168940 := by
    simpa [prefixWord, tailWord_1168940, baseEnd_1168940] using wordTrace_append hprefix tailTrace_1168940
  have hstable : (prefixWord ++ tailWord_1168940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168940).length < 2 ^ (prefixWord ++ tailWord_1168940).sum := by decide
  have hdescent : baseEnd_1168940 < baseStart_1168940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1168985 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 1, 6]
def baseStart_1168985 : Nat := 118140960795 + 1168985 * 2 ^ 59
def prefixEnd_1168985 : Nat := 4983230072969 + 3 ^ 40 * 1168985 * 2
def baseEnd_1168985 : Nat := 400167455264142716340961

theorem tailTrace_1168985 : CollatzResearch.WordTrace tailWord_1168985 prefixEnd_1168985 400167455264142716340961 := by
  unfold tailWord_1168985
  simp only [CollatzResearch.WordTrace]
  refine ⟨42636385669974466588420409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28424257113316311058946939 42636385669974466588420409)
  ·
    refine ⟨31977289252480849941315307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42636385669974466588420409 31977289252480849941315307)
    ·
      refine ⟨47965933878721274911972961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31977289252480849941315307 47965933878721274911972961)
      ·
        refine ⟨35974450409040956183979721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47965933878721274911972961 35974450409040956183979721)
        ·
          refine ⟨26980837806780717137984791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35974450409040956183979721 26980837806780717137984791)
          ·
            refine ⟨40471256710171075706977187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26980837806780717137984791 40471256710171075706977187)
            ·
              refine ⟨60706885065256613560465781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40471256710171075706977187 60706885065256613560465781)
              ·
                refine ⟨5691270474867807521293667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60706885065256613560465781 5691270474867807521293667)
                ·
                  refine ⟨8536905712301711281940501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5691270474867807521293667 8536905712301711281940501)
                  ·
                    refine ⟨400167455264142716340961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8536905712301711281940501 400167455264142716340961)
                    ·
                      rfl

theorem cell22_1168985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_1168985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1168985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1168985 prefixEnd_1168985 := by exact prefixLift 1168985
  have htrace : WordTrace (prefixWord ++ tailWord_1168985) baseStart_1168985 baseEnd_1168985 := by
    simpa [prefixWord, tailWord_1168985, baseEnd_1168985] using wordTrace_append hprefix tailTrace_1168985
  have hstable : (prefixWord ++ tailWord_1168985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1168985).length < 2 ^ (prefixWord ++ tailWord_1168985).sum := by decide
  have hdescent : baseEnd_1168985 < baseStart_1168985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1168985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169006 : List Nat := [4, 1, 2, 2, 3, 1, 1, 4, 4]
def baseStart_1169006 : Nat := 118140960795 + 1169006 * 2 ^ 59
def prefixEnd_1169006 : Nat := 4983230072969 + 3 ^ 40 * 1169006 * 2
def baseEnd_1169006 : Nat := 133391547997768553855299

theorem tailTrace_1169006 : CollatzResearch.WordTrace tailWord_1169006 prefixEnd_1169006 133391547997768553855299 := by
  unfold tailWord_1169006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5329643950362298396866859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28424767735265591449956581 5329643950362298396866859)
  ·
    refine ⟨7994465925543447595300289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5329643950362298396866859 7994465925543447595300289)
    ·
      refine ⟨5995849444157585696475217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7994465925543447595300289 5995849444157585696475217)
      ·
        refine ⟨4496887083118189272356413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5995849444157585696475217 4496887083118189272356413)
        ·
          refine ⟨1686332656169320977133655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4496887083118189272356413 1686332656169320977133655)
          ·
            refine ⟨2529498984253981465700483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686332656169320977133655 2529498984253981465700483)
            ·
              refine ⟨3794248476380972198550725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529498984253981465700483 3794248476380972198550725)
              ·
                refine ⟨711421589321432287228261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3794248476380972198550725 711421589321432287228261)
                ·
                  refine ⟨133391547997768553855299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 711421589321432287228261 133391547997768553855299)
                  ·
                    rfl

theorem cell22_1169006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_1169006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169006 prefixEnd_1169006 := by exact prefixLift 1169006
  have htrace : WordTrace (prefixWord ++ tailWord_1169006) baseStart_1169006 baseEnd_1169006 := by
    simpa [prefixWord, tailWord_1169006, baseEnd_1169006] using wordTrace_append hprefix tailTrace_1169006
  have hstable : (prefixWord ++ tailWord_1169006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169006).length < 2 ^ (prefixWord ++ tailWord_1169006).sum := by decide
  have hdescent : baseEnd_1169006 < baseStart_1169006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169015 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 2, 7]
def baseStart_1169015 : Nat := 118140960795 + 1169015 * 2 ^ 59
def prefixEnd_1169015 : Nat := 4983230072969 + 3 ^ 40 * 1169015 * 2
def baseEnd_1169015 : Nat := 400177724877232638090869

theorem tailTrace_1169015 : CollatzResearch.WordTrace tailWord_1169015 prefixEnd_1169015 400177724877232638090869 := by
  unfold tailWord_1169015
  simp only [CollatzResearch.WordTrace]
  refine ⟨42637479859865781712012499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28424986573243854474674999 42637479859865781712012499)
  ·
    refine ⟨63956219789798672568018749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42637479859865781712012499 63956219789798672568018749)
    ·
      refine ⟨23983582421174502213007031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63956219789798672568018749 23983582421174502213007031)
      ·
        refine ⟨35975373631761753319510547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23983582421174502213007031 35975373631761753319510547)
        ·
          refine ⟨53963060447642629979265821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35975373631761753319510547 53963060447642629979265821)
          ·
            refine ⟨20236147667865986242224683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53963060447642629979265821 20236147667865986242224683)
            ·
              refine ⟨30354221501798979363337025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20236147667865986242224683 30354221501798979363337025)
              ·
                refine ⟨22765666126349234522502769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30354221501798979363337025 22765666126349234522502769)
                ·
                  refine ⟨17074249594761925891877077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22765666126349234522502769 17074249594761925891877077)
                  ·
                    refine ⟨400177724877232638090869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17074249594761925891877077 400177724877232638090869)
                    ·
                      rfl

theorem cell22_1169015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_1169015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169015 prefixEnd_1169015 := by exact prefixLift 1169015
  have htrace : WordTrace (prefixWord ++ tailWord_1169015) baseStart_1169015 baseEnd_1169015 := by
    simpa [prefixWord, tailWord_1169015, baseEnd_1169015] using wordTrace_append hprefix tailTrace_1169015
  have hstable : (prefixWord ++ tailWord_1169015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169015).length < 2 ^ (prefixWord ++ tailWord_1169015).sum := by decide
  have hdescent : baseEnd_1169015 < baseStart_1169015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169034 : List Nat := [3, 1, 2, 3, 2, 2, 3, 6]
def baseStart_1169034 : Nat := 118140960795 + 1169034 * 2 ^ 59
def prefixEnd_1169034 : Nat := 4983230072969 + 3 ^ 40 * 1169034 * 2
def baseEnd_1169034 : Nat := 44464914329502546873979

theorem tailTrace_1169034 : CollatzResearch.WordTrace tailWord_1169034 prefixEnd_1169034 44464914329502546873979 := by
  unfold tailWord_1169034
  simp only [CollatzResearch.WordTrace]
  refine ⟨10659543211699236989238539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28425448564531298637969437 10659543211699236989238539)
  ·
    refine ⟨15989314817548855483857809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10659543211699236989238539 15989314817548855483857809)
    ·
      refine ⟨11991986113161641612893357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15989314817548855483857809 11991986113161641612893357)
      ·
        refine ⟨4496994792435615604835009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11991986113161641612893357 4496994792435615604835009)
        ·
          refine ⟨3372746094326711703626257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4496994792435615604835009 3372746094326711703626257)
          ·
            refine ⟨2529559570745033777719693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3372746094326711703626257 2529559570745033777719693)
            ·
              refine ⟨948584839029387666644885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2529559570745033777719693 948584839029387666644885)
              ·
                refine ⟨44464914329502546873979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 948584839029387666644885 44464914329502546873979)
                ·
                  rfl

theorem cell22_1169034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 6].length) (baseStart_1169034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169034 prefixEnd_1169034 := by exact prefixLift 1169034
  have htrace : WordTrace (prefixWord ++ tailWord_1169034) baseStart_1169034 baseEnd_1169034 := by
    simpa [prefixWord, tailWord_1169034, baseEnd_1169034] using wordTrace_append hprefix tailTrace_1169034
  have hstable : (prefixWord ++ tailWord_1169034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169034).length < 2 ^ (prefixWord ++ tailWord_1169034).sum := by decide
  have hdescent : baseEnd_1169034 < baseStart_1169034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169055 : List Nat := [1, 1, 2, 7, 2, 1, 1, 2, 2, 3]
def baseStart_1169055 : Nat := 118140960795 + 1169055 * 2 ^ 59
def prefixEnd_1169055 : Nat := 4983230072969 + 3 ^ 40 * 1169055 * 2
def baseEnd_1169055 : Nat := 400191417694685867090747

theorem tailTrace_1169055 : CollatzResearch.WordTrace tailWord_1169055 prefixEnd_1169055 400191417694685867090747 := by
  unfold tailWord_1169055
  simp only [CollatzResearch.WordTrace]
  refine ⟨42638938779720868543468619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28425959186480579028979079 42638938779720868543468619)
  ·
    refine ⟨63958408169581302815202929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42638938779720868543468619 63958408169581302815202929)
    ·
      refine ⟨47968806127185977111402197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63958408169581302815202929 47968806127185977111402197)
      ·
        refine ⟨1124268893605921338548489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 47968806127185977111402197 1124268893605921338548489)
        ·
          refine ⟨843201670204441003911367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1124268893605921338548489 843201670204441003911367)
          ·
            refine ⟨1264802505306661505867051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843201670204441003911367 1264802505306661505867051)
            ·
              refine ⟨1897203757959992258800577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264802505306661505867051 1897203757959992258800577)
              ·
                refine ⟨1422902818469994194100433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1897203757959992258800577 1422902818469994194100433)
                ·
                  refine ⟨1067177113852495645575325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1422902818469994194100433 1067177113852495645575325)
                  ·
                    refine ⟨400191417694685867090747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1067177113852495645575325 400191417694685867090747)
                    ·
                      rfl

theorem cell22_1169055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 2, 3].length) (baseStart_1169055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169055 prefixEnd_1169055 := by exact prefixLift 1169055
  have htrace : WordTrace (prefixWord ++ tailWord_1169055) baseStart_1169055 baseEnd_1169055 := by
    simpa [prefixWord, tailWord_1169055, baseEnd_1169055] using wordTrace_append hprefix tailTrace_1169055
  have hstable : (prefixWord ++ tailWord_1169055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169055).length < 2 ^ (prefixWord ++ tailWord_1169055).sum := by decide
  have hdescent : baseEnd_1169055 < baseStart_1169055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169100 : List Nat := [2, 2, 1, 5, 2, 2, 1, 3, 1, 3]
def baseStart_1169100 : Nat := 118140960795 + 1169100 * 2 ^ 59
def prefixEnd_1169100 : Nat := 4983230072969 + 3 ^ 40 * 1169100 * 2
def baseEnd_1169100 : Nat := 400206822114320749715609

theorem tailTrace_1169100 : CollatzResearch.WordTrace tailWord_1169100 prefixEnd_1169100 400206822114320749715609 := by
  unfold tailWord_1169100
  simp only [CollatzResearch.WordTrace]
  refine ⟨21320290032278920614428377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28427053376371894152571169 21320290032278920614428377)
  ·
    refine ⟨15990217524209190460821283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21320290032278920614428377 15990217524209190460821283)
    ·
      refine ⟨23985326286313785691231925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15990217524209190460821283 23985326286313785691231925)
      ·
        refine ⟨2248624339341917408552993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23985326286313785691231925 2248624339341917408552993)
        ·
          refine ⟨1686468254506438056414745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2248624339341917408552993 1686468254506438056414745)
          ·
            refine ⟨1264851190879828542311059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1686468254506438056414745 1264851190879828542311059)
            ·
              refine ⟨1897276786319742813466589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1264851190879828542311059 1897276786319742813466589)
              ·
                refine ⟨711478794869903555049971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1897276786319742813466589 711478794869903555049971)
                ·
                  refine ⟨1067218192304855332574957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711478794869903555049971 1067218192304855332574957)
                  ·
                    refine ⟨400206822114320749715609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1067218192304855332574957 400206822114320749715609)
                    ·
                      rfl

theorem cell22_1169100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 1, 3].length) (baseStart_1169100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169100 prefixEnd_1169100 := by exact prefixLift 1169100
  have htrace : WordTrace (prefixWord ++ tailWord_1169100) baseStart_1169100 baseEnd_1169100 := by
    simpa [prefixWord, tailWord_1169100, baseEnd_1169100] using wordTrace_append hprefix tailTrace_1169100
  have hstable : (prefixWord ++ tailWord_1169100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169100).length < 2 ^ (prefixWord ++ tailWord_1169100).sum := by decide
  have hdescent : baseEnd_1169100 < baseStart_1169100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169117 : List Nat := [1, 4, 3, 3, 1, 1, 3, 2, 1, 3]
def baseStart_1169117 : Nat := 118140960795 + 1169117 * 2 ^ 59
def prefixEnd_1169117 : Nat := 4983230072969 + 3 ^ 40 * 1169117 * 2
def baseEnd_1169117 : Nat := 400212641561738372040557

theorem tailTrace_1169117 : CollatzResearch.WordTrace tailWord_1169117 prefixEnd_1169117 400212641561738372040557 := by
  unfold tailWord_1169117
  simp only [CollatzResearch.WordTrace]
  refine ⟨42641200105496253132225605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28427466736997502088150403 42641200105496253132225605)
  ·
    refine ⟨7995225019780547462292301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42641200105496253132225605 7995225019780547462292301)
    ·
      refine ⟨2998209382417705298359613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7995225019780547462292301 2998209382417705298359613)
      ·
        refine ⟨1124328518406639486884855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2998209382417705298359613 1124328518406639486884855)
        ·
          refine ⟨1686492777609959230327283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124328518406639486884855 1686492777609959230327283)
          ·
            refine ⟨2529739166414938845490925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686492777609959230327283 2529739166414938845490925)
            ·
              refine ⟨948652187405602067059097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2529739166414938845490925 948652187405602067059097)
              ·
                refine ⟨711489140554201550294323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 948652187405602067059097 711489140554201550294323)
                ·
                  refine ⟨1067233710831302325441485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711489140554201550294323 1067233710831302325441485)
                  ·
                    refine ⟨400212641561738372040557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1067233710831302325441485 400212641561738372040557)
                    ·
                      rfl

theorem cell22_1169117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_1169117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169117 prefixEnd_1169117 := by exact prefixLift 1169117
  have htrace : WordTrace (prefixWord ++ tailWord_1169117) baseStart_1169117 baseEnd_1169117 := by
    simpa [prefixWord, tailWord_1169117, baseEnd_1169117] using wordTrace_append hprefix tailTrace_1169117
  have hstable : (prefixWord ++ tailWord_1169117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169117).length < 2 ^ (prefixWord ++ tailWord_1169117).sum := by decide
  have hdescent : baseEnd_1169117 < baseStart_1169117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169201 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 3, 3]
def baseStart_1169201 : Nat := 118140960795 + 1169201 * 2 ^ 59
def prefixEnd_1169201 : Nat := 4983230072969 + 3 ^ 40 * 1169201 * 2
def baseEnd_1169201 : Nat := 400241396478390152940299

theorem tailTrace_1169201 : CollatzResearch.WordTrace tailWord_1169201 prefixEnd_1169201 400241396478390152940299 := by
  unfold tailWord_1169201
  simp only [CollatzResearch.WordTrace]
  refine ⟨42644263837191935478283457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28429509224794623652188971 42644263837191935478283457)
  ·
    refine ⟨31983197877893951608712593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42644263837191935478283457 31983197877893951608712593)
    ·
      refine ⟨23987398408420463706534445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31983197877893951608712593 23987398408420463706534445)
      ·
        refine ⟨8995274403157673889950417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23987398408420463706534445 8995274403157673889950417)
        ·
          refine ⟨6746455802368255417462813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8995274403157673889950417 6746455802368255417462813)
          ·
            refine ⟨2529920925888095781548555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6746455802368255417462813 2529920925888095781548555)
            ·
              refine ⟨3794881388832143672322833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529920925888095781548555 3794881388832143672322833)
              ·
                refine ⟨2846161041624107754242125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3794881388832143672322833 2846161041624107754242125)
                ·
                  refine ⟨1067310390609040407840797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2846161041624107754242125 1067310390609040407840797)
                  ·
                    refine ⟨400241396478390152940299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1067310390609040407840797 400241396478390152940299)
                    ·
                      rfl

theorem cell22_1169201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_1169201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169201 prefixEnd_1169201 := by exact prefixLift 1169201
  have htrace : WordTrace (prefixWord ++ tailWord_1169201) baseStart_1169201 baseEnd_1169201 := by
    simpa [prefixWord, tailWord_1169201, baseEnd_1169201] using wordTrace_append hprefix tailTrace_1169201
  have hstable : (prefixWord ++ tailWord_1169201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169201).length < 2 ^ (prefixWord ++ tailWord_1169201).sum := by decide
  have hdescent : baseEnd_1169201 < baseStart_1169201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169261 : List Nat := [1, 5, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_1169261 : Nat := 118140960795 + 1169261 * 2 ^ 59
def prefixEnd_1169261 : Nat := 4983230072969 + 3 ^ 40 * 1169261 * 2
def baseEnd_1169261 : Nat := 400261935704569996440115

theorem tailTrace_1169261 : CollatzResearch.WordTrace tailWord_1169261 prefixEnd_1169261 400261935704569996440115 := by
  unfold tailWord_1169261
  simp only [CollatzResearch.WordTrace]
  refine ⟨42646452216974565725467637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28430968144649710483645091 42646452216974565725467637)
  ·
    refine ⟨3998104895341365536762591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42646452216974565725467637 3998104895341365536762591)
    ·
      refine ⟨5997157343012048305143887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3998104895341365536762591 5997157343012048305143887)
      ·
        refine ⟨8995736014518072457715831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5997157343012048305143887 8995736014518072457715831)
        ·
          refine ⟨13493604021777108686573747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8995736014518072457715831 13493604021777108686573747)
          ·
            refine ⟨20240406032665663029860621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13493604021777108686573747 20240406032665663029860621)
            ·
              refine ⟨7590152262249623636197733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20240406032665663029860621 7590152262249623636197733)
              ·
                refine ⟨1423153549171804431787075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7590152262249623636197733 1423153549171804431787075)
                ·
                  refine ⟨2134730323757706647680613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1423153549171804431787075 2134730323757706647680613)
                  ·
                    refine ⟨400261935704569996440115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2134730323757706647680613 400261935704569996440115)
                    ·
                      rfl

theorem cell22_1169261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_1169261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169261 prefixEnd_1169261 := by exact prefixLift 1169261
  have htrace : WordTrace (prefixWord ++ tailWord_1169261) baseStart_1169261 baseEnd_1169261 := by
    simpa [prefixWord, tailWord_1169261, baseEnd_1169261] using wordTrace_append hprefix tailTrace_1169261
  have hstable : (prefixWord ++ tailWord_1169261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169261).length < 2 ^ (prefixWord ++ tailWord_1169261).sum := by decide
  have hdescent : baseEnd_1169261 < baseStart_1169261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169274 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 1, 5]
def baseStart_1169274 : Nat := 118140960795 + 1169274 * 2 ^ 59
def prefixEnd_1169274 : Nat := 4983230072969 + 3 ^ 40 * 1169274 * 2
def baseEnd_1169274 : Nat := 400266385870242295865075

theorem tailTrace_1169274 : CollatzResearch.WordTrace tailWord_1169274 prefixEnd_1169274 400266385870242295865075 := by
  unfold tailWord_1169274
  simp only [CollatzResearch.WordTrace]
  refine ⟨10661731591481867236422719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28431284243951645963793917 10661731591481867236422719)
  ·
    refine ⟨15992597387222800854634079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10661731591481867236422719 15992597387222800854634079)
    ·
      refine ⟨23988896080834201281951119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15992597387222800854634079 23988896080834201281951119)
      ·
        refine ⟨35983344121251301922926679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23988896080834201281951119 35983344121251301922926679)
        ·
          refine ⟨53975016181876952884390019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35983344121251301922926679 53975016181876952884390019)
          ·
            refine ⟨80962524272815429326585029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53975016181876952884390019 80962524272815429326585029)
            ·
              refine ⟨15180473301152892998734693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80962524272815429326585029 15180473301152892998734693)
              ·
                refine ⟨2846338743966167437262755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15180473301152892998734693 2846338743966167437262755)
                ·
                  refine ⟨4269508115949251155894133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2846338743966167437262755 4269508115949251155894133)
                  ·
                    refine ⟨400266385870242295865075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4269508115949251155894133 400266385870242295865075)
                    ·
                      rfl

theorem cell22_1169274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_1169274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169274 prefixEnd_1169274 := by exact prefixLift 1169274
  have htrace : WordTrace (prefixWord ++ tailWord_1169274) baseStart_1169274 baseEnd_1169274 := by
    simpa [prefixWord, tailWord_1169274, baseEnd_1169274] using wordTrace_append hprefix tailTrace_1169274
  have hstable : (prefixWord ++ tailWord_1169274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169274).length < 2 ^ (prefixWord ++ tailWord_1169274).sum := by decide
  have hdescent : baseEnd_1169274 < baseStart_1169274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169291 : List Nat := [1, 1, 1, 1, 4, 2, 1, 6, 2, 3]
def baseStart_1169291 : Nat := 118140960795 + 1169291 * 2 ^ 59
def prefixEnd_1169291 : Nat := 4983230072969 + 3 ^ 40 * 1169291 * 2
def baseEnd_1169291 : Nat := 400272205317659918190023

theorem tailTrace_1169291 : CollatzResearch.WordTrace tailWord_1169291 prefixEnd_1169291 400272205317659918190023 := by
  unfold tailWord_1169291
  simp only [CollatzResearch.WordTrace]
  refine ⟨42647546406865880849059727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28431697604577253899373151 42647546406865880849059727)
  ·
    refine ⟨63971319610298821273589591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42647546406865880849059727 63971319610298821273589591)
    ·
      refine ⟨95956979415448231910384387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63971319610298821273589591 95956979415448231910384387)
      ·
        refine ⟨143935469123172347865576581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95956979415448231910384387 143935469123172347865576581)
        ·
          refine ⟨26987900460594815224795609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143935469123172347865576581 26987900460594815224795609)
          ·
            refine ⟨20240925345446111418596707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26987900460594815224795609 20240925345446111418596707)
            ·
              refine ⟨30361388018169167127895061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20240925345446111418596707 30361388018169167127895061)
              ·
                refine ⟨1423190063351679709120081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30361388018169167127895061 1423190063351679709120081)
                ·
                  refine ⟨1067392547513759781840061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1423190063351679709120081 1067392547513759781840061)
                  ·
                    refine ⟨400272205317659918190023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1067392547513759781840061 400272205317659918190023)
                    ·
                      rfl

theorem cell22_1169291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 3].length) (baseStart_1169291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169291 prefixEnd_1169291 := by exact prefixLift 1169291
  have htrace : WordTrace (prefixWord ++ tailWord_1169291) baseStart_1169291 baseEnd_1169291 := by
    simpa [prefixWord, tailWord_1169291, baseEnd_1169291] using wordTrace_append hprefix tailTrace_1169291
  have hstable : (prefixWord ++ tailWord_1169291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169291).length < 2 ^ (prefixWord ++ tailWord_1169291).sum := by decide
  have hdescent : baseEnd_1169291 < baseStart_1169291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169353 : List Nat := [1, 2, 1, 1, 2, 1, 2, 8, 1, 3]
def baseStart_1169353 : Nat := 118140960795 + 1169353 * 2 ^ 59
def prefixEnd_1169353 : Nat := 4983230072969 + 3 ^ 40 * 1169353 * 2
def baseEnd_1169353 : Nat := 400293429184712423139833

theorem tailTrace_1169353 : CollatzResearch.WordTrace tailWord_1169353 prefixEnd_1169353 400293429184712423139833 := by
  unfold tailWord_1169353
  simp only [CollatzResearch.WordTrace]
  refine ⟨42649807732641265437816713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28433205155094176958544475 42649807732641265437816713)
  ·
    refine ⟨31987355799480949078362535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42649807732641265437816713 31987355799480949078362535)
    ·
      refine ⟨47981033699221423617543803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31987355799480949078362535 47981033699221423617543803)
      ·
        refine ⟨71971550548832135426315705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47981033699221423617543803 71971550548832135426315705)
        ·
          refine ⟨53978662911624101569736779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71971550548832135426315705 53978662911624101569736779)
          ·
            refine ⟨80967994367436152354605169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53978662911624101569736779 80967994367436152354605169)
            ·
              refine ⟨60725995775577114265953877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80967994367436152354605169 60725995775577114265953877)
              ·
                refine ⟨711632762995044307804147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 60725995775577114265953877 711632762995044307804147)
                ·
                  refine ⟨1067449144492566461706221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711632762995044307804147 1067449144492566461706221)
                  ·
                    refine ⟨400293429184712423139833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1067449144492566461706221 400293429184712423139833)
                    ·
                      rfl

theorem cell22_1169353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 1, 3].length) (baseStart_1169353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169353 prefixEnd_1169353 := by exact prefixLift 1169353
  have htrace : WordTrace (prefixWord ++ tailWord_1169353) baseStart_1169353 baseEnd_1169353 := by
    simpa [prefixWord, tailWord_1169353, baseEnd_1169353] using wordTrace_append hprefix tailTrace_1169353
  have hstable : (prefixWord ++ tailWord_1169353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169353).length < 2 ^ (prefixWord ++ tailWord_1169353).sum := by decide
  have hdescent : baseEnd_1169353 < baseStart_1169353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169372 : List Nat := [2, 2, 6, 1, 1, 1, 3, 6]
def baseStart_1169372 : Nat := 118140960795 + 1169372 * 2 ^ 59
def prefixEnd_1169372 : Nat := 4983230072969 + 3 ^ 40 * 1169372 * 2
def baseEnd_1169372 : Nat := 44477770363666967434975

theorem tailTrace_1169372 : CollatzResearch.WordTrace tailWord_1169372 prefixEnd_1169372 44477770363666967434975 := by
  unfold tailWord_1169372
  simp only [CollatzResearch.WordTrace]
  refine ⟨21325250359786215841379185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28433667146381621121838913 21325250359786215841379185)
  ·
    refine ⟨15993937769839661881034389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21325250359786215841379185 15993937769839661881034389)
    ·
      refine ⟨749715832961234150673487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15993937769839661881034389 749715832961234150673487)
      ·
        refine ⟨1124573749441851226010231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749715832961234150673487 1124573749441851226010231)
        ·
          refine ⟨1686860624162776839015347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124573749441851226010231 1686860624162776839015347)
          ·
            refine ⟨2530290936244165258523021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686860624162776839015347 2530290936244165258523021)
            ·
              refine ⟨948859101091561971946133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2530290936244165258523021 948859101091561971946133)
              ·
                refine ⟨44477770363666967434975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 948859101091561971946133 44477770363666967434975)
                ·
                  rfl

theorem cell22_1169372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 6].length) (baseStart_1169372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169372 prefixEnd_1169372 := by exact prefixLift 1169372
  have htrace : WordTrace (prefixWord ++ tailWord_1169372) baseStart_1169372 baseEnd_1169372 := by
    simpa [prefixWord, tailWord_1169372, baseEnd_1169372] using wordTrace_append hprefix tailTrace_1169372
  have hstable : (prefixWord ++ tailWord_1169372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169372).length < 2 ^ (prefixWord ++ tailWord_1169372).sum := by decide
  have hdescent : baseEnd_1169372 < baseStart_1169372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169445 : List Nat := [1, 3, 1, 2, 2, 5, 1, 3, 4]
def baseStart_1169445 : Nat := 118140960795 + 1169445 * 2 ^ 59
def prefixEnd_1169445 : Nat := 4983230072969 + 3 ^ 40 * 1169445 * 2
def baseEnd_1169445 : Nat := 133441640888284949946517

theorem tailTrace_1169445 : CollatzResearch.WordTrace tailWord_1169445 prefixEnd_1169445 133441640888284949946517 := by
  unfold tailWord_1169445
  simp only [CollatzResearch.WordTrace]
  refine ⟨42653163248307965150165789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28435442165538643433443859 42653163248307965150165789)
  ·
    refine ⟨15994936218115486931312171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42653163248307965150165789 15994936218115486931312171)
    ·
      refine ⟨23992404327173230396968257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15994936218115486931312171 23992404327173230396968257)
      ·
        refine ⟨17994303245379922797726193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23992404327173230396968257 17994303245379922797726193)
        ·
          refine ⟨13495727434034942098294645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17994303245379922797726193 13495727434034942098294645)
          ·
            refine ⟨1265224446940775821715123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13495727434034942098294645 1265224446940775821715123)
            ·
              refine ⟨1897836670411163732572685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265224446940775821715123 1897836670411163732572685)
              ·
                refine ⟨711688751404186399714757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1897836670411163732572685 711688751404186399714757)
                ·
                  refine ⟨133441640888284949946517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 711688751404186399714757 133441640888284949946517)
                  ·
                    rfl

theorem cell22_1169445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_1169445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169445 prefixEnd_1169445 := by exact prefixLift 1169445
  have htrace : WordTrace (prefixWord ++ tailWord_1169445) baseStart_1169445 baseEnd_1169445 := by
    simpa [prefixWord, tailWord_1169445, baseEnd_1169445] using wordTrace_append hprefix tailTrace_1169445
  have hstable : (prefixWord ++ tailWord_1169445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169445).length < 2 ^ (prefixWord ++ tailWord_1169445).sum := by decide
  have hdescent : baseEnd_1169445 < baseStart_1169445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169456 : List Nat := [2, 1, 1, 1, 2, 7, 8]
def baseStart_1169456 : Nat := 118140960795 + 1169456 * 2 ^ 59
def prefixEnd_1169456 : Nat := 4983230072969 + 3 ^ 40 * 1169456 * 2
def baseEnd_1169456 : Nat := 14826988451468684733871

theorem tailTrace_1169456 : CollatzResearch.WordTrace tailWord_1169456 prefixEnd_1169456 14826988451468684733871 := by
  unfold tailWord_1169456
  simp only [CollatzResearch.WordTrace]
  refine ⟨21326782225634057014408111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28435709634178742685877481 21326782225634057014408111)
  ·
    refine ⟨31990173338451085521612167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21326782225634057014408111 31990173338451085521612167)
    ·
      refine ⟨47985260007676628282418251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31990173338451085521612167 47985260007676628282418251)
      ·
        refine ⟨71977890011514942423627377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47985260007676628282418251 71977890011514942423627377)
        ·
          refine ⟨53983417508636206817720533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71977890011514942423627377 53983417508636206817720533)
          ·
            refine ⟨1265236347858661097290325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 53983417508636206817720533 1265236347858661097290325)
            ·
              refine ⟨14826988451468684733871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1265236347858661097290325 14826988451468684733871)
              ·
                rfl

theorem cell22_1169456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 8].length) (baseStart_1169456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169456 prefixEnd_1169456 := by exact prefixLift 1169456
  have htrace : WordTrace (prefixWord ++ tailWord_1169456) baseStart_1169456 baseEnd_1169456 := by
    simpa [prefixWord, tailWord_1169456, baseEnd_1169456] using wordTrace_append hprefix tailTrace_1169456
  have hstable : (prefixWord ++ tailWord_1169456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169456).length < 2 ^ (prefixWord ++ tailWord_1169456).sum := by decide
  have hdescent : baseEnd_1169456 < baseStart_1169456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169458 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_1169458 : Nat := 118140960795 + 1169458 * 2 ^ 59
def prefixEnd_1169458 : Nat := 4983230072969 + 3 ^ 40 * 1169458 * 2
def baseEnd_1169458 : Nat := 400329372830527149264511

theorem tailTrace_1169458 : CollatzResearch.WordTrace tailWord_1169458 prefixEnd_1169458 400329372830527149264511 := by
  unfold tailWord_1169458
  simp only [CollatzResearch.WordTrace]
  refine ⟨10663409349315217092597257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28435758264840578913592685 10663409349315217092597257)
  ·
    refine ⟨7997557011986412819447943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10663409349315217092597257 7997557011986412819447943)
    ·
      refine ⟨11996335517979619229171915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7997557011986412819447943 11996335517979619229171915)
      ·
        refine ⟨17994503276969428843757873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11996335517979619229171915 17994503276969428843757873)
        ·
          refine ⟨13495877457727071632818405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17994503276969428843757873 13495877457727071632818405)
          ·
            refine ⟨2530477023323825931153451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13495877457727071632818405 2530477023323825931153451)
            ·
              refine ⟨3795715534985738896730177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2530477023323825931153451 3795715534985738896730177)
              ·
                refine ⟨2846786651239304172547633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3795715534985738896730177 2846786651239304172547633)
                ·
                  refine ⟨2135089988429478129410725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2846786651239304172547633 2135089988429478129410725)
                  ·
                    refine ⟨400329372830527149264511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2135089988429478129410725 400329372830527149264511)
                    ·
                      rfl

theorem cell22_1169458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_1169458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169458 prefixEnd_1169458 := by exact prefixLift 1169458
  have htrace : WordTrace (prefixWord ++ tailWord_1169458) baseStart_1169458 baseEnd_1169458 := by
    simpa [prefixWord, tailWord_1169458, baseEnd_1169458] using wordTrace_append hprefix tailTrace_1169458
  have hstable : (prefixWord ++ tailWord_1169458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169458).length < 2 ^ (prefixWord ++ tailWord_1169458).sum := by decide
  have hdescent : baseEnd_1169458 < baseStart_1169458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169462 : List Nat := [5, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_1169462 : Nat := 118140960795 + 1169462 * 2 ^ 59
def prefixEnd_1169462 : Nat := 4983230072969 + 3 ^ 40 * 1169462 * 2
def baseEnd_1169462 : Nat := 133443580704090824054833

theorem tailTrace_1169462 : CollatzResearch.WordTrace tailWord_1169462 prefixEnd_1169462 133443580704090824054833 := by
  unfold tailWord_1169462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2665861455577898565845915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28435855526164251369023093 2665861455577898565845915)
  ·
    refine ⟨3998792183366847848768873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2665861455577898565845915 3998792183366847848768873)
    ·
      refine ⟨2999094137525135886576655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3998792183366847848768873 2999094137525135886576655)
      ·
        refine ⟨4498641206287703829864983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2999094137525135886576655 4498641206287703829864983)
        ·
          refine ⟨6747961809431555744797475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4498641206287703829864983 6747961809431555744797475)
          ·
            refine ⟨10121942714147333617196213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6747961809431555744797475 10121942714147333617196213)
            ·
              refine ⟨948932129451312526612145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10121942714147333617196213 948932129451312526612145)
              ·
                refine ⟨711699097088484394959109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 948932129451312526612145 711699097088484394959109)
                ·
                  refine ⟨133443580704090824054833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 711699097088484394959109 133443580704090824054833)
                  ·
                    rfl

theorem cell22_1169462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_1169462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169462 prefixEnd_1169462 := by exact prefixLift 1169462
  have htrace : WordTrace (prefixWord ++ tailWord_1169462) baseStart_1169462 baseEnd_1169462 := by
    simpa [prefixWord, tailWord_1169462, baseEnd_1169462] using wordTrace_append hprefix tailTrace_1169462
  have hstable : (prefixWord ++ tailWord_1169462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169462).length < 2 ^ (prefixWord ++ tailWord_1169462).sum := by decide
  have hdescent : baseEnd_1169462 < baseStart_1169462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169473 : List Nat := [1, 2, 5, 1, 2, 2, 2, 7]
def baseStart_1169473 : Nat := 118140960795 + 1169473 * 2 ^ 59
def prefixEnd_1169473 : Nat := 4983230072969 + 3 ^ 40 * 1169473 * 2
def baseEnd_1169473 : Nat := 44481611959674678904385

theorem tailTrace_1169473 : CollatzResearch.WordTrace tailWord_1169473 prefixEnd_1169473 44481611959674678904385 := by
  unfold tailWord_1169473
  simp only [CollatzResearch.WordTrace]
  refine ⟨42654184492206525932185073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28436122994804350621456715 42654184492206525932185073)
  ·
    refine ⟨31990638369154894449138805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42654184492206525932185073 31990638369154894449138805)
    ·
      refine ⟨2999122347108271354606763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31990638369154894449138805 2999122347108271354606763)
      ·
        refine ⟨4498683520662407031910145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2999122347108271354606763 4498683520662407031910145)
        ·
          refine ⟨3374012640496805273932609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4498683520662407031910145 3374012640496805273932609)
          ·
            refine ⟨2530509480372603955449457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3374012640496805273932609 2530509480372603955449457)
            ·
              refine ⟨1897882110279452966587093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2530509480372603955449457 1897882110279452966587093)
              ·
                refine ⟨44481611959674678904385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1897882110279452966587093 44481611959674678904385)
                ·
                  rfl

theorem cell22_1169473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 7].length) (baseStart_1169473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169473 prefixEnd_1169473 := by exact prefixLift 1169473
  have htrace : WordTrace (prefixWord ++ tailWord_1169473) baseStart_1169473 baseEnd_1169473 := by
    simpa [prefixWord, tailWord_1169473, baseEnd_1169473] using wordTrace_append hprefix tailTrace_1169473
  have hstable : (prefixWord ++ tailWord_1169473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169473).length < 2 ^ (prefixWord ++ tailWord_1169473).sum := by decide
  have hdescent : baseEnd_1169473 < baseStart_1169473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169505 : List Nat := [1, 2, 3, 1, 1, 2, 1, 7, 1, 3]
def baseStart_1169505 : Nat := 118140960795 + 1169505 * 2 ^ 59
def prefixEnd_1169505 : Nat := 4983230072969 + 3 ^ 40 * 1169505 * 2
def baseEnd_1169505 : Nat := 400345461891034693339367

theorem tailTrace_1169505 : CollatzResearch.WordTrace tailWord_1169505 prefixEnd_1169505 400345461891034693339367 := by
  unfold tailWord_1169505
  simp only [CollatzResearch.WordTrace]
  refine ⟨42655351628090595397349969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28436901085393730264899979 42655351628090595397349969)
  ·
    refine ⟨31991513721067946548012477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42655351628090595397349969 31991513721067946548012477)
    ·
      refine ⟨11996817645400479955504679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31991513721067946548012477 11996817645400479955504679)
      ·
        refine ⟨17995226468100719933257019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11996817645400479955504679 17995226468100719933257019)
        ·
          refine ⟨26992839702151079899885529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17995226468100719933257019 26992839702151079899885529)
          ·
            refine ⟨20244629776613309924914147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26992839702151079899885529 20244629776613309924914147)
            ·
              refine ⟨30366944664919964887371221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20244629776613309924914147 30366944664919964887371221)
              ·
                refine ⟨711725265584061677047763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30366944664919964887371221 711725265584061677047763)
                ·
                  refine ⟨1067587898376092515571645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711725265584061677047763 1067587898376092515571645)
                  ·
                    refine ⟨400345461891034693339367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1067587898376092515571645 400345461891034693339367)
                    ·
                      rfl

theorem cell22_1169505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_1169505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169505 prefixEnd_1169505 := by exact prefixLift 1169505
  have htrace : WordTrace (prefixWord ++ tailWord_1169505) baseStart_1169505 baseEnd_1169505 := by
    simpa [prefixWord, tailWord_1169505, baseEnd_1169505] using wordTrace_append hprefix tailTrace_1169505
  have hstable : (prefixWord ++ tailWord_1169505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169505).length < 2 ^ (prefixWord ++ tailWord_1169505).sum := by decide
  have hdescent : baseEnd_1169505 < baseStart_1169505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169522 : List Nat := [3, 2, 1, 2, 2, 3, 1, 4, 1, 3]
def baseStart_1169522 : Nat := 118140960795 + 1169522 * 2 ^ 59
def prefixEnd_1169522 : Nat := 4983230072969 + 3 ^ 40 * 1169522 * 2
def baseEnd_1169522 : Nat := 400351281338452315664315

theorem tailTrace_1169522 : CollatzResearch.WordTrace tailWord_1169522 prefixEnd_1169522 400351281338452315664315 := by
  unfold tailWord_1169522
  simp only [CollatzResearch.WordTrace]
  refine ⟨10663992917257251825179705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28437314446019338200479213 10663992917257251825179705)
  ·
    refine ⟨7997994687942938868884779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10663992917257251825179705 7997994687942938868884779)
    ·
      refine ⟨11996992031914408303327169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7997994687942938868884779 11996992031914408303327169)
      ·
        refine ⟨8997744023935806227495377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11996992031914408303327169 8997744023935806227495377)
        ·
          refine ⟨6748308017951854670621533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8997744023935806227495377 6748308017951854670621533)
          ·
            refine ⟨2530615506731945501483075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6748308017951854670621533 2530615506731945501483075)
            ·
              refine ⟨3795923260097918252224613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2530615506731945501483075 3795923260097918252224613)
              ·
                refine ⟨711735611268359672292115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3795923260097918252224613 711735611268359672292115)
                ·
                  refine ⟨1067603416902539508438173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711735611268359672292115 1067603416902539508438173)
                  ·
                    refine ⟨400351281338452315664315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1067603416902539508438173 400351281338452315664315)
                    ·
                      rfl

theorem cell22_1169522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_1169522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169522 prefixEnd_1169522 := by exact prefixLift 1169522
  have htrace : WordTrace (prefixWord ++ tailWord_1169522) baseStart_1169522 baseEnd_1169522 := by
    simpa [prefixWord, tailWord_1169522, baseEnd_1169522] using wordTrace_append hprefix tailTrace_1169522
  have hstable : (prefixWord ++ tailWord_1169522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169522).length < 2 ^ (prefixWord ++ tailWord_1169522).sum := by decide
  have hdescent : baseEnd_1169522 < baseStart_1169522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169533 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_1169533 : Nat := 118140960795 + 1169533 * 2 ^ 59
def prefixEnd_1169533 : Nat := 4983230072969 + 3 ^ 40 * 1169533 * 2
def baseEnd_1169533 : Nat := 400355046863251953639281

theorem tailTrace_1169533 : CollatzResearch.WordTrace tailWord_1169533 prefixEnd_1169533 400355046863251953639281 := by
  unfold tailWord_1169533
  simp only [CollatzResearch.WordTrace]
  refine ⟨42656372871989156179369253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28437581914659437452912835 42656372871989156179369253)
  ·
    refine ⟨7998069913497966783631735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42656372871989156179369253 7998069913497966783631735)
    ·
      refine ⟨11997104870246950175447603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7998069913497966783631735 11997104870246950175447603)
      ·
        refine ⟨17995657305370425263171405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11997104870246950175447603 17995657305370425263171405)
        ·
          refine ⟨6748371489513909473689277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17995657305370425263171405 6748371489513909473689277)
          ·
            refine ⟨2530639308567716052633479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6748371489513909473689277 2530639308567716052633479)
            ·
              refine ⟨3795958962851574078950219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2530639308567716052633479 3795958962851574078950219)
              ·
                refine ⟨5693938444277361118425329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3795958962851574078950219 5693938444277361118425329)
                ·
                  refine ⟨4270453833208020838818997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5693938444277361118425329 4270453833208020838818997)
                  ·
                    refine ⟨400355046863251953639281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4270453833208020838818997 400355046863251953639281)
                    ·
                      rfl

theorem cell22_1169533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_1169533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169533 prefixEnd_1169533 := by exact prefixLift 1169533
  have htrace : WordTrace (prefixWord ++ tailWord_1169533) baseStart_1169533 baseEnd_1169533 := by
    simpa [prefixWord, tailWord_1169533, baseEnd_1169533] using wordTrace_append hprefix tailTrace_1169533
  have hstable : (prefixWord ++ tailWord_1169533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169533).length < 2 ^ (prefixWord ++ tailWord_1169533).sum := by decide
  have hdescent : baseEnd_1169533 < baseStart_1169533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169556 : List Nat := [2, 4, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_1169556 : Nat := 118140960795 + 1169556 * 2 ^ 59
def prefixEnd_1169556 : Nat := 4983230072969 + 3 ^ 40 * 1169556 * 2
def baseEnd_1169556 : Nat := 400362920233287560314211

theorem tailTrace_1169556 : CollatzResearch.WordTrace tailWord_1169556 prefixEnd_1169556 400362920233287560314211 := by
  unfold tailWord_1169556
  simp only [CollatzResearch.WordTrace]
  refine ⟨21328605875452915553728261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28438141167270554071637681 21328605875452915553728261)
  ·
    refine ⟨3999113601647421666324049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21328605875452915553728261 3999113601647421666324049)
    ·
      refine ⟨2999335201235566249743037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3999113601647421666324049 2999335201235566249743037)
      ·
        refine ⟨1124750700463337343653639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2999335201235566249743037 1124750700463337343653639)
        ·
          refine ⟨1687126050695006015480459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124750700463337343653639 1687126050695006015480459)
          ·
            refine ⟨2530689076042509023220689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1687126050695006015480459 2530689076042509023220689)
            ·
              refine ⟨1898016807031881767415517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2530689076042509023220689 1898016807031881767415517)
              ·
                refine ⟨711756302636955662780819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1898016807031881767415517 711756302636955662780819)
                ·
                  refine ⟨1067634453955433494171229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711756302636955662780819 1067634453955433494171229)
                  ·
                    refine ⟨400362920233287560314211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1067634453955433494171229 400362920233287560314211)
                    ·
                      rfl

theorem cell22_1169556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_1169556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169556 prefixEnd_1169556 := by exact prefixLift 1169556
  have htrace : WordTrace (prefixWord ++ tailWord_1169556) baseStart_1169556 baseEnd_1169556 := by
    simpa [prefixWord, tailWord_1169556, baseEnd_1169556] using wordTrace_append hprefix tailTrace_1169556
  have hstable : (prefixWord ++ tailWord_1169556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169556).length < 2 ^ (prefixWord ++ tailWord_1169556).sum := by decide
  have hdescent : baseEnd_1169556 < baseStart_1169556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169565 : List Nat := [1, 4, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1169565 : Nat := 118140960795 + 1169565 * 2 ^ 59
def prefixEnd_1169565 : Nat := 4983230072969 + 3 ^ 40 * 1169565 * 2
def baseEnd_1169565 : Nat := 400366001117214536839183

theorem tailTrace_1169565 : CollatzResearch.WordTrace tailWord_1169565 prefixEnd_1169565 400366001117214536839183 := by
  unfold tailWord_1169565
  simp only [CollatzResearch.WordTrace]
  refine ⟨42657540007873225644534149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28438360005248817096356099 42657540007873225644534149)
  ·
    refine ⟨7998288751476229808350153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42657540007873225644534149 7998288751476229808350153)
    ·
      refine ⟨5998716563607172356262615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7998288751476229808350153 5998716563607172356262615)
      ·
        refine ⟨8998074845410758534393923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5998716563607172356262615 8998074845410758534393923)
        ·
          refine ⟨13497112268116137801590885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8998074845410758534393923 13497112268116137801590885)
          ·
            refine ⟨2530708550271775837798291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13497112268116137801590885 2530708550271775837798291)
            ·
              refine ⟨3796062825407663756697437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2530708550271775837798291 3796062825407663756697437)
              ·
                refine ⟨1423523559527873908761539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3796062825407663756697437 1423523559527873908761539)
                ·
                  refine ⟨2135285339291810863142309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1423523559527873908761539 2135285339291810863142309)
                  ·
                    refine ⟨400366001117214536839183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2135285339291810863142309 400366001117214536839183)
                    ·
                      rfl

theorem cell22_1169565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1169565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169565 prefixEnd_1169565 := by exact prefixLift 1169565
  have htrace : WordTrace (prefixWord ++ tailWord_1169565) baseStart_1169565 baseEnd_1169565 := by
    simpa [prefixWord, tailWord_1169565, baseEnd_1169565] using wordTrace_append hprefix tailTrace_1169565
  have hstable : (prefixWord ++ tailWord_1169565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169565).length < 2 ^ (prefixWord ++ tailWord_1169565).sum := by decide
  have hdescent : baseEnd_1169565 < baseStart_1169565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169700 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_1169700 : Nat := 118140960795 + 1169700 * 2 ^ 59
def prefixEnd_1169700 : Nat := 4983230072969 + 3 ^ 40 * 1169700 * 2
def baseEnd_1169700 : Nat := 400412214376119184713769

theorem tailTrace_1169700 : CollatzResearch.WordTrace tailWord_1169700 prefixEnd_1169700 400412214376119184713769 := by
  unfold tailWord_1169700
  simp only [CollatzResearch.WordTrace]
  refine ⟨21331231931192071850349277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28441642574922762467132369 21331231931192071850349277)
  ·
    refine ⟨7999211974197026943880979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21331231931192071850349277 7999211974197026943880979)
    ·
      refine ⟨11998817961295540415821469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7999211974197026943880979 11998817961295540415821469)
      ·
        refine ⟨4499556735485827655933051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11998817961295540415821469 4499556735485827655933051)
        ·
          refine ⟨6749335103228741483899577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4499556735485827655933051 6749335103228741483899577)
          ·
            refine ⟨5062001327421556112924683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6749335103228741483899577 5062001327421556112924683)
            ·
              refine ⟨7593001991132334169387025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5062001327421556112924683 7593001991132334169387025)
              ·
                refine ⟨5694751493349250627040269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7593001991132334169387025 5694751493349250627040269)
                ·
                  refine ⟨2135531810005968985140101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5694751493349250627040269 2135531810005968985140101)
                  ·
                    refine ⟨400412214376119184713769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2135531810005968985140101 400412214376119184713769)
                    ·
                      rfl

theorem cell22_1169700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_1169700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169700 prefixEnd_1169700 := by exact prefixLift 1169700
  have htrace : WordTrace (prefixWord ++ tailWord_1169700) baseStart_1169700 baseEnd_1169700 := by
    simpa [prefixWord, tailWord_1169700, baseEnd_1169700] using wordTrace_append hprefix tailTrace_1169700
  have hstable : (prefixWord ++ tailWord_1169700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169700).length < 2 ^ (prefixWord ++ tailWord_1169700).sum := by decide
  have hdescent : baseEnd_1169700 < baseStart_1169700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169764 : List Nat := [2, 3, 1, 1, 3, 1, 5, 1, 2, 3]
def baseStart_1169764 : Nat := 118140960795 + 1169764 * 2 ^ 59
def prefixEnd_1169764 : Nat := 4983230072969 + 3 ^ 40 * 1169764 * 2
def baseEnd_1169764 : Nat := 400434122884044351113573

theorem tailTrace_1169764 : CollatzResearch.WordTrace tailWord_1169764 prefixEnd_1169764 400434122884044351113573 := by
  unfold tailWord_1169764
  simp only [CollatzResearch.WordTrace]
  refine ⟨21332399067076141315514173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28443198756101521754018897 21332399067076141315514173)
  ·
    refine ⟨7999649650153552993317815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21332399067076141315514173 7999649650153552993317815)
    ·
      refine ⟨11999474475230329489976723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7999649650153552993317815 11999474475230329489976723)
      ·
        refine ⟨17999211712845494234965085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11999474475230329489976723 17999211712845494234965085)
        ·
          refine ⟨6749704392317060338111907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17999211712845494234965085 6749704392317060338111907)
          ·
            refine ⟨10124556588475590507167861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6749704392317060338111907 10124556588475590507167861)
            ·
              refine ⟨949177180169586610046987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10124556588475590507167861 949177180169586610046987)
              ·
                refine ⟨1423765770254379915070481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 949177180169586610046987 1423765770254379915070481)
                ·
                  refine ⟨1067824327690784936302861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1423765770254379915070481 1067824327690784936302861)
                  ·
                    refine ⟨400434122884044351113573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1067824327690784936302861 400434122884044351113573)
                    ·
                      rfl

theorem cell22_1169764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_1169764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169764 prefixEnd_1169764 := by exact prefixLift 1169764
  have htrace : WordTrace (prefixWord ++ tailWord_1169764) baseStart_1169764 baseEnd_1169764 := by
    simpa [prefixWord, tailWord_1169764, baseEnd_1169764] using wordTrace_append hprefix tailTrace_1169764
  have hstable : (prefixWord ++ tailWord_1169764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169764).length < 2 ^ (prefixWord ++ tailWord_1169764).sum := by decide
  have hdescent : baseEnd_1169764 < baseStart_1169764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169775 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 5, 3]
def baseStart_1169775 : Nat := 118140960795 + 1169775 * 2 ^ 59
def prefixEnd_1169775 : Nat := 4983230072969 + 3 ^ 40 * 1169775 * 2
def baseEnd_1169775 : Nat := 400437888408843989088539

theorem tailTrace_1169775 : CollatzResearch.WordTrace tailWord_1169775 prefixEnd_1169775 400437888408843989088539 := by
  unfold tailWord_1169775
  simp only [CollatzResearch.WordTrace]
  refine ⟨42665199337112431509678779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28443466224741621006452519 42665199337112431509678779)
  ·
    refine ⟨63997799005668647264518169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42665199337112431509678779 63997799005668647264518169)
    ·
      refine ⟨47998349254251485448388627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63997799005668647264518169 47998349254251485448388627)
      ·
        refine ⟨71997523881377228172582941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47998349254251485448388627 71997523881377228172582941)
        ·
          refine ⟨26999071455516460564718603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71997523881377228172582941 26999071455516460564718603)
          ·
            refine ⟨40498607183274690847077905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26999071455516460564718603 40498607183274690847077905)
            ·
              refine ⟨30373955387456018135308429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40498607183274690847077905 30373955387456018135308429)
              ·
                refine ⟨11390233270296006800740661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30373955387456018135308429 11390233270296006800740661)
                ·
                  refine ⟨1067834369090250637569437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11390233270296006800740661 1067834369090250637569437)
                  ·
                    refine ⟨400437888408843989088539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1067834369090250637569437 400437888408843989088539)
                    ·
                      rfl

theorem cell22_1169775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 3].length) (baseStart_1169775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169775 prefixEnd_1169775 := by exact prefixLift 1169775
  have htrace : WordTrace (prefixWord ++ tailWord_1169775) baseStart_1169775 baseEnd_1169775 := by
    simpa [prefixWord, tailWord_1169775, baseEnd_1169775] using wordTrace_append hprefix tailTrace_1169775
  have hstable : (prefixWord ++ tailWord_1169775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169775).length < 2 ^ (prefixWord ++ tailWord_1169775).sum := by decide
  have hdescent : baseEnd_1169775 < baseStart_1169775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169794 : List Nat := [3, 4, 2, 1, 2, 2, 8]
def baseStart_1169794 : Nat := 118140960795 + 1169794 * 2 ^ 59
def prefixEnd_1169794 : Nat := 4983230072969 + 3 ^ 40 * 1169794 * 2
def baseEnd_1169794 : Nat := 14831273796190158254203

theorem tailTrace_1169794 : CollatzResearch.WordTrace tailWord_1169794 prefixEnd_1169794 14831273796190158254203 := by
  unfold tailWord_1169794
  simp only [CollatzResearch.WordTrace]
  refine ⟨10666473081010899438655109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28443928216029065169746957 10666473081010899438655109)
  ·
    refine ⟨1999963702689543644747833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10666473081010899438655109 1999963702689543644747833)
    ·
      refine ⟨1499972777017157733560875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1999963702689543644747833 1499972777017157733560875)
      ·
        refine ⟨2249959165525736600341313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1499972777017157733560875 2249959165525736600341313)
        ·
          refine ⟨1687469374144302450255985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2249959165525736600341313 1687469374144302450255985)
          ·
            refine ⟨1265602030608226837691989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1687469374144302450255985 1265602030608226837691989)
            ·
              refine ⟨14831273796190158254203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1265602030608226837691989 14831273796190158254203)
              ·
                rfl

theorem cell22_1169794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 8].length) (baseStart_1169794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169794 prefixEnd_1169794 := by exact prefixLift 1169794
  have htrace : WordTrace (prefixWord ++ tailWord_1169794) baseStart_1169794 baseEnd_1169794 := by
    simpa [prefixWord, tailWord_1169794, baseEnd_1169794] using wordTrace_append hprefix tailTrace_1169794
  have hstable : (prefixWord ++ tailWord_1169794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169794).length < 2 ^ (prefixWord ++ tailWord_1169794).sum := by decide
  have hdescent : baseEnd_1169794 < baseStart_1169794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169860 : List Nat := [2, 3, 3, 2, 2, 2, 2, 2, 1, 3]
def baseStart_1169860 : Nat := 118140960795 + 1169860 * 2 ^ 59
def prefixEnd_1169860 : Nat := 4983230072969 + 3 ^ 40 * 1169860 * 2
def baseEnd_1169860 : Nat := 400466985645932100713279

theorem tailTrace_1169860 : CollatzResearch.WordTrace tailWord_1169860 prefixEnd_1169860 400466985645932100713279 := by
  unfold tailWord_1169860
  simp only [CollatzResearch.WordTrace]
  refine ⟨21334149770902245513261517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28445533027869660684348689 21334149770902245513261517)
  ·
    refine ⟨8000306164088342067473069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21334149770902245513261517 8000306164088342067473069)
    ·
      refine ⟨3000114811533128275302401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8000306164088342067473069 3000114811533128275302401)
      ·
        refine ⟨2250086108649846206476801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3000114811533128275302401 2250086108649846206476801)
        ·
          refine ⟨1687564581487384654857601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2250086108649846206476801 1687564581487384654857601)
          ·
            refine ⟨1265673436115538491143201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1687564581487384654857601 1265673436115538491143201)
            ·
              refine ⟨949255077086653868357401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1265673436115538491143201 949255077086653868357401)
              ·
                refine ⟨711941307814990401268051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 949255077086653868357401 711941307814990401268051)
                ·
                  refine ⟨1067911961722485601902077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 711941307814990401268051 1067911961722485601902077)
                  ·
                    refine ⟨400466985645932100713279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1067911961722485601902077 400466985645932100713279)
                    ·
                      rfl

theorem cell22_1169860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_1169860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169860 prefixEnd_1169860 := by exact prefixLift 1169860
  have htrace : WordTrace (prefixWord ++ tailWord_1169860) baseStart_1169860 baseEnd_1169860 := by
    simpa [prefixWord, tailWord_1169860, baseEnd_1169860] using wordTrace_append hprefix tailTrace_1169860
  have hstable : (prefixWord ++ tailWord_1169860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169860).length < 2 ^ (prefixWord ++ tailWord_1169860).sum := by decide
  have hdescent : baseEnd_1169860 < baseStart_1169860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169880 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 1, 6]
def baseStart_1169880 : Nat := 118140960795 + 1169880 * 2 ^ 59
def prefixEnd_1169880 : Nat := 4983230072969 + 3 ^ 40 * 1169880 * 2
def baseEnd_1169880 : Nat := 400473832054658715213217

theorem tailTrace_1169880 : CollatzResearch.WordTrace tailWord_1169880 prefixEnd_1169880 400473832054658715213217 := by
  unfold tailWord_1169880
  simp only [CollatzResearch.WordTrace]
  refine ⟨21334514500866017221125547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28446019334488022961500729 21334514500866017221125547)
  ·
    refine ⟨32001771751299025831688321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21334514500866017221125547 32001771751299025831688321)
    ·
      refine ⟨24001328813474269373766241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32001771751299025831688321 24001328813474269373766241)
      ·
        refine ⟨18000996610105702030324681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24001328813474269373766241 18000996610105702030324681)
        ·
          refine ⟨13500747457579276522743511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18000996610105702030324681 13500747457579276522743511)
          ·
            refine ⟨20251121186368914784115267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13500747457579276522743511 20251121186368914784115267)
            ·
              refine ⟨30376681779553372176172901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20251121186368914784115267 30376681779553372176172901)
              ·
                refine ⟨5695627833666257283032419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30376681779553372176172901 5695627833666257283032419)
                ·
                  refine ⟨8543441750499385924548629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5695627833666257283032419 8543441750499385924548629)
                  ·
                    refine ⟨400473832054658715213217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8543441750499385924548629 400473832054658715213217)
                    ·
                      rfl

theorem cell22_1169880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_1169880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169880 prefixEnd_1169880 := by exact prefixLift 1169880
  have htrace : WordTrace (prefixWord ++ tailWord_1169880) baseStart_1169880 baseEnd_1169880 := by
    simpa [prefixWord, tailWord_1169880, baseEnd_1169880] using wordTrace_append hprefix tailTrace_1169880
  have hstable : (prefixWord ++ tailWord_1169880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169880).length < 2 ^ (prefixWord ++ tailWord_1169880).sum := by decide
  have hdescent : baseEnd_1169880 < baseStart_1169880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169882 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 1, 5]
def baseStart_1169882 : Nat := 118140960795 + 1169882 * 2 ^ 59
def prefixEnd_1169882 : Nat := 4983230072969 + 3 ^ 40 * 1169882 * 2
def baseEnd_1169882 : Nat := 400474516695531376663211

theorem tailTrace_1169882 : CollatzResearch.WordTrace tailWord_1169882 prefixEnd_1169882 400474516695531376663211 := by
  unfold tailWord_1169882
  simp only [CollatzResearch.WordTrace]
  refine ⟨10667275486931197195955975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28446067965149859189215933 10667275486931197195955975)
  ·
    refine ⟨16000913230396795793933963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10667275486931197195955975 16000913230396795793933963)
    ·
      refine ⟨24001369845595193690900945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16000913230396795793933963 24001369845595193690900945)
      ·
        refine ⟨18001027384196395268175709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24001369845595193690900945 18001027384196395268175709)
        ·
          refine ⟨6750385269073648225565891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18001027384196395268175709 6750385269073648225565891)
          ·
            refine ⟨10125577903610472338348837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6750385269073648225565891 10125577903610472338348837)
            ·
              refine ⟨1898545856926963563440407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10125577903610472338348837 1898545856926963563440407)
              ·
                refine ⟨2847818785390445345160611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1898545856926963563440407 2847818785390445345160611)
                ·
                  refine ⟨4271728178085668017740917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2847818785390445345160611 4271728178085668017740917)
                  ·
                    refine ⟨400474516695531376663211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4271728178085668017740917 400474516695531376663211)
                    ·
                      rfl

theorem cell22_1169882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_1169882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169882 prefixEnd_1169882 := by exact prefixLift 1169882
  have htrace : WordTrace (prefixWord ++ tailWord_1169882) baseStart_1169882 baseEnd_1169882 := by
    simpa [prefixWord, tailWord_1169882, baseEnd_1169882] using wordTrace_append hprefix tailTrace_1169882
  have hstable : (prefixWord ++ tailWord_1169882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169882).length < 2 ^ (prefixWord ++ tailWord_1169882).sum := by decide
  have hdescent : baseEnd_1169882 < baseStart_1169882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169901 : List Nat := [1, 5, 1, 3, 1, 2, 2, 3, 4]
def baseStart_1169901 : Nat := 118140960795 + 1169901 * 2 ^ 59
def prefixEnd_1169901 : Nat := 4983230072969 + 3 ^ 40 * 1169901 * 2
def baseEnd_1169901 : Nat := 133493673594607220146051

theorem tailTrace_1169901 : CollatzResearch.WordTrace tailWord_1169901 prefixEnd_1169901 133493673594607220146051 := by
  unfold tailWord_1169901
  simp only [CollatzResearch.WordTrace]
  refine ⟨42669794934655955028765557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28446529956437303352510371 42669794934655955028765557)
  ·
    refine ⟨4000293275123995783946771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42669794934655955028765557 4000293275123995783946771)
    ·
      refine ⟨6000439912685993675920157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4000293275123995783946771 6000439912685993675920157)
      ·
        refine ⟨2250164967257247628470059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6000439912685993675920157 2250164967257247628470059)
        ·
          refine ⟨3375247450885871442705089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2250164967257247628470059 3375247450885871442705089)
          ·
            refine ⟨2531435588164403582028817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3375247450885871442705089 2531435588164403582028817)
            ·
              refine ⟨1898576691123302686521613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2531435588164403582028817 1898576691123302686521613)
              ·
                refine ⟨711966259171238507445605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1898576691123302686521613 711966259171238507445605)
                ·
                  refine ⟨133493673594607220146051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 711966259171238507445605 133493673594607220146051)
                  ·
                    rfl

theorem cell22_1169901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_1169901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169901 prefixEnd_1169901 := by exact prefixLift 1169901
  have htrace : WordTrace (prefixWord ++ tailWord_1169901) baseStart_1169901 baseEnd_1169901 := by
    simpa [prefixWord, tailWord_1169901, baseEnd_1169901] using wordTrace_append hprefix tailTrace_1169901
  have hstable : (prefixWord ++ tailWord_1169901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169901).length < 2 ^ (prefixWord ++ tailWord_1169901).sum := by decide
  have hdescent : baseEnd_1169901 < baseStart_1169901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169925 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 1, 8]
def baseStart_1169925 : Nat := 118140960795 + 1169925 * 2 ^ 59
def prefixEnd_1169925 : Nat := 4983230072969 + 3 ^ 40 * 1169925 * 2
def baseEnd_1169925 : Nat := 400489236474293597838079

theorem tailTrace_1169925 : CollatzResearch.WordTrace tailWord_1169925 prefixEnd_1169925 400489236474293597838079 := by
  unfold tailWord_1169925
  simp only [CollatzResearch.WordTrace]
  refine ⟨42670670286569007127639229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28447113524379338085092819 42670670286569007127639229)
  ·
    refine ⟨16001501357463377672864711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42670670286569007127639229 16001501357463377672864711)
    ·
      refine ⟨24002252036195066509297067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16001501357463377672864711 24002252036195066509297067)
      ·
        refine ⟨36003378054292599763945601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24002252036195066509297067 36003378054292599763945601)
        ·
          refine ⟨27002533540719449822959201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36003378054292599763945601 27002533540719449822959201)
          ·
            refine ⟨20251900155539587367219401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27002533540719449822959201 20251900155539587367219401)
            ·
              refine ⟨15188925116654690525414551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20251900155539587367219401 15188925116654690525414551)
              ·
                refine ⟨22783387674982035788121827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15188925116654690525414551 22783387674982035788121827)
                ·
                  refine ⟨34175081512473053682182741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22783387674982035788121827 34175081512473053682182741)
                  ·
                    refine ⟨400489236474293597838079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34175081512473053682182741 400489236474293597838079)
                    ·
                      rfl

theorem cell22_1169925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_1169925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169925 prefixEnd_1169925 := by exact prefixLift 1169925
  have htrace : WordTrace (prefixWord ++ tailWord_1169925) baseStart_1169925 baseEnd_1169925 := by
    simpa [prefixWord, tailWord_1169925, baseEnd_1169925] using wordTrace_append hprefix tailTrace_1169925
  have hstable : (prefixWord ++ tailWord_1169925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169925).length < 2 ^ (prefixWord ++ tailWord_1169925).sum := by decide
  have hdescent : baseEnd_1169925 < baseStart_1169925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169933 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_1169933 : Nat := 118140960795 + 1169933 * 2 ^ 59
def prefixEnd_1169933 : Nat := 4983230072969 + 3 ^ 40 * 1169933 * 2
def baseEnd_1169933 : Nat := 400491975037784243638055

theorem tailTrace_1169933 : CollatzResearch.WordTrace tailWord_1169933 prefixEnd_1169933 400491975037784243638055 := by
  unfold tailWord_1169933
  simp only [CollatzResearch.WordTrace]
  refine ⟨42670962070540024493930453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28447308047026682995953635 42670962070540024493930453)
  ·
    refine ⟨1000100673528281824076495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 42670962070540024493930453 1000100673528281824076495)
    ·
      refine ⟨1500151010292422736114743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1000100673528281824076495 1500151010292422736114743)
      ·
        refine ⟨2250226515438634104172115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1500151010292422736114743 2250226515438634104172115)
        ·
          refine ⟨3375339773157951156258173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2250226515438634104172115 3375339773157951156258173)
          ·
            refine ⟨1265752414934231683596815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3375339773157951156258173 1265752414934231683596815)
            ·
              refine ⟨1898628622401347525395223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1265752414934231683596815 1898628622401347525395223)
              ·
                refine ⟨2847942933602021288092835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1898628622401347525395223 2847942933602021288092835)
                ·
                  refine ⟨4271914400403031932139253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2847942933602021288092835 4271914400403031932139253)
                  ·
                    refine ⟨400491975037784243638055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4271914400403031932139253 400491975037784243638055)
                    ·
                      rfl

theorem cell22_1169933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_1169933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169933 prefixEnd_1169933 := by exact prefixLift 1169933
  have htrace : WordTrace (prefixWord ++ tailWord_1169933) baseStart_1169933 baseEnd_1169933 := by
    simpa [prefixWord, tailWord_1169933, baseEnd_1169933] using wordTrace_append hprefix tailTrace_1169933
  have hstable : (prefixWord ++ tailWord_1169933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169933).length < 2 ^ (prefixWord ++ tailWord_1169933).sum := by decide
  have hdescent : baseEnd_1169933 < baseStart_1169933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169944 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 3, 3]
def baseStart_1169944 : Nat := 118140960795 + 1169944 * 2 ^ 59
def prefixEnd_1169944 : Nat := 4983230072969 + 3 ^ 40 * 1169944 * 2
def baseEnd_1169944 : Nat := 400495740562583881613021

theorem tailTrace_1169944 : CollatzResearch.WordTrace tailWord_1169944 prefixEnd_1169944 400495740562583881613021 := by
  unfold tailWord_1169944
  simp only [CollatzResearch.WordTrace]
  refine ⟨21335681636750086686290443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28447575515666782248387257 21335681636750086686290443)
  ·
    refine ⟨32003522455125130029435665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21335681636750086686290443 32003522455125130029435665)
    ·
      refine ⟨24002641841343847522076749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32003522455125130029435665 24002641841343847522076749)
      ·
        refine ⟨9000990690503942820778781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24002641841343847522076749 9000990690503942820778781)
        ·
          refine ⟨3375371508938978557792043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9000990690503942820778781 3375371508938978557792043)
          ·
            refine ⟨5063057263408467836688065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3375371508938978557792043 5063057263408467836688065)
            ·
              refine ⟨3797292947556350877516049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5063057263408467836688065 3797292947556350877516049)
              ·
                refine ⟨2847969710667263158137037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3797292947556350877516049 2847969710667263158137037)
                ·
                  refine ⟨1067988641500223684301389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2847969710667263158137037 1067988641500223684301389)
                  ·
                    refine ⟨400495740562583881613021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1067988641500223684301389 400495740562583881613021)
                    ·
                      rfl

theorem cell22_1169944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_1169944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169944 prefixEnd_1169944 := by exact prefixLift 1169944
  have htrace : WordTrace (prefixWord ++ tailWord_1169944) baseStart_1169944 baseEnd_1169944 := by
    simpa [prefixWord, tailWord_1169944, baseEnd_1169944] using wordTrace_append hprefix tailTrace_1169944
  have hstable : (prefixWord ++ tailWord_1169944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169944).length < 2 ^ (prefixWord ++ tailWord_1169944).sum := by decide
  have hdescent : baseEnd_1169944 < baseStart_1169944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169974 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_1169974 : Nat := 118140960795 + 1169974 * 2 ^ 59
def prefixEnd_1169974 : Nat := 4983230072969 + 3 ^ 40 * 1169974 * 2
def baseEnd_1169974 : Nat := 133502003391891267787643

theorem tailTrace_1169974 : CollatzResearch.WordTrace tailWord_1169974 prefixEnd_1169974 133502003391891267787643 := by
  unfold tailWord_1169974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2667028591461968031010811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28448304975594325664115317 2667028591461968031010811)
  ·
    refine ⟨4000542887192952046516217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2667028591461968031010811 4000542887192952046516217)
    ·
      refine ⟨3000407165394714034887163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4000542887192952046516217 3000407165394714034887163)
      ·
        refine ⟨4500610748092071052330745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3000407165394714034887163 4500610748092071052330745)
        ·
          refine ⟨3375458061069053289248059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4500610748092071052330745 3375458061069053289248059)
          ·
            refine ⟨5063187091603579933872089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3375458061069053289248059 5063187091603579933872089)
            ·
              refine ⟨3797390318702684950404067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5063187091603579933872089 3797390318702684950404067)
              ·
                refine ⟨5696085478054027425606101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3797390318702684950404067 5696085478054027425606101)
                ·
                  refine ⟨133502003391891267787643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5696085478054027425606101 133502003391891267787643)
                  ·
                    rfl

theorem cell22_1169974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_1169974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169974 prefixEnd_1169974 := by exact prefixLift 1169974
  have htrace : WordTrace (prefixWord ++ tailWord_1169974) baseStart_1169974 baseEnd_1169974 := by
    simpa [prefixWord, tailWord_1169974, baseEnd_1169974] using wordTrace_append hprefix tailTrace_1169974
  have hstable : (prefixWord ++ tailWord_1169974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169974).length < 2 ^ (prefixWord ++ tailWord_1169974).sum := by decide
  have hdescent : baseEnd_1169974 < baseStart_1169974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169978 : List Nat := [3, 1, 1, 1, 3, 4, 3, 2, 1, 3]
def baseStart_1169978 : Nat := 118140960795 + 1169978 * 2 ^ 59
def prefixEnd_1169978 : Nat := 4983230072969 + 3 ^ 40 * 1169978 * 2
def baseEnd_1169978 : Nat := 400507379457419126262917

theorem tailTrace_1169978 : CollatzResearch.WordTrace tailWord_1169978 prefixEnd_1169978 400507379457419126262917 := by
  unfold tailWord_1169978
  simp only [CollatzResearch.WordTrace]
  refine ⟨10668150838844249294829647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28448402236917998119545725 10668150838844249294829647)
  ·
    refine ⟨16002226258266373942244471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10668150838844249294829647 16002226258266373942244471)
    ·
      refine ⟨24003339387399560913366707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16002226258266373942244471 24003339387399560913366707)
      ·
        refine ⟨36005009081099341370050061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24003339387399560913366707 36005009081099341370050061)
        ·
          refine ⟨13501878405412253013768773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36005009081099341370050061 13501878405412253013768773)
          ·
            refine ⟨2531602201014797440081645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13501878405412253013768773 2531602201014797440081645)
            ·
              refine ⟨949350825380549040030617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2531602201014797440081645 949350825380549040030617)
              ·
                refine ⟨712013119035411780022963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 949350825380549040030617 712013119035411780022963)
                ·
                  refine ⟨1068019678553117670034445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712013119035411780022963 1068019678553117670034445)
                  ·
                    refine ⟨400507379457419126262917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1068019678553117670034445 400507379457419126262917)
                    ·
                      rfl

theorem cell22_1169978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 1, 3].length) (baseStart_1169978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169978 prefixEnd_1169978 := by exact prefixLift 1169978
  have htrace : WordTrace (prefixWord ++ tailWord_1169978) baseStart_1169978 baseEnd_1169978 := by
    simpa [prefixWord, tailWord_1169978, baseEnd_1169978] using wordTrace_append hprefix tailTrace_1169978
  have hstable : (prefixWord ++ tailWord_1169978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169978).length < 2 ^ (prefixWord ++ tailWord_1169978).sum := by decide
  have hdescent : baseEnd_1169978 < baseStart_1169978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1169991 : List Nat := [1, 1, 4, 1, 4, 3, 2, 1, 5]
def baseStart_1169991 : Nat := 118140960795 + 1169991 * 2 ^ 59
def prefixEnd_1169991 : Nat := 4983230072969 + 3 ^ 40 * 1169991 * 2
def baseEnd_1169991 : Nat := 133503943207697141895959

theorem tailTrace_1169991 : CollatzResearch.WordTrace tailWord_1169991 prefixEnd_1169991 133503943207697141895959 := by
  unfold tailWord_1169991
  simp only [CollatzResearch.WordTrace]
  refine ⟨42673077504329900399541827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28448718336219933599694551 42673077504329900399541827)
  ·
    refine ⟨64009616256494850599312741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42673077504329900399541827 64009616256494850599312741)
    ·
      refine ⟨12001803048092784487371139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64009616256494850599312741 12001803048092784487371139)
      ·
        refine ⟨18002704572139176731056709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12001803048092784487371139 18002704572139176731056709)
        ·
          refine ⟨3375507107276095637073133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18002704572139176731056709 3375507107276095637073133)
          ·
            refine ⟨1265815165228535863902425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3375507107276095637073133 1265815165228535863902425)
            ·
              refine ⟨949361373921401897926819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1265815165228535863902425 949361373921401897926819)
              ·
                refine ⟨1424042060882102846890229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 949361373921401897926819 1424042060882102846890229)
                ·
                  refine ⟨133503943207697141895959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1424042060882102846890229 133503943207697141895959)
                  ·
                    rfl

theorem cell22_1169991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 5].length) (baseStart_1169991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1169991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1169991 prefixEnd_1169991 := by exact prefixLift 1169991
  have htrace : WordTrace (prefixWord ++ tailWord_1169991) baseStart_1169991 baseEnd_1169991 := by
    simpa [prefixWord, tailWord_1169991, baseEnd_1169991] using wordTrace_append hprefix tailTrace_1169991
  have hstable : (prefixWord ++ tailWord_1169991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1169991).length < 2 ^ (prefixWord ++ tailWord_1169991).sum := by decide
  have hdescent : baseEnd_1169991 < baseStart_1169991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1169991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170002 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 8]
def baseStart_1170002 : Nat := 118140960795 + 1170002 * 2 ^ 59
def prefixEnd_1170002 : Nat := 4983230072969 + 3 ^ 40 * 1170002 * 2
def baseEnd_1170002 : Nat := 133505198382630354554281

theorem tailTrace_1170002 : CollatzResearch.WordTrace tailWord_1170002 prefixEnd_1170002 133505198382630354554281 := by
  unfold tailWord_1170002
  simp only [CollatzResearch.WordTrace]
  refine ⟨10668369676822512319548065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28448985804860032852128173 10668369676822512319548065)
  ·
    refine ⟨8001277257616884239661049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10668369676822512319548065 8001277257616884239661049)
    ·
      refine ⟨6000957943212663179745787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8001277257616884239661049 6000957943212663179745787)
      ·
        refine ⟨9001436914818994769618681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6000957943212663179745787 9001436914818994769618681)
        ·
          refine ⟨6751077686114246077214011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9001436914818994769618681 6751077686114246077214011)
          ·
            refine ⟨10126616529171369115821017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6751077686114246077214011 10126616529171369115821017)
            ·
              refine ⟨7594962396878526836865763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10126616529171369115821017 7594962396878526836865763)
              ·
                refine ⟨11392443595317790255298645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7594962396878526836865763 11392443595317790255298645)
                ·
                  refine ⟨133505198382630354554281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11392443595317790255298645 133505198382630354554281)
                  ·
                    rfl

theorem cell22_1170002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_1170002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170002 prefixEnd_1170002 := by exact prefixLift 1170002
  have htrace : WordTrace (prefixWord ++ tailWord_1170002) baseStart_1170002 baseEnd_1170002 := by
    simpa [prefixWord, tailWord_1170002, baseEnd_1170002] using wordTrace_append hprefix tailTrace_1170002
  have hstable : (prefixWord ++ tailWord_1170002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170002).length < 2 ^ (prefixWord ++ tailWord_1170002).sum := by decide
  have hdescent : baseEnd_1170002 < baseStart_1170002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170004 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_1170004 : Nat := 118140960795 + 1170004 * 2 ^ 59
def prefixEnd_1170004 : Nat := 4983230072969 + 3 ^ 40 * 1170004 * 2
def baseEnd_1170004 : Nat := 400516279788763725112837

theorem tailTrace_1170004 : CollatzResearch.WordTrace tailWord_1170004 prefixEnd_1170004 400516279788763725112837 := by
  unfold tailWord_1170004
  simp only [CollatzResearch.WordTrace]
  refine ⟨21336775826641401809882533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28449034435521869079843377 21336775826641401809882533)
  ·
    refine ⟨4000645467495262839352975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21336775826641401809882533 4000645467495262839352975)
    ·
      refine ⟨6000968201242894259029463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4000645467495262839352975 6000968201242894259029463)
      ·
        refine ⟨9001452301864341388544195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6000968201242894259029463 9001452301864341388544195)
        ·
          refine ⟨13502178452796512082816293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9001452301864341388544195 13502178452796512082816293)
          ·
            refine ⟨2531658459899346015528055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13502178452796512082816293 2531658459899346015528055)
            ·
              refine ⟨3797487689849019023292083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2531658459899346015528055 3797487689849019023292083)
              ·
                refine ⟨5696231534773528534938125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3797487689849019023292083 5696231534773528534938125)
                ·
                  refine ⟨2136086825540073200601797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5696231534773528534938125 2136086825540073200601797)
                  ·
                    refine ⟨400516279788763725112837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2136086825540073200601797 400516279788763725112837)
                    ·
                      rfl

theorem cell22_1170004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_1170004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170004 prefixEnd_1170004 := by exact prefixLift 1170004
  have htrace : WordTrace (prefixWord ++ tailWord_1170004) baseStart_1170004 baseEnd_1170004 := by
    simpa [prefixWord, tailWord_1170004, baseEnd_1170004] using wordTrace_append hprefix tailTrace_1170004
  have hstable : (prefixWord ++ tailWord_1170004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170004).length < 2 ^ (prefixWord ++ tailWord_1170004).sum := by decide
  have hdescent : baseEnd_1170004 < baseStart_1170004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170017 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 3, 5]
def baseStart_1170017 : Nat := 118140960795 + 1170017 * 2 ^ 59
def prefixEnd_1170017 : Nat := 4983230072969 + 3 ^ 40 * 1170017 * 2
def baseEnd_1170017 : Nat := 400520729954436024537797

theorem tailTrace_1170017 : CollatzResearch.WordTrace tailWord_1170017 prefixEnd_1170017 400520729954436024537797 := by
  unfold tailWord_1170017
  simp only [CollatzResearch.WordTrace]
  refine ⟨42674025802235706839988305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28449350534823804559992203 42674025802235706839988305)
  ·
    refine ⟨32005519351676780129991229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42674025802235706839988305 32005519351676780129991229)
    ·
      refine ⟨12002069756878792548746711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32005519351676780129991229 12002069756878792548746711)
      ·
        refine ⟨18003104635318188823120067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12002069756878792548746711 18003104635318188823120067)
        ·
          refine ⟨27004656952977283234680101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18003104635318188823120067 27004656952977283234680101)
          ·
            refine ⟨5063373178683240606502519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27004656952977283234680101 5063373178683240606502519)
            ·
              refine ⟨7595059768024860909753779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5063373178683240606502519 7595059768024860909753779)
              ·
                refine ⟨11392589652037291364630669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7595059768024860909753779 11392589652037291364630669)
                ·
                  refine ⟨4272221119513984261736501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11392589652037291364630669 4272221119513984261736501)
                  ·
                    refine ⟨400520729954436024537797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4272221119513984261736501 400520729954436024537797)
                    ·
                      rfl

theorem cell22_1170017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_1170017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170017 prefixEnd_1170017 := by exact prefixLift 1170017
  have htrace : WordTrace (prefixWord ++ tailWord_1170017) baseStart_1170017 baseEnd_1170017 := by
    simpa [prefixWord, tailWord_1170017, baseEnd_1170017] using wordTrace_append hprefix tailTrace_1170017
  have hstable : (prefixWord ++ tailWord_1170017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170017).length < 2 ^ (prefixWord ++ tailWord_1170017).sum := by decide
  have hdescent : baseEnd_1170017 < baseStart_1170017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170019 : List Nat := [1, 1, 1, 5, 1, 2, 2, 5, 4]
def baseStart_1170019 : Nat := 118140960795 + 1170019 * 2 ^ 59
def prefixEnd_1170019 : Nat := 4983230072969 + 3 ^ 40 * 1170019 * 2
def baseEnd_1170019 : Nat := 133507138198436228662597

theorem tailTrace_1170019 : CollatzResearch.WordTrace tailWord_1170019 prefixEnd_1170019 133507138198436228662597 := by
  unfold tailWord_1170019
  simp only [CollatzResearch.WordTrace]
  refine ⟨42674098748228461181561111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28449399165485640787707407 42674098748228461181561111)
  ·
    refine ⟨64011148122342691772341667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42674098748228461181561111 64011148122342691772341667)
    ·
      refine ⟨96016722183514037658512501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64011148122342691772341667 96016722183514037658512501)
      ·
        refine ⟨9001567704704441030485547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96016722183514037658512501 9001567704704441030485547)
        ·
          refine ⟨13502351557056661545728321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9001567704704441030485547 13502351557056661545728321)
          ·
            refine ⟨10126763667792496159296241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13502351557056661545728321 10126763667792496159296241)
            ·
              refine ⟨7595072750844372119472181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10126763667792496159296241 7595072750844372119472181)
              ·
                refine ⟨712038070391659886200517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7595072750844372119472181 712038070391659886200517)
                ·
                  refine ⟨133507138198436228662597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 712038070391659886200517 133507138198436228662597)
                  ·
                    rfl

theorem cell22_1170019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 4].length) (baseStart_1170019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170019 prefixEnd_1170019 := by exact prefixLift 1170019
  have htrace : WordTrace (prefixWord ++ tailWord_1170019) baseStart_1170019 baseEnd_1170019 := by
    simpa [prefixWord, tailWord_1170019, baseEnd_1170019] using wordTrace_append hprefix tailTrace_1170019
  have hstable : (prefixWord ++ tailWord_1170019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170019).length < 2 ^ (prefixWord ++ tailWord_1170019).sum := by decide
  have hdescent : baseEnd_1170019 < baseStart_1170019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170066 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1170066 : Nat := 118140960795 + 1170066 * 2 ^ 59
def prefixEnd_1170066 : Nat := 4983230072969 + 3 ^ 40 * 1170066 * 2
def baseEnd_1170066 : Nat := 400537503655816230062647

theorem tailTrace_1170066 : CollatzResearch.WordTrace tailWord_1170066 prefixEnd_1170066 400537503655816230062647 := by
  unfold tailWord_1170066
  simp only [CollatzResearch.WordTrace]
  refine ⟨10668953244764547052130513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28450541986038792139014701 10668953244764547052130513)
  ·
    refine ⟨8001714933573410289097885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10668953244764547052130513 8001714933573410289097885)
    ·
      refine ⟨3000643100090028858411707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8001714933573410289097885 3000643100090028858411707)
      ·
        refine ⟨4500964650135043287617561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3000643100090028858411707 4500964650135043287617561)
        ·
          refine ⟨3375723487601282465713171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4500964650135043287617561 3375723487601282465713171)
          ·
            refine ⟨5063585231401923698569757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3375723487601282465713171 5063585231401923698569757)
            ·
              refine ⟨1898844461775721386963659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5063585231401923698569757 1898844461775721386963659)
              ·
                refine ⟨2848266692663582080445489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1898844461775721386963659 2848266692663582080445489)
                ·
                  refine ⟨2136200019497686560334117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2848266692663582080445489 2136200019497686560334117)
                  ·
                    refine ⟨400537503655816230062647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2136200019497686560334117 400537503655816230062647)
                    ·
                      rfl

theorem cell22_1170066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1170066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170066 prefixEnd_1170066 := by exact prefixLift 1170066
  have htrace : WordTrace (prefixWord ++ tailWord_1170066) baseStart_1170066 baseEnd_1170066 := by
    simpa [prefixWord, tailWord_1170066, baseEnd_1170066] using wordTrace_append hprefix tailTrace_1170066
  have hstable : (prefixWord ++ tailWord_1170066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170066).length < 2 ^ (prefixWord ++ tailWord_1170066).sum := by decide
  have hdescent : baseEnd_1170066 < baseStart_1170066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170102 : List Nat := [5, 1, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_1170102 : Nat := 118140960795 + 1170102 * 2 ^ 59
def prefixEnd_1170102 : Nat := 4983230072969 + 3 ^ 40 * 1170102 * 2
def baseEnd_1170102 : Nat := 400549827191524136162537

theorem tailTrace_1170102 : CollatzResearch.WordTrace tailWord_1170102 prefixEnd_1170102 400549827191524136162537 := by
  unfold tailWord_1170102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2667320375432985397302035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28451417337951844237888373 2667320375432985397302035)
  ·
    refine ⟨4000980563149478095953053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2667320375432985397302035 4000980563149478095953053)
    ·
      refine ⟨1500367711181054285982395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4000980563149478095953053 1500367711181054285982395)
      ·
        refine ⟨2250551566771581428973593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1500367711181054285982395 2250551566771581428973593)
        ·
          refine ⟨1687913675078686071730195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2250551566771581428973593 1687913675078686071730195)
          ·
            refine ⟨2531870512618029107595293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1687913675078686071730195 2531870512618029107595293)
            ·
              refine ⟨949451442231760915348235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2531870512618029107595293 949451442231760915348235)
              ·
                refine ⟨1424177163347641373022353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 949451442231760915348235 1424177163347641373022353)
                ·
                  refine ⟨1068132872510731029766765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1424177163347641373022353 1068132872510731029766765)
                  ·
                    refine ⟨400549827191524136162537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1068132872510731029766765 400549827191524136162537)
                    ·
                      rfl

theorem cell22_1170102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_1170102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170102 prefixEnd_1170102 := by exact prefixLift 1170102
  have htrace : WordTrace (prefixWord ++ tailWord_1170102) baseStart_1170102 baseEnd_1170102 := by
    simpa [prefixWord, tailWord_1170102, baseEnd_1170102] using wordTrace_append hprefix tailTrace_1170102
  have hstable : (prefixWord ++ tailWord_1170102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170102).length < 2 ^ (prefixWord ++ tailWord_1170102).sum := by decide
  have hdescent : baseEnd_1170102 < baseStart_1170102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170199 : List Nat := [1, 1, 3, 4, 3, 10]
def baseStart_1170199 : Nat := 118140960795 + 1170199 * 2 ^ 59
def prefixEnd_1170199 : Nat := 4983230072969 + 3 ^ 40 * 1170199 * 2
def baseEnd_1170199 : Nat := 4945469534245039709719

theorem tailTrace_1170199 : CollatzResearch.WordTrace tailWord_1170199 prefixEnd_1170199 4945469534245039709719 := by
  unfold tailWord_1170199
  simp only [CollatzResearch.WordTrace]
  refine ⟨42680663887576351923113651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28453775925050901282075767 42680663887576351923113651)
  ·
    refine ⟨64020995831364527884670477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42680663887576351923113651 64020995831364527884670477)
    ·
      refine ⟨24007873436761697956751429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64020995831364527884670477 24007873436761697956751429)
      ·
        refine ⟨4501476269392818366890893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24007873436761697956751429 4501476269392818366890893)
        ·
          refine ⟨1688053601022306887584085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4501476269392818366890893 1688053601022306887584085)
          ·
            refine ⟨4945469534245039709719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1688053601022306887584085 4945469534245039709719)
            ·
              rfl

theorem cell22_1170199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 10].length) (baseStart_1170199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170199 prefixEnd_1170199 := by exact prefixLift 1170199
  have htrace : WordTrace (prefixWord ++ tailWord_1170199) baseStart_1170199 baseEnd_1170199 := by
    simpa [prefixWord, tailWord_1170199, baseEnd_1170199] using wordTrace_append hprefix tailTrace_1170199
  have hstable : (prefixWord ++ tailWord_1170199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170199).length < 2 ^ (prefixWord ++ tailWord_1170199).sum := by decide
  have hdescent : baseEnd_1170199 < baseStart_1170199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170205 : List Nat := [1, 4, 2, 4, 1, 1, 1, 4, 4]
def baseStart_1170205 : Nat := 118140960795 + 1170205 * 2 ^ 59
def prefixEnd_1170205 : Nat := 4983230072969 + 3 ^ 40 * 1170205 * 2
def baseEnd_1170205 : Nat := 133528362065488733612407

theorem tailTrace_1170205 : CollatzResearch.WordTrace tailWord_1170205 prefixEnd_1170205 133528362065488733612407 := by
  unfold tailWord_1170205
  simp only [CollatzResearch.WordTrace]
  refine ⟨42680882725554614947832069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28453921817036409965221379 42680882725554614947832069)
  ·
    refine ⟨8002665511041490302718513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42680882725554614947832069 8002665511041490302718513)
    ·
      refine ⟨6001999133281117727038885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8002665511041490302718513 6001999133281117727038885)
      ·
        refine ⟨1125374837490209573819791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6001999133281117727038885 1125374837490209573819791)
        ·
          refine ⟨1688062256235314360729687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1125374837490209573819791 1688062256235314360729687)
          ·
            refine ⟨2532093384352971541094531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1688062256235314360729687 2532093384352971541094531)
            ·
              refine ⟨3798140076529457311641797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2532093384352971541094531 3798140076529457311641797)
              ·
                refine ⟨712151264349273245932837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3798140076529457311641797 712151264349273245932837)
                ·
                  refine ⟨133528362065488733612407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 712151264349273245932837 133528362065488733612407)
                  ·
                    rfl

theorem cell22_1170205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_1170205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170205 prefixEnd_1170205 := by exact prefixLift 1170205
  have htrace : WordTrace (prefixWord ++ tailWord_1170205) baseStart_1170205 baseEnd_1170205 := by
    simpa [prefixWord, tailWord_1170205, baseEnd_1170205] using wordTrace_append hprefix tailTrace_1170205
  have hstable : (prefixWord ++ tailWord_1170205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170205).length < 2 ^ (prefixWord ++ tailWord_1170205).sum := by decide
  have hdescent : baseEnd_1170205 < baseStart_1170205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170231 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 3, 3]
def baseStart_1170231 : Nat := 118140960795 + 1170231 * 2 ^ 59
def prefixEnd_1170231 : Nat := 4983230072969 + 3 ^ 40 * 1170231 * 2
def baseEnd_1170231 : Nat := 400593986527810799687141

theorem tailTrace_1170231 : CollatzResearch.WordTrace tailWord_1170231 prefixEnd_1170231 400593986527810799687141 := by
  unfold tailWord_1170231
  simp only [CollatzResearch.WordTrace]
  refine ⟨42681831023460421388278547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28454554015640280925519031 42681831023460421388278547)
  ·
    refine ⟨64022746535190632082417821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42681831023460421388278547 64022746535190632082417821)
    ·
      refine ⟨24008529950696487030906683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64022746535190632082417821 24008529950696487030906683)
      ·
        refine ⟨36012794926044730546360025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24008529950696487030906683 36012794926044730546360025)
        ·
          refine ⟨27009596194533547909770019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36012794926044730546360025 27009596194533547909770019)
          ·
            refine ⟨40514394291800321864655029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27009596194533547909770019 40514394291800321864655029)
            ·
              refine ⟨3798224464856280174811409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40514394291800321864655029 3798224464856280174811409)
              ·
                refine ⟨2848668348642210131108557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3798224464856280174811409 2848668348642210131108557)
                ·
                  refine ⟨1068250630740828799165709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2848668348642210131108557 1068250630740828799165709)
                  ·
                    refine ⟨400593986527810799687141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1068250630740828799165709 400593986527810799687141)
                    ·
                      rfl

theorem cell22_1170231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_1170231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170231 prefixEnd_1170231 := by exact prefixLift 1170231
  have htrace : WordTrace (prefixWord ++ tailWord_1170231) baseStart_1170231 baseEnd_1170231 := by
    simpa [prefixWord, tailWord_1170231, baseEnd_1170231] using wordTrace_append hprefix tailTrace_1170231
  have hstable : (prefixWord ++ tailWord_1170231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170231).length < 2 ^ (prefixWord ++ tailWord_1170231).sum := by decide
  have hdescent : baseEnd_1170231 < baseStart_1170231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170276 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_1170276 : Nat := 118140960795 + 1170276 * 2 ^ 59
def prefixEnd_1170276 : Nat := 4983230072969 + 3 ^ 40 * 1170276 * 2
def baseEnd_1170276 : Nat := 400609390947445682312003

theorem tailTrace_1170276 : CollatzResearch.WordTrace tailWord_1170276 prefixEnd_1170276 400609390947445682312003 := by
  unfold tailWord_1170276
  simp only [CollatzResearch.WordTrace]
  refine ⟨21341736154148697036833341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28455648205531596049111121 21341736154148697036833341)
  ·
    refine ⟨8003151057805761388812503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21341736154148697036833341 8003151057805761388812503)
    ·
      refine ⟨12004726586708642083218755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8003151057805761388812503 12004726586708642083218755)
      ·
        refine ⟨18007089880062963124828133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12004726586708642083218755 18007089880062963124828133)
        ·
          refine ⟨3376329352511805585905275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18007089880062963124828133 3376329352511805585905275)
          ·
            refine ⟨5064494028767708378857913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3376329352511805585905275 5064494028767708378857913)
            ·
              refine ⟨3798370521575781284143435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5064494028767708378857913 3798370521575781284143435)
              ·
                refine ⟨5697555782363671926215153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3798370521575781284143435 5697555782363671926215153)
                ·
                  refine ⟨4273166836772753944661365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5697555782363671926215153 4273166836772753944661365)
                  ·
                    refine ⟨400609390947445682312003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4273166836772753944661365 400609390947445682312003)
                    ·
                      rfl

theorem cell22_1170276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_1170276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170276 prefixEnd_1170276 := by exact prefixLift 1170276
  have htrace : WordTrace (prefixWord ++ tailWord_1170276) baseStart_1170276 baseEnd_1170276 := by
    simpa [prefixWord, tailWord_1170276, baseEnd_1170276] using wordTrace_append hprefix tailTrace_1170276
  have hstable : (prefixWord ++ tailWord_1170276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170276).length < 2 ^ (prefixWord ++ tailWord_1170276).sum := by decide
  have hdescent : baseEnd_1170276 < baseStart_1170276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170291 : List Nat := [1, 1, 1, 2, 2, 1, 5, 4, 1, 4]
def baseStart_1170291 : Nat := 118140960795 + 1170291 * 2 ^ 59
def prefixEnd_1170291 : Nat := 4983230072969 + 3 ^ 40 * 1170291 * 2
def baseEnd_1170291 : Nat := 400614525753990643186957

theorem tailTrace_1170291 : CollatzResearch.WordTrace tailWord_1170291 prefixEnd_1170291 400614525753990643186957 := by
  unfold tailWord_1170291
  simp only [CollatzResearch.WordTrace]
  refine ⟨42684019403243051635462727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28456012935495367756975151 42684019403243051635462727)
  ·
    refine ⟨64026029104864577453194091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42684019403243051635462727 64026029104864577453194091)
    ·
      refine ⟨96039043657296866179791137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64026029104864577453194091 96039043657296866179791137)
      ·
        refine ⟨72029282742972649634843353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96039043657296866179791137 72029282742972649634843353)
        ·
          refine ⟨54021962057229487226132515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72029282742972649634843353 54021962057229487226132515)
          ·
            refine ⟨81032943085844230839198773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54021962057229487226132515 81032943085844230839198773)
            ·
              refine ⟨7596838414297896641174885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81032943085844230839198773 7596838414297896641174885)
              ·
                refine ⟨1424407202680855620220291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7596838414297896641174885 1424407202680855620220291)
                ·
                  refine ⟨2136610804021283430330437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1424407202680855620220291 2136610804021283430330437)
                  ·
                    refine ⟨400614525753990643186957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2136610804021283430330437 400614525753990643186957)
                    ·
                      rfl

theorem cell22_1170291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 4].length) (baseStart_1170291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170291 prefixEnd_1170291 := by exact prefixLift 1170291
  have htrace : WordTrace (prefixWord ++ tailWord_1170291) baseStart_1170291 baseEnd_1170291 := by
    simpa [prefixWord, tailWord_1170291, baseEnd_1170291] using wordTrace_append hprefix tailTrace_1170291
  have hstable : (prefixWord ++ tailWord_1170291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170291).length < 2 ^ (prefixWord ++ tailWord_1170291).sum := by decide
  have hdescent : baseEnd_1170291 < baseStart_1170291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170417 : List Nat := [1, 2, 2, 2, 4, 2, 2, 3, 1, 3]
def baseStart_1170417 : Nat := 118140960795 + 1170417 * 2 ^ 59
def prefixEnd_1170417 : Nat := 4983230072969 + 3 ^ 40 * 1170417 * 2
def baseEnd_1170417 : Nat := 400657658128968314536571

theorem tailTrace_1170417 : CollatzResearch.WordTrace tailWord_1170417 prefixEnd_1170417 400657658128968314536571 := by
  unfold tailWord_1170417
  simp only [CollatzResearch.WordTrace]
  refine ⟨42688615000786575154549505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28459076667191050103033003 42688615000786575154549505)
  ·
    refine ⟨32016461250589931365912129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42688615000786575154549505 32016461250589931365912129)
    ·
      refine ⟨24012345937942448524434097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32016461250589931365912129 24012345937942448524434097)
      ·
        refine ⟨18009259453456836393325573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24012345937942448524434097 18009259453456836393325573)
        ·
          refine ⟨3376736147523156823748545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18009259453456836393325573 3376736147523156823748545)
          ·
            refine ⟨2532552110642367617811409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3376736147523156823748545 2532552110642367617811409)
            ·
              refine ⟨1899414082981775713358557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2532552110642367617811409 1899414082981775713358557)
              ·
                refine ⟨712280281118165892509459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1899414082981775713358557 712280281118165892509459)
                ·
                  refine ⟨1068420421677248838764189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712280281118165892509459 1068420421677248838764189)
                  ·
                    refine ⟨400657658128968314536571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1068420421677248838764189 400657658128968314536571)
                    ·
                      rfl

theorem cell22_1170417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 1, 3].length) (baseStart_1170417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170417 prefixEnd_1170417 := by exact prefixLift 1170417
  have htrace : WordTrace (prefixWord ++ tailWord_1170417) baseStart_1170417 baseEnd_1170417 := by
    simpa [prefixWord, tailWord_1170417, baseEnd_1170417] using wordTrace_append hprefix tailTrace_1170417
  have hstable : (prefixWord ++ tailWord_1170417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170417).length < 2 ^ (prefixWord ++ tailWord_1170417).sum := by decide
  have hdescent : baseEnd_1170417 < baseStart_1170417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170430 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 7]
def baseStart_1170430 : Nat := 118140960795 + 1170430 * 2 ^ 59
def prefixEnd_1170430 : Nat := 4983230072969 + 3 ^ 40 * 1170430 * 2
def baseEnd_1170430 : Nat := 133554036098213537987177

theorem tailTrace_1170430 : CollatzResearch.WordTrace tailWord_1170430 prefixEnd_1170430 133554036098213537987177 := by
  unfold tailWord_1170430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5336136143717434796846593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28459392766492985583181829 5336136143717434796846593)
  ·
    refine ⟨4002102107788076097634945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5336136143717434796846593 4002102107788076097634945)
    ·
      refine ⟨3001576580841057073226209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4002102107788076097634945 3001576580841057073226209)
      ·
        refine ⟨2251182435630792804919657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3001576580841057073226209 2251182435630792804919657)
        ·
          refine ⟨1688386826723094603689743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2251182435630792804919657 1688386826723094603689743)
          ·
            refine ⟨2532580240084641905534615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1688386826723094603689743 2532580240084641905534615)
            ·
              refine ⟨3798870360126962858301923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2532580240084641905534615 3798870360126962858301923)
              ·
                refine ⟨5698305540190444287452885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3798870360126962858301923 5698305540190444287452885)
                ·
                  refine ⟨133554036098213537987177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5698305540190444287452885 133554036098213537987177)
                  ·
                    rfl

theorem cell22_1170430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_1170430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170430 prefixEnd_1170430 := by exact prefixLift 1170430
  have htrace : WordTrace (prefixWord ++ tailWord_1170430) baseStart_1170430 baseEnd_1170430 := by
    simpa [prefixWord, tailWord_1170430, baseEnd_1170430] using wordTrace_append hprefix tailTrace_1170430
  have hstable : (prefixWord ++ tailWord_1170430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170430).length < 2 ^ (prefixWord ++ tailWord_1170430).sum := by decide
  have hdescent : baseEnd_1170430 < baseStart_1170430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170434 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_1170434 : Nat := 118140960795 + 1170434 * 2 ^ 59
def prefixEnd_1170434 : Nat := 4983230072969 + 3 ^ 40 * 1170434 * 2
def baseEnd_1170434 : Nat := 400663477576385936861519

theorem tailTrace_1170434 : CollatzResearch.WordTrace tailWord_1170434 prefixEnd_1170434 400663477576385936861519 := by
  unfold tailWord_1170434
  simp only [CollatzResearch.WordTrace]
  refine ⟨10672308760431246764479589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28459490027816658038612237 10672308760431246764479589)
  ·
    refine ⟨2001057892580858768339923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10672308760431246764479589 2001057892580858768339923)
    ·
      refine ⟨3001586838871288152509885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2001057892580858768339923 3001586838871288152509885)
      ·
        refine ⟨1125595064576733057191207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3001586838871288152509885 1125595064576733057191207)
        ·
          refine ⟨1688392596865099585786811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1125595064576733057191207 1688392596865099585786811)
          ·
            refine ⟨2532588895297649378680217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1688392596865099585786811 2532588895297649378680217)
            ·
              refine ⟨1899441671473237034010163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2532588895297649378680217 1899441671473237034010163)
              ·
                refine ⟨2849162507209855551015245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1899441671473237034010163 2849162507209855551015245)
                ·
                  refine ⟨1068435940203695831630717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2849162507209855551015245 1068435940203695831630717)
                  ·
                    refine ⟨400663477576385936861519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1068435940203695831630717 400663477576385936861519)
                    ·
                      rfl

theorem cell22_1170434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_1170434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170434 prefixEnd_1170434 := by exact prefixLift 1170434
  have htrace : WordTrace (prefixWord ++ tailWord_1170434) baseStart_1170434 baseEnd_1170434 := by
    simpa [prefixWord, tailWord_1170434, baseEnd_1170434] using wordTrace_append hprefix tailTrace_1170434
  have hstable : (prefixWord ++ tailWord_1170434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170434).length < 2 ^ (prefixWord ++ tailWord_1170434).sum := by decide
  have hdescent : baseEnd_1170434 < baseStart_1170434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170488 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 4, 4]
def baseStart_1170488 : Nat := 118140960795 + 1170488 * 2 ^ 59
def prefixEnd_1170488 : Nat := 4983230072969 + 3 ^ 40 * 1170488 * 2
def baseEnd_1170488 : Nat := 400681962879947796011353

theorem tailTrace_1170488 : CollatzResearch.WordTrace tailWord_1170488 prefixEnd_1170488 400681962879947796011353 := by
  unfold tailWord_1170488
  simp only [CollatzResearch.WordTrace]
  refine ⟨21345602291764677140192059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28460803055686236186922745 21345602291764677140192059)
  ·
    refine ⟨32018403437647015710288089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21345602291764677140192059 32018403437647015710288089)
    ·
      refine ⟨24013802578235261782716067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32018403437647015710288089 24013802578235261782716067)
      ·
        refine ⟨36020703867352892674074101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24013802578235261782716067 36020703867352892674074101)
        ·
          refine ⟨3376940987564333688194447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36020703867352892674074101 3376940987564333688194447)
          ·
            refine ⟨5065411481346500532291671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3376940987564333688194447 5065411481346500532291671)
            ·
              refine ⟨7598117222019750798437507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5065411481346500532291671 7598117222019750798437507)
              ·
                refine ⟨11397175833029626197656261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7598117222019750798437507 11397175833029626197656261)
                ·
                  refine ⟨2136970468693054912060549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11397175833029626197656261 2136970468693054912060549)
                  ·
                    refine ⟨400681962879947796011353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2136970468693054912060549 400681962879947796011353)
                    ·
                      rfl

theorem cell22_1170488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_1170488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170488 prefixEnd_1170488 := by exact prefixLift 1170488
  have htrace : WordTrace (prefixWord ++ tailWord_1170488) baseStart_1170488 baseEnd_1170488 := by
    simpa [prefixWord, tailWord_1170488, baseEnd_1170488] using wordTrace_append hprefix tailTrace_1170488
  have hstable : (prefixWord ++ tailWord_1170488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170488).length < 2 ^ (prefixWord ++ tailWord_1170488).sum := by decide
  have hdescent : baseEnd_1170488 < baseStart_1170488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170492 : List Nat := [2, 2, 2, 2, 2, 3, 3, 2, 4]
def baseStart_1170492 : Nat := 118140960795 + 1170492 * 2 ^ 59
def prefixEnd_1170492 : Nat := 4983230072969 + 3 ^ 40 * 1170492 * 2
def baseEnd_1170492 : Nat := 133561110720564372970447

theorem tailTrace_1170492 : CollatzResearch.WordTrace tailWord_1170492 prefixEnd_1170492 133561110720564372970447 := by
  unfold tailWord_1170492
  simp only [CollatzResearch.WordTrace]
  refine ⟨21345675237757431481764865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28460900317009908642353153 21345675237757431481764865)
  ·
    refine ⟨16009256428318073611323649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21345675237757431481764865 16009256428318073611323649)
    ·
      refine ⟨12006942321238555208492737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16009256428318073611323649 12006942321238555208492737)
      ·
        refine ⟨9005206740928916406369553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12006942321238555208492737 9005206740928916406369553)
        ·
          refine ⟨6753905055696687304777165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9005206740928916406369553 6753905055696687304777165)
          ·
            refine ⟨2532714395886257739291437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6753905055696687304777165 2532714395886257739291437)
            ·
              refine ⟨949767898457346652234289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2532714395886257739291437 949767898457346652234289)
              ·
                refine ⟨712325923843009989175717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 949767898457346652234289 712325923843009989175717)
                ·
                  refine ⟨133561110720564372970447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 712325923843009989175717 133561110720564372970447)
                  ·
                    rfl

theorem cell22_1170492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_1170492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170492 prefixEnd_1170492 := by exact prefixLift 1170492
  have htrace : WordTrace (prefixWord ++ tailWord_1170492) baseStart_1170492 baseEnd_1170492 := by
    simpa [prefixWord, tailWord_1170492, baseEnd_1170492] using wordTrace_append hprefix tailTrace_1170492
  have hstable : (prefixWord ++ tailWord_1170492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170492).length < 2 ^ (prefixWord ++ tailWord_1170492).sum := by decide
  have hdescent : baseEnd_1170492 < baseStart_1170492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170503 : List Nat := [1, 1, 4, 1, 3, 3, 2, 7]
def baseStart_1170503 : Nat := 118140960795 + 1170503 * 2 ^ 59
def prefixEnd_1170503 : Nat := 4983230072969 + 3 ^ 40 * 1170503 * 2
def baseEnd_1170503 : Nat := 44520788631832528542923

theorem tailTrace_1170503 : CollatzResearch.WordTrace tailWord_1170503 prefixEnd_1170503 44520788631832528542923 := by
  unfold tailWord_1170503
  simp only [CollatzResearch.WordTrace]
  refine ⟨42691751678475011842180163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28461167785650007894786775 42691751678475011842180163)
  ·
    refine ⟨64037627517712517763270245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42691751678475011842180163 64037627517712517763270245)
    ·
      refine ⟨12007055159571097080613171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64037627517712517763270245 12007055159571097080613171)
      ·
        refine ⟨18010582739356645620919757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12007055159571097080613171 18010582739356645620919757)
        ·
          refine ⟨6753968527258742107844909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18010582739356645620919757 6753968527258742107844909)
          ·
            refine ⟨2532738197722028290441841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6753968527258742107844909 2532738197722028290441841)
            ·
              refine ⟨1899553648291521217831381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2532738197722028290441841 1899553648291521217831381)
              ·
                refine ⟨44520788631832528542923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1899553648291521217831381 44520788631832528542923)
                ·
                  rfl

theorem cell22_1170503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 7].length) (baseStart_1170503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170503 prefixEnd_1170503 := by exact prefixLift 1170503
  have htrace : WordTrace (prefixWord ++ tailWord_1170503) baseStart_1170503 baseEnd_1170503 := by
    simpa [prefixWord, tailWord_1170503, baseEnd_1170503] using wordTrace_append hprefix tailTrace_1170503
  have hstable : (prefixWord ++ tailWord_1170503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170503).length < 2 ^ (prefixWord ++ tailWord_1170503).sum := by decide
  have hdescent : baseEnd_1170503 < baseStart_1170503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170563 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 2, 5]
def baseStart_1170563 : Nat := 118140960795 + 1170563 * 2 ^ 59
def prefixEnd_1170563 : Nat := 4983230072969 + 3 ^ 40 * 1170563 * 2
def baseEnd_1170563 : Nat := 400707636912672600386123

theorem tailTrace_1170563 : CollatzResearch.WordTrace tailWord_1170563 prefixEnd_1170563 400707636912672600386123 := by
  unfold tailWord_1170563
  simp only [CollatzResearch.WordTrace]
  refine ⟨42693940058257642089364343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28462626705505094726242895 42693940058257642089364343)
  ·
    refine ⟨64040910087386463134046515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42693940058257642089364343 64040910087386463134046515)
    ·
      refine ⟨96061365131079694701069773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64040910087386463134046515 96061365131079694701069773)
      ·
        refine ⟨36023011924154885512901165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96061365131079694701069773 36023011924154885512901165)
        ·
          refine ⟨13508629471558082067337937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36023011924154885512901165 13508629471558082067337937)
          ·
            refine ⟨10131472103668561550503453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13508629471558082067337937 10131472103668561550503453)
            ·
              refine ⟨3799302038875710581438795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10131472103668561550503453 3799302038875710581438795)
              ·
                refine ⟨5698953058313565872158193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3799302038875710581438795 5698953058313565872158193)
                ·
                  refine ⟨4274214793735174404118645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5698953058313565872158193 4274214793735174404118645)
                  ·
                    refine ⟨400707636912672600386123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4274214793735174404118645 400707636912672600386123)
                    ·
                      rfl

theorem cell22_1170563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 5].length) (baseStart_1170563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170563 prefixEnd_1170563 := by exact prefixLift 1170563
  have htrace : WordTrace (prefixWord ++ tailWord_1170563) baseStart_1170563 baseEnd_1170563 := by
    simpa [prefixWord, tailWord_1170563, baseEnd_1170563] using wordTrace_append hprefix tailTrace_1170563
  have hstable : (prefixWord ++ tailWord_1170563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170563).length < 2 ^ (prefixWord ++ tailWord_1170563).sum := by decide
  have hdescent : baseEnd_1170563 < baseStart_1170563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170593 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 8]
def baseStart_1170593 : Nat := 118140960795 + 1170593 * 2 ^ 59
def prefixEnd_1170593 : Nat := 4983230072969 + 3 ^ 40 * 1170593 * 2
def baseEnd_1170593 : Nat := 133572635508587507378677

theorem tailTrace_1170593 : CollatzResearch.WordTrace tailWord_1170593 prefixEnd_1170593 133572635508587507378677 := by
  unfold tailWord_1170593
  simp only [CollatzResearch.WordTrace]
  refine ⟨42695034248148957212956433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28463356165432638141970955 42695034248148957212956433)
  ·
    refine ⟨32021275686111717909717325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42695034248148957212956433 32021275686111717909717325)
    ·
      refine ⟨12007978382291894216143997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32021275686111717909717325 12007978382291894216143997)
      ·
        refine ⟨4502991893359460331053999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12007978382291894216143997 4502991893359460331053999)
        ·
          refine ⟨6754487840039190496580999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4502991893359460331053999 6754487840039190496580999)
          ·
            refine ⟨10131731760058785744871499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6754487840039190496580999 10131731760058785744871499)
            ·
              refine ⟨15197597640088178617307249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10131731760058785744871499 15197597640088178617307249)
              ·
                refine ⟨11398198230066133962980437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15197597640088178617307249 11398198230066133962980437)
                ·
                  refine ⟨133572635508587507378677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11398198230066133962980437 133572635508587507378677)
                  ·
                    rfl

theorem cell22_1170593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 8].length) (baseStart_1170593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170593 prefixEnd_1170593 := by exact prefixLift 1170593
  have htrace : WordTrace (prefixWord ++ tailWord_1170593) baseStart_1170593 baseEnd_1170593 := by
    simpa [prefixWord, tailWord_1170593, baseEnd_1170593] using wordTrace_append hprefix tailTrace_1170593
  have hstable : (prefixWord ++ tailWord_1170593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170593).length < 2 ^ (prefixWord ++ tailWord_1170593).sum := by decide
  have hdescent : baseEnd_1170593 < baseStart_1170593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170610 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 6]
def baseStart_1170610 : Nat := 118140960795 + 1170610 * 2 ^ 59
def prefixEnd_1170610 : Nat := 4983230072969 + 3 ^ 40 * 1170610 * 2
def baseEnd_1170610 : Nat := 133574575324393381486993

theorem tailTrace_1170610 : CollatzResearch.WordTrace tailWord_1170610 prefixEnd_1170610 133574575324393381486993 := by
  unfold tailWord_1170610
  simp only [CollatzResearch.WordTrace]
  refine ⟨10673913572271842279081321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28463769526058246077550189 10673913572271842279081321)
  ·
    refine ⟨8005435179203881709310991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10673913572271842279081321 8005435179203881709310991)
    ·
      refine ⟨12008152768805822563966487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8005435179203881709310991 12008152768805822563966487)
      ·
        refine ⟨18012229153208733845949731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12008152768805822563966487 18012229153208733845949731)
        ·
          refine ⟨27018343729813100768924597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18012229153208733845949731 27018343729813100768924597)
          ·
            refine ⟨2532969724669978197086681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27018343729813100768924597 2532969724669978197086681)
            ·
              refine ⟨1899727293502483647815011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2532969724669978197086681 1899727293502483647815011)
              ·
                refine ⟨2849590940253725471722517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1899727293502483647815011 2849590940253725471722517)
                ·
                  refine ⟨133574575324393381486993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2849590940253725471722517 133574575324393381486993)
                  ·
                    rfl

theorem cell22_1170610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_1170610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170610 prefixEnd_1170610 := by exact prefixLift 1170610
  have htrace : WordTrace (prefixWord ++ tailWord_1170610) baseStart_1170610 baseEnd_1170610 := by
    simpa [prefixWord, tailWord_1170610, baseEnd_1170610] using wordTrace_append hprefix tailTrace_1170610
  have hstable : (prefixWord ++ tailWord_1170610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170610).length < 2 ^ (prefixWord ++ tailWord_1170610).sum := by decide
  have hdescent : baseEnd_1170610 < baseStart_1170610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170623 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 1, 6]
def baseStart_1170623 : Nat := 118140960795 + 1170623 * 2 ^ 59
def prefixEnd_1170623 : Nat := 4983230072969 + 3 ^ 40 * 1170623 * 2
def baseEnd_1170623 : Nat := 400728176138852443885939

theorem tailTrace_1170623 : CollatzResearch.WordTrace tailWord_1170623 prefixEnd_1170623 400728176138852443885939 := by
  unfold tailWord_1170623
  simp only [CollatzResearch.WordTrace]
  refine ⟨42696128438040272336548523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28464085625360181557699015 42696128438040272336548523)
  ·
    refine ⟨64044192657060408504822785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42696128438040272336548523 64044192657060408504822785)
    ·
      refine ⟨48033144492795306378617089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64044192657060408504822785 48033144492795306378617089)
      ·
        refine ⟨36024858369596479783962817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48033144492795306378617089 36024858369596479783962817)
        ·
          refine ⟨27018643777197359837972113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36024858369596479783962817 27018643777197359837972113)
          ·
            refine ⟨20263982832898019878479085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27018643777197359837972113 20263982832898019878479085)
            ·
              refine ⟨7598993562336757454429657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20263982832898019878479085 7598993562336757454429657)
              ·
                refine ⟨5699245171752568090822243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7598993562336757454429657 5699245171752568090822243)
                ·
                  refine ⟨8548867757628852136233365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5699245171752568090822243 8548867757628852136233365)
                  ·
                    refine ⟨400728176138852443885939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8548867757628852136233365 400728176138852443885939)
                    ·
                      rfl

theorem cell22_1170623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_1170623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170623 prefixEnd_1170623 := by exact prefixLift 1170623
  have htrace : WordTrace (prefixWord ++ tailWord_1170623) baseStart_1170623 baseEnd_1170623 := by
    simpa [prefixWord, tailWord_1170623, baseEnd_1170623] using wordTrace_append hprefix tailTrace_1170623
  have hstable : (prefixWord ++ tailWord_1170623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170623).length < 2 ^ (prefixWord ++ tailWord_1170623).sum := by decide
  have hdescent : baseEnd_1170623 < baseStart_1170623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170717 : List Nat := [1, 4, 2, 3, 1, 1, 1, 4, 5]
def baseStart_1170717 : Nat := 118140960795 + 1170717 * 2 ^ 59
def prefixEnd_1170717 : Nat := 4983230072969 + 3 ^ 40 * 1170717 * 2
def baseEnd_1170717 : Nat := 133586784753289177345217

theorem tailTrace_1170717 : CollatzResearch.WordTrace tailWord_1170717 prefixEnd_1170717 133586784753289177345217 := by
  unfold tailWord_1170717
  simp only [CollatzResearch.WordTrace]
  refine ⟨42699556899699726390470405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28466371266466484260313603 42699556899699726390470405)
  ·
    refine ⟨8006166918693698698213201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42699556899699726390470405 8006166918693698698213201)
    ·
      refine ⟨6004625189020274023659901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8006166918693698698213201 6004625189020274023659901)
      ·
        refine ⟨2251734445882602758872463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6004625189020274023659901 2251734445882602758872463)
        ·
          refine ⟨3377601668823904138308695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2251734445882602758872463 3377601668823904138308695)
          ·
            refine ⟨5066402503235856207463043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3377601668823904138308695 5066402503235856207463043)
            ·
              refine ⟨7599603754853784311194565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5066402503235856207463043 7599603754853784311194565)
              ·
                refine ⟨1424925704035084558348981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7599603754853784311194565 1424925704035084558348981)
                ·
                  refine ⟨133586784753289177345217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1424925704035084558348981 133586784753289177345217)
                  ·
                    rfl

theorem cell22_1170717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_1170717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170717 prefixEnd_1170717 := by exact prefixLift 1170717
  have htrace : WordTrace (prefixWord ++ tailWord_1170717) baseStart_1170717 baseEnd_1170717 := by
    simpa [prefixWord, tailWord_1170717, baseEnd_1170717] using wordTrace_append hprefix tailTrace_1170717
  have hstable : (prefixWord ++ tailWord_1170717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170717).length < 2 ^ (prefixWord ++ tailWord_1170717).sum := by decide
  have hdescent : baseEnd_1170717 < baseStart_1170717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170764 : List Nat := [2, 2, 1, 3, 2, 2, 4, 1, 1, 4]
def baseStart_1170764 : Nat := 118140960795 + 1170764 * 2 ^ 59
def prefixEnd_1170764 : Nat := 4983230072969 + 3 ^ 40 * 1170764 * 2
def baseEnd_1170764 : Nat := 400776443320375076110507

theorem tailTrace_1170764 : CollatzResearch.WordTrace tailWord_1170764 prefixEnd_1170764 400776443320375076110507 := by
  unfold tailWord_1170764
  simp only [CollatzResearch.WordTrace]
  refine ⟨21350635565264726708715673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28467514087019635611620897 21350635565264726708715673)
  ·
    refine ⟨16012976673948545031536755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21350635565264726708715673 16012976673948545031536755)
    ·
      refine ⟨24019465010922817547305133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16012976673948545031536755 24019465010922817547305133)
      ·
        refine ⟨9007299379096056580239425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24019465010922817547305133 9007299379096056580239425)
        ·
          refine ⟨6755474534322042435179569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9007299379096056580239425 6755474534322042435179569)
          ·
            refine ⟨5066605900741531826384677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6755474534322042435179569 5066605900741531826384677)
            ·
              refine ⟨949988606389037217447127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5066605900741531826384677 949988606389037217447127)
              ·
                refine ⟨1424982909583555826170691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 949988606389037217447127 1424982909583555826170691)
                ·
                  refine ⟨2137474364375333739256037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1424982909583555826170691 2137474364375333739256037)
                  ·
                    refine ⟨400776443320375076110507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2137474364375333739256037 400776443320375076110507)
                    ·
                      rfl

theorem cell22_1170764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_1170764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170764 prefixEnd_1170764 := by exact prefixLift 1170764
  have htrace : WordTrace (prefixWord ++ tailWord_1170764) baseStart_1170764 baseEnd_1170764 := by
    simpa [prefixWord, tailWord_1170764, baseEnd_1170764] using wordTrace_append hprefix tailTrace_1170764
  have hstable : (prefixWord ++ tailWord_1170764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170764).length < 2 ^ (prefixWord ++ tailWord_1170764).sum := by decide
  have hdescent : baseEnd_1170764 < baseStart_1170764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170933 : List Nat := [1, 3, 5, 1, 1, 1, 4, 1, 1, 4]
def baseStart_1170933 : Nat := 118140960795 + 1170933 * 2 ^ 59
def prefixEnd_1170933 : Nat := 4983230072969 + 3 ^ 40 * 1170933 * 2
def baseEnd_1170933 : Nat := 400834295474114968634989

theorem tailTrace_1170933 : CollatzResearch.WordTrace tailWord_1170933 prefixEnd_1170933 400834295474114968634989 := by
  unfold tailWord_1170933
  simp only [CollatzResearch.WordTrace]
  refine ⟨42707435066917195280333453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28471623377944796853555635 42707435066917195280333453)
  ·
    refine ⟨16015288150093948230125045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42707435066917195280333453 16015288150093948230125045)
    ·
      refine ⟨1501433264071307646574223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16015288150093948230125045 1501433264071307646574223)
      ·
        refine ⟨2252149896106961469861335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1501433264071307646574223 2252149896106961469861335)
        ·
          refine ⟨3378224844160442204792003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2252149896106961469861335 3378224844160442204792003)
          ·
            refine ⟨5067337266240663307188005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3378224844160442204792003 5067337266240663307188005)
            ·
              refine ⟨950125737420124370097751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5067337266240663307188005 950125737420124370097751)
              ·
                refine ⟨1425188606130186555146627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950125737420124370097751 1425188606130186555146627)
                ·
                  refine ⟨2137782909195279832719941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1425188606130186555146627 2137782909195279832719941)
                  ·
                    refine ⟨400834295474114968634989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2137782909195279832719941 400834295474114968634989)
                    ·
                      rfl

theorem cell22_1170933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_1170933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170933 prefixEnd_1170933 := by exact prefixLift 1170933
  have htrace : WordTrace (prefixWord ++ tailWord_1170933) baseStart_1170933 baseEnd_1170933 := by
    simpa [prefixWord, tailWord_1170933, baseEnd_1170933] using wordTrace_append hprefix tailTrace_1170933
  have hstable : (prefixWord ++ tailWord_1170933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170933).length < 2 ^ (prefixWord ++ tailWord_1170933).sum := by decide
  have hdescent : baseEnd_1170933 < baseStart_1170933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1170976 : List Nat := [2, 1, 1, 6, 1, 3, 2, 6]
def baseStart_1170976 : Nat := 118140960795 + 1170976 * 2 ^ 59
def prefixEnd_1170976 : Nat := 4983230072969 + 3 ^ 40 * 1170976 * 2
def baseEnd_1170976 : Nat := 44538779472541909978873

theorem tailTrace_1170976 : CollatzResearch.WordTrace tailWord_1170976 prefixEnd_1170976 44538779472541909978873 := by
  unfold tailWord_1170976
  simp only [CollatzResearch.WordTrace]
  refine ⟨21354501702880706812074391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28472668937174275749432521 21354501702880706812074391)
  ·
    refine ⟨32031752554321060218111587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21354501702880706812074391 32031752554321060218111587)
    ·
      refine ⟨48047628831481590327167381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32031752554321060218111587 48047628831481590327167381)
      ·
        refine ⟨2252232601475699546585971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48047628831481590327167381 2252232601475699546585971)
        ·
          refine ⟨3378348902213549319878957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2252232601475699546585971 3378348902213549319878957)
          ·
            refine ⟨1266880838330080994954609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3378348902213549319878957 1266880838330080994954609)
            ·
              refine ⟨950160628747560746215957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1266880838330080994954609 950160628747560746215957)
              ·
                refine ⟨44538779472541909978873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 950160628747560746215957 44538779472541909978873)
                ·
                  rfl

theorem cell22_1170976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 6].length) (baseStart_1170976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1170976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1170976 prefixEnd_1170976 := by exact prefixLift 1170976
  have htrace : WordTrace (prefixWord ++ tailWord_1170976) baseStart_1170976 baseEnd_1170976 := by
    simpa [prefixWord, tailWord_1170976, baseEnd_1170976] using wordTrace_append hprefix tailTrace_1170976
  have hstable : (prefixWord ++ tailWord_1170976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1170976).length < 2 ^ (prefixWord ++ tailWord_1170976).sum := by decide
  have hdescent : baseEnd_1170976 < baseStart_1170976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1170976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171014 : List Nat := [6, 1, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_1171014 : Nat := 118140960795 + 1171014 * 2 ^ 59
def prefixEnd_1171014 : Nat := 4983230072969 + 3 ^ 40 * 1171014 * 2
def baseEnd_1171014 : Nat := 400862023429457757359741

theorem tailTrace_1171014 : CollatzResearch.WordTrace tailWord_1171014 prefixEnd_1171014 400862023429457757359741 := by
  unfold tailWord_1171014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1334699668113242066063503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 28473592919749164076021397 1334699668113242066063503)
  ·
    refine ⟨2002049502169863099095255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1334699668113242066063503 2002049502169863099095255)
    ·
      refine ⟨3003074253254794648642883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2002049502169863099095255 3003074253254794648642883)
      ·
        refine ⟨4504611379882191972964325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3003074253254794648642883 4504611379882191972964325)
        ·
          refine ⟨844614633727910994930811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4504611379882191972964325 844614633727910994930811)
          ·
            refine ⟨1266921950591866492396217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844614633727910994930811 1266921950591866492396217)
            ·
              refine ⟨950191462943899869297163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1266921950591866492396217 950191462943899869297163)
              ·
                refine ⟨1425287194415849803945745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950191462943899869297163 1425287194415849803945745)
                ·
                  refine ⟨1068965395811887352959309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1425287194415849803945745 1068965395811887352959309)
                  ·
                    refine ⟨400862023429457757359741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1068965395811887352959309 400862023429457757359741)
                    ·
                      rfl

theorem cell22_1171014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_1171014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171014 prefixEnd_1171014 := by exact prefixLift 1171014
  have htrace : WordTrace (prefixWord ++ tailWord_1171014) baseStart_1171014 baseEnd_1171014 := by
    simpa [prefixWord, tailWord_1171014, baseEnd_1171014] using wordTrace_append hprefix tailTrace_1171014
  have hstable : (prefixWord ++ tailWord_1171014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171014).length < 2 ^ (prefixWord ++ tailWord_1171014).sum := by decide
  have hdescent : baseEnd_1171014 < baseStart_1171014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171032 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 8]
def baseStart_1171032 : Nat := 118140960795 + 1171032 * 2 ^ 59
def prefixEnd_1171032 : Nat := 4983230072969 + 3 ^ 40 * 1171032 * 2
def baseEnd_1171032 : Nat := 133622728399103903469895

theorem tailTrace_1171032 : CollatzResearch.WordTrace tailWord_1171032 prefixEnd_1171032 133622728399103903469895 := by
  unfold tailWord_1171032
  simp only [CollatzResearch.WordTrace]
  refine ⟨21355522946779267594093675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28474030595705690125458233 21355522946779267594093675)
  ·
    refine ⟨32033284420168901391140513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21355522946779267594093675 32033284420168901391140513)
    ·
      refine ⟨24024963315126676043355385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32033284420168901391140513 24024963315126676043355385)
      ·
        refine ⟨18018722486345007032516539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24024963315126676043355385 18018722486345007032516539)
        ·
          refine ⟨27028083729517510548774809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18018722486345007032516539 27028083729517510548774809)
          ·
            refine ⟨20271062797138132911581107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27028083729517510548774809 20271062797138132911581107)
            ·
              refine ⟨30406594195707199367371661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20271062797138132911581107 30406594195707199367371661)
              ·
                refine ⟨11402472823390199762764373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30406594195707199367371661 11402472823390199762764373)
                ·
                  refine ⟨133622728399103903469895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11402472823390199762764373 133622728399103903469895)
                  ·
                    rfl

theorem cell22_1171032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 8].length) (baseStart_1171032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171032 prefixEnd_1171032 := by exact prefixLift 1171032
  have htrace : WordTrace (prefixWord ++ tailWord_1171032) baseStart_1171032 baseEnd_1171032 := by
    simpa [prefixWord, tailWord_1171032, baseEnd_1171032] using wordTrace_append hprefix tailTrace_1171032
  have hstable : (prefixWord ++ tailWord_1171032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171032).length < 2 ^ (prefixWord ++ tailWord_1171032).sum := by decide
  have hdescent : baseEnd_1171032 < baseStart_1171032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171081 : List Nat := [1, 2, 1, 1, 4, 1, 4, 3, 2, 3]
def baseStart_1171081 : Nat := 118140960795 + 1171081 * 2 ^ 59
def prefixEnd_1171081 : Nat := 4983230072969 + 3 ^ 40 * 1171081 * 2
def baseEnd_1171081 : Nat := 400884958898691915934535

theorem tailTrace_1171081 : CollatzResearch.WordTrace tailWord_1171081 prefixEnd_1171081 400884958898691915934535 := by
  unfold tailWord_1171081
  simp only [CollatzResearch.WordTrace]
  refine ⟨42712833070381016556721097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28475222046920677704480731 42712833070381016556721097)
  ·
    refine ⟨32034624802785762417540823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42712833070381016556721097 32034624802785762417540823)
    ·
      refine ⟨48051937204178643626311235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32034624802785762417540823 48051937204178643626311235)
      ·
        refine ⟨72077905806267965439466853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48051937204178643626311235 72077905806267965439466853)
        ·
          refine ⟨13514607338675243519900035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72077905806267965439466853 13514607338675243519900035)
          ·
            refine ⟨20271911008012865279850053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13514607338675243519900035 20271911008012865279850053)
            ·
              refine ⟨3800983314002412239971885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20271911008012865279850053 3800983314002412239971885)
              ·
                refine ⟨1425368742750904589989457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3800983314002412239971885 1425368742750904589989457)
                ·
                  refine ⟨1069026557063178442492093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1425368742750904589989457 1069026557063178442492093)
                  ·
                    refine ⟨400884958898691915934535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1069026557063178442492093 400884958898691915934535)
                    ·
                      rfl

theorem cell22_1171081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 3].length) (baseStart_1171081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171081 prefixEnd_1171081 := by exact prefixLift 1171081
  have htrace : WordTrace (prefixWord ++ tailWord_1171081) baseStart_1171081 baseEnd_1171081 := by
    simpa [prefixWord, tailWord_1171081, baseEnd_1171081] using wordTrace_append hprefix tailTrace_1171081
  have hstable : (prefixWord ++ tailWord_1171081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171081).length < 2 ^ (prefixWord ++ tailWord_1171081).sum := by decide
  have hdescent : baseEnd_1171081 < baseStart_1171081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171096 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 2, 4]
def baseStart_1171096 : Nat := 118140960795 + 1171096 * 2 ^ 59
def prefixEnd_1171096 : Nat := 4983230072969 + 3 ^ 40 * 1171096 * 2
def baseEnd_1171096 : Nat := 400890093705236876809489

theorem tailTrace_1171096 : CollatzResearch.WordTrace tailWord_1171096 prefixEnd_1171096 400890093705236876809489 := by
  unfold tailWord_1171096
  simp only [CollatzResearch.WordTrace]
  refine ⟨21356690082663337059258571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28475586776884449412344761 21356690082663337059258571)
  ·
    refine ⟨32035035123995005588887857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21356690082663337059258571 32035035123995005588887857)
    ·
      refine ⟨24026276342996254191665893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32035035123995005588887857 24026276342996254191665893)
      ·
        refine ⟨4504926814311797660937355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24026276342996254191665893 4504926814311797660937355)
        ·
          refine ⟨6757390221467696491406033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4504926814311797660937355 6757390221467696491406033)
          ·
            refine ⟨5068042666100772368554525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6757390221467696491406033 5068042666100772368554525)
            ·
              refine ⟨1900515999787789638207947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5068042666100772368554525 1900515999787789638207947)
              ·
                refine ⟨2850773999681684457311921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1900515999787789638207947 2850773999681684457311921)
                ·
                  refine ⟨2138080499761263342983941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2850773999681684457311921 2138080499761263342983941)
                  ·
                    refine ⟨400890093705236876809489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2138080499761263342983941 400890093705236876809489)
                    ·
                      rfl

theorem cell22_1171096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_1171096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171096 prefixEnd_1171096 := by exact prefixLift 1171096
  have htrace : WordTrace (prefixWord ++ tailWord_1171096) baseStart_1171096 baseEnd_1171096 := by
    simpa [prefixWord, tailWord_1171096, baseEnd_1171096] using wordTrace_append hprefix tailTrace_1171096
  have hstable : (prefixWord ++ tailWord_1171096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171096).length < 2 ^ (prefixWord ++ tailWord_1171096).sum := by decide
  have hdescent : baseEnd_1171096 < baseStart_1171096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171156 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 7]
def baseStart_1171156 : Nat := 118140960795 + 1171156 * 2 ^ 59
def prefixEnd_1171156 : Nat := 4983230072969 + 3 ^ 40 * 1171156 * 2
def baseEnd_1171156 : Nat := 133636877643805573436435

theorem tailTrace_1171156 : CollatzResearch.WordTrace tailWord_1171156 prefixEnd_1171156 133636877643805573436435 := by
  unfold tailWord_1171156
  simp only [CollatzResearch.WordTrace]
  refine ⟨21357784272554652182850661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28477045696739536243800881 21357784272554652182850661)
  ·
    refine ⟨4004584551103997284284499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21357784272554652182850661 4004584551103997284284499)
    ·
      refine ⟨6006876826655995926426749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4004584551103997284284499 6006876826655995926426749)
      ·
        refine ⟨2252578809995998472410031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6006876826655995926426749 2252578809995998472410031)
        ·
          refine ⟨3378868214993997708615047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2252578809995998472410031 3378868214993997708615047)
          ·
            refine ⟨5068302322490996562922571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3378868214993997708615047 5068302322490996562922571)
            ·
              refine ⟨7602453483736494844383857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5068302322490996562922571 7602453483736494844383857)
              ·
                refine ⟨5701840112802371133287893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7602453483736494844383857 5701840112802371133287893)
                ·
                  refine ⟨133636877643805573436435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5701840112802371133287893 133636877643805573436435)
                  ·
                    rfl

theorem cell22_1171156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_1171156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171156 prefixEnd_1171156 := by exact prefixLift 1171156
  have htrace : WordTrace (prefixWord ++ tailWord_1171156) baseStart_1171156 baseEnd_1171156 := by
    simpa [prefixWord, tailWord_1171156, baseEnd_1171156] using wordTrace_append hprefix tailTrace_1171156
  have hstable : (prefixWord ++ tailWord_1171156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171156).length < 2 ^ (prefixWord ++ tailWord_1171156).sum := by decide
  have hdescent : baseEnd_1171156 < baseStart_1171156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171184 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 6]
def baseStart_1171184 : Nat := 118140960795 + 1171184 * 2 ^ 59
def prefixEnd_1171184 : Nat := 4983230072969 + 3 ^ 40 * 1171184 * 2
def baseEnd_1171184 : Nat := 133640072634544660203073

theorem tailTrace_1171184 : CollatzResearch.WordTrace tailWord_1171184 prefixEnd_1171184 133640072634544660203073 := by
  unfold tailWord_1171184
  simp only [CollatzResearch.WordTrace]
  refine ⟨21358294894503932573860303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28477726526005243431813737 21358294894503932573860303)
  ·
    refine ⟨32037442341755898860790455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21358294894503932573860303 32037442341755898860790455)
    ·
      refine ⟨48056163512633848291185683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32037442341755898860790455 48056163512633848291185683)
      ·
        refine ⟨72084245268950772436778525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48056163512633848291185683 72084245268950772436778525)
        ·
          refine ⟨27031591975856539663791947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72084245268950772436778525 27031591975856539663791947)
          ·
            refine ⟨40547387963784809495687921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27031591975856539663791947 40547387963784809495687921)
            ·
              refine ⟨30410540972838607121765941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40547387963784809495687921 30410540972838607121765941)
              ·
                refine ⟨2850988216203619417665557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30410540972838607121765941 2850988216203619417665557)
                ·
                  refine ⟨133640072634544660203073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2850988216203619417665557 133640072634544660203073)
                  ·
                    rfl

theorem cell22_1171184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 6].length) (baseStart_1171184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171184 prefixEnd_1171184 := by exact prefixLift 1171184
  have htrace : WordTrace (prefixWord ++ tailWord_1171184) baseStart_1171184 baseEnd_1171184 := by
    simpa [prefixWord, tailWord_1171184, baseEnd_1171184] using wordTrace_append hprefix tailTrace_1171184
  have hstable : (prefixWord ++ tailWord_1171184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171184).length < 2 ^ (prefixWord ++ tailWord_1171184).sum := by decide
  have hdescent : baseEnd_1171184 < baseStart_1171184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171186 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_1171186 : Nat := 118140960795 + 1171186 * 2 ^ 59
def prefixEnd_1171186 : Nat := 4983230072969 + 3 ^ 40 * 1171186 * 2
def baseEnd_1171186 : Nat := 400920902544506642059213

theorem tailTrace_1171186 : CollatzResearch.WordTrace tailWord_1171186 prefixEnd_1171186 400920902544506642059213 := by
  unfold tailWord_1171186
  simp only [CollatzResearch.WordTrace]
  refine ⟨10679165683750154872323353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28477775156667079659528941 10679165683750154872323353)
  ·
    refine ⟨8009374262812616154242515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10679165683750154872323353 8009374262812616154242515)
    ·
      refine ⟨12014061394218924231363773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8009374262812616154242515 12014061394218924231363773)
      ·
        refine ⟨4505273022832096586761415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12014061394218924231363773 4505273022832096586761415)
        ·
          refine ⟨6757909534248144880142123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4505273022832096586761415 6757909534248144880142123)
          ·
            refine ⟨10136864301372217320213185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6757909534248144880142123 10136864301372217320213185)
            ·
              refine ⟨7602648226029162990159889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10136864301372217320213185 7602648226029162990159889)
              ·
                refine ⟨5701986169521872242619917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7602648226029162990159889 5701986169521872242619917)
                ·
                  refine ⟨2138244813570702090982469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5701986169521872242619917 2138244813570702090982469)
                  ·
                    refine ⟨400920902544506642059213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2138244813570702090982469 400920902544506642059213)
                    ·
                      rfl

theorem cell22_1171186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_1171186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171186 prefixEnd_1171186 := by exact prefixLift 1171186
  have htrace : WordTrace (prefixWord ++ tailWord_1171186) baseStart_1171186 baseEnd_1171186 := by
    simpa [prefixWord, tailWord_1171186, baseEnd_1171186] using wordTrace_append hprefix tailTrace_1171186
  have hstable : (prefixWord ++ tailWord_1171186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171186).length < 2 ^ (prefixWord ++ tailWord_1171186).sum := by decide
  have hdescent : baseEnd_1171186 < baseStart_1171186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171190 : List Nat := [5, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_1171190 : Nat := 118140960795 + 1171190 * 2 ^ 59
def prefixEnd_1171190 : Nat := 4983230072969 + 3 ^ 40 * 1171190 * 2
def baseEnd_1171190 : Nat := 133640757275417321653067

theorem tailTrace_1171190 : CollatzResearch.WordTrace tailWord_1171190 prefixEnd_1171190 133640757275417321653067 := by
  unfold tailWord_1171190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2669800539186633010777439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28477872417990752114959349 2669800539186633010777439)
  ·
    refine ⟨4004700808779949516166159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2669800539186633010777439 4004700808779949516166159)
    ·
      refine ⟨6007051213169924274249239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4004700808779949516166159 6007051213169924274249239)
      ·
        refine ⟨9010576819754886411373859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6007051213169924274249239 9010576819754886411373859)
        ·
          refine ⟨13515865229632329617060789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9010576819754886411373859 13515865229632329617060789)
          ·
            refine ⟨1267112365278030901599449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13515865229632329617060789 1267112365278030901599449)
            ·
              refine ⟨950334273958523176199587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1267112365278030901599449 950334273958523176199587)
              ·
                refine ⟨1425501410937784764299381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950334273958523176199587 1425501410937784764299381)
                ·
                  refine ⟨133640757275417321653067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1425501410937784764299381 133640757275417321653067)
                  ·
                    rfl

theorem cell22_1171190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_1171190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171190 prefixEnd_1171190 := by exact prefixLift 1171190
  have htrace : WordTrace (prefixWord ++ tailWord_1171190) baseStart_1171190 baseEnd_1171190 := by
    simpa [prefixWord, tailWord_1171190, baseEnd_1171190] using wordTrace_append hprefix tailTrace_1171190
  have hstable : (prefixWord ++ tailWord_1171190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171190).length < 2 ^ (prefixWord ++ tailWord_1171190).sum := by decide
  have hdescent : baseEnd_1171190 < baseStart_1171190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171229 : List Nat := [1, 4, 2, 15]
def baseStart_1171229 : Nat := 118140960795 + 1171229 * 2 ^ 59
def prefixEnd_1171229 : Nat := 4983230072969 + 3 ^ 40 * 1171229 * 2
def baseEnd_1171229 : Nat := 549980277535348234889

theorem tailTrace_1171229 : CollatzResearch.WordTrace tailWord_1171229 prefixEnd_1171229 549980277535348234889 := by
  unfold tailWord_1171229
  simp only [CollatzResearch.WordTrace]
  refine ⟨42718231073844837833108741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28478820715896558555405827 42718231073844837833108741)
  ·
    refine ⟨8009668326345907093707889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42718231073844837833108741 8009668326345907093707889)
    ·
      refine ⟨6007251244759430320280917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8009668326345907093707889 6007251244759430320280917)
      ·
        refine ⟨549980277535348234889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 6007251244759430320280917 549980277535348234889)
        ·
          rfl

theorem cell22_1171229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 15].length) (baseStart_1171229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171229 prefixEnd_1171229 := by exact prefixLift 1171229
  have htrace : WordTrace (prefixWord ++ tailWord_1171229) baseStart_1171229 baseEnd_1171229 := by
    simpa [prefixWord, tailWord_1171229, baseEnd_1171229] using wordTrace_append hprefix tailTrace_1171229
  have hstable : (prefixWord ++ tailWord_1171229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171229).length < 2 ^ (prefixWord ++ tailWord_1171229).sum := by decide
  have hdescent : baseEnd_1171229 < baseStart_1171229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171231 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 2, 4]
def baseStart_1171231 : Nat := 118140960795 + 1171231 * 2 ^ 59
def prefixEnd_1171231 : Nat := 4983230072969 + 3 ^ 40 * 1171231 * 2
def baseEnd_1171231 : Nat := 400936306964141524684075

theorem tailTrace_1171231 : CollatzResearch.WordTrace tailWord_1171231 prefixEnd_1171231 400936306964141524684075 := by
  unfold tailWord_1171231
  simp only [CollatzResearch.WordTrace]
  refine ⟨42718304019837592174681547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28478869346558394783121031 42718304019837592174681547)
  ·
    refine ⟨64077456029756388262022321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42718304019837592174681547 64077456029756388262022321)
    ·
      refine ⟨48058092022317291196516741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64077456029756388262022321 48058092022317291196516741)
      ·
        refine ⟨9010892254184492099346889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48058092022317291196516741 9010892254184492099346889)
        ·
          refine ⟨6758169190638369074510167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9010892254184492099346889 6758169190638369074510167)
          ·
            refine ⟨10137253785957553611765251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6758169190638369074510167 10137253785957553611765251)
            ·
              refine ⟨15205880678936330417647877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10137253785957553611765251 15205880678936330417647877)
              ·
                refine ⟨2851102627300561953308977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15205880678936330417647877 2851102627300561953308977)
                ·
                  refine ⟨2138326970475421464981733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2851102627300561953308977 2138326970475421464981733)
                  ·
                    refine ⟨400936306964141524684075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2138326970475421464981733 400936306964141524684075)
                    ·
                      rfl

theorem cell22_1171231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_1171231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171231 prefixEnd_1171231 := by exact prefixLift 1171231
  have htrace : WordTrace (prefixWord ++ tailWord_1171231) baseStart_1171231 baseEnd_1171231 := by
    simpa [prefixWord, tailWord_1171231, baseEnd_1171231] using wordTrace_append hprefix tailTrace_1171231
  have hstable : (prefixWord ++ tailWord_1171231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171231).length < 2 ^ (prefixWord ++ tailWord_1171231).sum := by decide
  have hdescent : baseEnd_1171231 < baseStart_1171231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171233 : List Nat := [1, 2, 3, 2, 1, 3, 1, 4, 2, 3]
def baseStart_1171233 : Nat := 118140960795 + 1171233 * 2 ^ 59
def prefixEnd_1171233 : Nat := 4983230072969 + 3 ^ 40 * 1171233 * 2
def baseEnd_1171233 : Nat := 400936991605014186134069

theorem tailTrace_1171233 : CollatzResearch.WordTrace tailWord_1171233 prefixEnd_1171233 400936991605014186134069 := by
  unfold tailWord_1171233
  simp only [CollatzResearch.WordTrace]
  refine ⟨42718376965830346516254353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28478917977220231010836235 42718376965830346516254353)
  ·
    refine ⟨32038782724372759887190765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42718376965830346516254353 32038782724372759887190765)
    ·
      refine ⟨12014543521639784957696537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32038782724372759887190765 12014543521639784957696537)
      ·
        refine ⟨9010907641229838718272403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12014543521639784957696537 9010907641229838718272403)
        ·
          refine ⟨13516361461844758077408605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9010907641229838718272403 13516361461844758077408605)
          ·
            refine ⟨5068635548191784279028227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13516361461844758077408605 5068635548191784279028227)
            ·
              refine ⟨7602953322287676418542341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5068635548191784279028227 7602953322287676418542341)
              ·
                refine ⟨1425553747928939328476689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7602953322287676418542341 1425553747928939328476689)
                ·
                  refine ⟨1069165310946704496357517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1425553747928939328476689 1069165310946704496357517)
                  ·
                    refine ⟨400936991605014186134069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1069165310946704496357517 400936991605014186134069)
                    ·
                      rfl

theorem cell22_1171233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_1171233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171233 prefixEnd_1171233 := by exact prefixLift 1171233
  have htrace : WordTrace (prefixWord ++ tailWord_1171233) baseStart_1171233 baseEnd_1171233 := by
    simpa [prefixWord, tailWord_1171233, baseEnd_1171233] using wordTrace_append hprefix tailTrace_1171233
  have hstable : (prefixWord ++ tailWord_1171233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171233).length < 2 ^ (prefixWord ++ tailWord_1171233).sum := by decide
  have hdescent : baseEnd_1171233 < baseStart_1171233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171263 : List Nat := [1, 1, 2, 2, 6, 1, 3, 6]
def baseStart_1171263 : Nat := 118140960795 + 1171263 * 2 ^ 59
def prefixEnd_1171263 : Nat := 4983230072969 + 3 ^ 40 * 1171263 * 2
def baseEnd_1171263 : Nat := 44549695690900456431553

theorem tailTrace_1171263 : CollatzResearch.WordTrace tailWord_1171263 prefixEnd_1171263 44549695690900456431553 := by
  unfold tailWord_1171263
  simp only [CollatzResearch.WordTrace]
  refine ⟨42719471155721661639846443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28479647437147774426564295 42719471155721661639846443)
  ·
    refine ⟨64079206733582492459769665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42719471155721661639846443 64079206733582492459769665)
    ·
      refine ⟨48059405050186869344827249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64079206733582492459769665 48059405050186869344827249)
      ·
        refine ⟨36044553787640152008620437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48059405050186869344827249 36044553787640152008620437)
        ·
          refine ⟨1689588458795632125404083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36044553787640152008620437 1689588458795632125404083)
          ·
            refine ⟨2534382688193448188106125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1689588458795632125404083 2534382688193448188106125)
            ·
              refine ⟨950393508072543070539797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2534382688193448188106125 950393508072543070539797)
              ·
                refine ⟨44549695690900456431553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 950393508072543070539797 44549695690900456431553)
                ·
                  rfl

theorem cell22_1171263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 6].length) (baseStart_1171263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171263 prefixEnd_1171263 := by exact prefixLift 1171263
  have htrace : WordTrace (prefixWord ++ tailWord_1171263) baseStart_1171263 baseEnd_1171263 := by
    simpa [prefixWord, tailWord_1171263, baseEnd_1171263] using wordTrace_append hprefix tailTrace_1171263
  have hstable : (prefixWord ++ tailWord_1171263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171263).length < 2 ^ (prefixWord ++ tailWord_1171263).sum := by decide
  have hdescent : baseEnd_1171263 < baseStart_1171263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171295 : List Nat := [1, 1, 2, 3, 1, 4, 2, 4, 1, 3]
def baseStart_1171295 : Nat := 118140960795 + 1171295 * 2 ^ 59
def prefixEnd_1171295 : Nat := 4983230072969 + 3 ^ 40 * 1171295 * 2
def baseEnd_1171295 : Nat := 400958215472066691083879

theorem tailTrace_1171295 : CollatzResearch.WordTrace tailWord_1171295 prefixEnd_1171295 400958215472066691083879 := by
  unfold tailWord_1171295
  simp only [CollatzResearch.WordTrace]
  refine ⟨42720638291605731105011339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28480425527737154070007559 42720638291605731105011339)
  ·
    refine ⟨64080957437408596657517009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42720638291605731105011339 64080957437408596657517009)
    ·
      refine ⟨48060718078056447493137757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64080957437408596657517009 48060718078056447493137757)
      ·
        refine ⟨18022769279271167809926659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48060718078056447493137757 18022769279271167809926659)
        ·
          refine ⟨27034153918906751714889989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18022769279271167809926659 27034153918906751714889989)
          ·
            refine ⟨5068903859795015946541873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27034153918906751714889989 5068903859795015946541873)
            ·
              refine ⟨3801677894846261959906405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5068903859795015946541873 3801677894846261959906405)
              ·
                refine ⟨712814605283674117482451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3801677894846261959906405 712814605283674117482451)
                ·
                  refine ⟨1069221907925511176223677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 712814605283674117482451 1069221907925511176223677)
                  ·
                    refine ⟨400958215472066691083879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1069221907925511176223677 400958215472066691083879)
                    ·
                      rfl

theorem cell22_1171295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 1, 3].length) (baseStart_1171295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171295 prefixEnd_1171295 := by exact prefixLift 1171295
  have htrace : WordTrace (prefixWord ++ tailWord_1171295) baseStart_1171295 baseEnd_1171295 := by
    simpa [prefixWord, tailWord_1171295, baseEnd_1171295] using wordTrace_append hprefix tailTrace_1171295
  have hstable : (prefixWord ++ tailWord_1171295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171295).length < 2 ^ (prefixWord ++ tailWord_1171295).sum := by decide
  have hdescent : baseEnd_1171295 < baseStart_1171295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171353 : List Nat := [1, 2, 1, 2, 1, 3, 2, 6, 4]
def baseStart_1171353 : Nat := 118140960795 + 1171353 * 2 ^ 59
def prefixEnd_1171353 : Nat := 4983230072969 + 3 ^ 40 * 1171353 * 2
def baseEnd_1171353 : Nat := 133659356685791291044567

theorem tailTrace_1171353 : CollatzResearch.WordTrace tailWord_1171353 prefixEnd_1171353 133659356685791291044567 := by
  unfold tailWord_1171353
  simp only [CollatzResearch.WordTrace]
  refine ⟨42722753725395607010622713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28481835816930404673748475 42722753725395607010622713)
  ·
    refine ⟨32042065294046705257967035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42722753725395607010622713 32042065294046705257967035)
    ·
      refine ⟨48063097941070057886950553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32042065294046705257967035 48063097941070057886950553)
      ·
        refine ⟨36047323455802543415212915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48063097941070057886950553 36047323455802543415212915)
        ·
          refine ⟨54070985183703815122819373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36047323455802543415212915 54070985183703815122819373)
          ·
            refine ⟨20276619443888930671057265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54070985183703815122819373 20276619443888930671057265)
            ·
              refine ⟨15207464582916698003292949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20276619443888930671057265 15207464582916698003292949)
              ·
                refine ⟨712849902324220218904357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15207464582916698003292949 712849902324220218904357)
                ·
                  refine ⟨133659356685791291044567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 712849902324220218904357 133659356685791291044567)
                  ·
                    rfl

theorem cell22_1171353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 4].length) (baseStart_1171353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171353 prefixEnd_1171353 := by exact prefixLift 1171353
  have htrace : WordTrace (prefixWord ++ tailWord_1171353) baseStart_1171353 baseEnd_1171353 := by
    simpa [prefixWord, tailWord_1171353, baseEnd_1171353] using wordTrace_append hprefix tailTrace_1171353
  have hstable : (prefixWord ++ tailWord_1171353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171353).length < 2 ^ (prefixWord ++ tailWord_1171353).sum := by decide
  have hdescent : baseEnd_1171353 < baseStart_1171353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171477 : List Nat := [1, 3, 2, 1, 5, 1, 3, 1, 5]
def baseStart_1171477 : Nat := 118140960795 + 1171477 * 2 ^ 59
def prefixEnd_1171477 : Nat := 4983230072969 + 3 ^ 40 * 1171477 * 2
def baseEnd_1171477 : Nat := 133673505930492961011107

theorem tailTrace_1171477 : CollatzResearch.WordTrace tailWord_1171477 prefixEnd_1171477 133673505930492961011107 := by
  unfold tailWord_1171477
  simp only [CollatzResearch.WordTrace]
  refine ⟨42727276376946376188136685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28484850917964250792091123 42727276376946376188136685)
  ·
    refine ⟨16022728641354891070551257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42727276376946376188136685 16022728641354891070551257)
    ·
      refine ⟨12017046481016168302913443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16022728641354891070551257 12017046481016168302913443)
      ·
        refine ⟨18025569721524252454370165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12017046481016168302913443 18025569721524252454370165)
        ·
          refine ⟨1689897161392898667597203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18025569721524252454370165 1689897161392898667597203)
          ·
            refine ⟨2534845742089348001395805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1689897161392898667597203 2534845742089348001395805)
            ·
              refine ⟨950567153283505500523427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2534845742089348001395805 950567153283505500523427)
              ·
                refine ⟨1425850729925258250785141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950567153283505500523427 1425850729925258250785141)
                ·
                  refine ⟨133673505930492961011107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1425850729925258250785141 133673505930492961011107)
                  ·
                    rfl

theorem cell22_1171477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_1171477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171477 prefixEnd_1171477 := by exact prefixLift 1171477
  have htrace : WordTrace (prefixWord ++ tailWord_1171477) baseStart_1171477 baseEnd_1171477 := by
    simpa [prefixWord, tailWord_1171477, baseEnd_1171477] using wordTrace_append hprefix tailTrace_1171477
  have hstable : (prefixWord ++ tailWord_1171477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171477).length < 2 ^ (prefixWord ++ tailWord_1171477).sum := by decide
  have hdescent : baseEnd_1171477 < baseStart_1171477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171520 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 4, 3]
def baseStart_1171520 : Nat := 118140960795 + 1171520 * 2 ^ 59
def prefixEnd_1171520 : Nat := 4983230072969 + 3 ^ 40 * 1171520 * 2
def baseEnd_1171520 : Nat := 401035237570241104208189

theorem tailTrace_1171520 : CollatzResearch.WordTrace tailWord_1171520 prefixEnd_1171520 401035237570241104208189 := by
  unfold tailWord_1171520
  simp only [CollatzResearch.WordTrace]
  refine ⟨21364422357895297265976007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28485896477193729687968009 21364422357895297265976007)
  ·
    refine ⟨32046633536842945898964011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21364422357895297265976007 32046633536842945898964011)
    ·
      refine ⟨48069950305264418848446017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32046633536842945898964011 48069950305264418848446017)
      ·
        refine ⟨36052462728948314136334513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48069950305264418848446017 36052462728948314136334513)
        ·
          refine ⟨27039347046711235602250885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36052462728948314136334513 27039347046711235602250885)
          ·
            refine ⟨5069877571258356675422041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27039347046711235602250885 5069877571258356675422041)
            ·
              refine ⟨3802408178443767506566531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5069877571258356675422041 3802408178443767506566531)
              ·
                refine ⟨5703612267665651259849797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3802408178443767506566531 5703612267665651259849797)
                ·
                  refine ⟨1069427300187309611221837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5703612267665651259849797 1069427300187309611221837)
                  ·
                    refine ⟨401035237570241104208189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1069427300187309611221837 401035237570241104208189)
                    ·
                      rfl

theorem cell22_1171520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 4, 3].length) (baseStart_1171520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171520 prefixEnd_1171520 := by exact prefixLift 1171520
  have htrace : WordTrace (prefixWord ++ tailWord_1171520) baseStart_1171520 baseEnd_1171520 := by
    simpa [prefixWord, tailWord_1171520, baseEnd_1171520] using wordTrace_append hprefix tailTrace_1171520
  have hstable : (prefixWord ++ tailWord_1171520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171520).length < 2 ^ (prefixWord ++ tailWord_1171520).sum := by decide
  have hdescent : baseEnd_1171520 < baseStart_1171520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171629 : List Nat := [1, 5, 2, 1, 2, 3, 1, 2, 5]
def baseStart_1171629 : Nat := 118140960795 + 1171629 * 2 ^ 59
def prefixEnd_1171629 : Nat := 4983230072969 + 3 ^ 40 * 1171629 * 2
def baseEnd_1171629 : Nat := 133690850165933717744285

theorem tailTrace_1171629 : CollatzResearch.WordTrace tailWord_1171629 prefixEnd_1171629 133690850165933717744285 := by
  unfold tailWord_1171629
  simp only [CollatzResearch.WordTrace]
  refine ⟨42732820272395706147669941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28488546848263804098446627 42732820272395706147669941)
  ·
    refine ⟨4006201900537097451344057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42732820272395706147669941 4006201900537097451344057)
    ·
      refine ⟨3004651425402823088508043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4006201900537097451344057 3004651425402823088508043)
      ·
        refine ⟨4506977138104234632762065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3004651425402823088508043 4506977138104234632762065)
        ·
          refine ⟨3380232853578175974571549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4506977138104234632762065 3380232853578175974571549)
          ·
            refine ⟨1267587320091815990464331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3380232853578175974571549 1267587320091815990464331)
            ·
              refine ⟨1901380980137723985696497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267587320091815990464331 1901380980137723985696497)
              ·
                refine ⟨1426035735103292989272373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1901380980137723985696497 1426035735103292989272373)
                ·
                  refine ⟨133690850165933717744285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1426035735103292989272373 133690850165933717744285)
                  ·
                    rfl

theorem cell22_1171629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_1171629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171629 prefixEnd_1171629 := by exact prefixLift 1171629
  have htrace : WordTrace (prefixWord ++ tailWord_1171629) baseStart_1171629 baseEnd_1171629 := by
    simpa [prefixWord, tailWord_1171629, baseEnd_1171629] using wordTrace_append hprefix tailTrace_1171629
  have hstable : (prefixWord ++ tailWord_1171629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171629).length < 2 ^ (prefixWord ++ tailWord_1171629).sum := by decide
  have hdescent : baseEnd_1171629 < baseStart_1171629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171640 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 6]
def baseStart_1171640 : Nat := 118140960795 + 1171640 * 2 ^ 59
def prefixEnd_1171640 : Nat := 4983230072969 + 3 ^ 40 * 1171640 * 2
def baseEnd_1171640 : Nat := 133692105340866930402607

theorem tailTrace_1171640 : CollatzResearch.WordTrace tailWord_1171640 prefixEnd_1171640 133692105340866930402607 := by
  unfold tailWord_1171640
  simp only [CollatzResearch.WordTrace]
  refine ⟨21366610737677927513160187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28488814316903903350880249 21366610737677927513160187)
  ·
    refine ⟨32049916106516891269740281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21366610737677927513160187 32049916106516891269740281)
    ·
      refine ⟨24037437079887668452305211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32049916106516891269740281 24037437079887668452305211)
      ·
        refine ⟨36056155619831502678457817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24037437079887668452305211 36056155619831502678457817)
        ·
          refine ⟨27042116714873627008843363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36056155619831502678457817 27042116714873627008843363)
          ·
            refine ⟨40563175072310440513265045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27042116714873627008843363 40563175072310440513265045)
            ·
              refine ⟨1901398831514551899059299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40563175072310440513265045 1901398831514551899059299)
              ·
                refine ⟨2852098247271827848588949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1901398831514551899059299 2852098247271827848588949)
                ·
                  refine ⟨133692105340866930402607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2852098247271827848588949 133692105340866930402607)
                  ·
                    rfl

theorem cell22_1171640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 6].length) (baseStart_1171640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171640 prefixEnd_1171640 := by exact prefixLift 1171640
  have htrace : WordTrace (prefixWord ++ tailWord_1171640) baseStart_1171640 baseEnd_1171640 := by
    simpa [prefixWord, tailWord_1171640, baseEnd_1171640] using wordTrace_append hprefix tailTrace_1171640
  have hstable : (prefixWord ++ tailWord_1171640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171640).length < 2 ^ (prefixWord ++ tailWord_1171640).sum := by decide
  have hdescent : baseEnd_1171640 < baseStart_1171640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171672 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 4, 3]
def baseStart_1171672 : Nat := 118140960795 + 1171672 * 2 ^ 59
def prefixEnd_1171672 : Nat := 4983230072969 + 3 ^ 40 * 1171672 * 2
def baseEnd_1171672 : Nat := 401087270276563374407723

theorem tailTrace_1171672 : CollatzResearch.WordTrace tailWord_1171672 prefixEnd_1171672 401087270276563374407723 := by
  unfold tailWord_1171672
  simp only [CollatzResearch.WordTrace]
  refine ⟨21367194305619962245742635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28489592407493282994323513 21367194305619962245742635)
  ·
    refine ⟨32050791458429943368613953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21367194305619962245742635 32050791458429943368613953)
    ·
      refine ⟨24038093593822457526460465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32050791458429943368613953 24038093593822457526460465)
      ·
        refine ⟨18028570195366843144845349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24038093593822457526460465 18028570195366843144845349)
        ·
          refine ⟨3380356911631283089658503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18028570195366843144845349 3380356911631283089658503)
          ·
            refine ⟨5070535367446924634487755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3380356911631283089658503 5070535367446924634487755)
            ·
              refine ⟨7605803051170386951731633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5070535367446924634487755 7605803051170386951731633)
              ·
                refine ⟨5704352288377790213798725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7605803051170386951731633 5704352288377790213798725)
                ·
                  refine ⟨1069566054070835665087261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5704352288377790213798725 1069566054070835665087261)
                  ·
                    refine ⟨401087270276563374407723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1069566054070835665087261 401087270276563374407723)
                    ·
                      rfl

theorem cell22_1171672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_1171672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171672 prefixEnd_1171672 := by exact prefixLift 1171672
  have htrace : WordTrace (prefixWord ++ tailWord_1171672) baseStart_1171672 baseEnd_1171672 := by
    simpa [prefixWord, tailWord_1171672, baseEnd_1171672] using wordTrace_append hprefix tailTrace_1171672
  have hstable : (prefixWord ++ tailWord_1171672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171672).length < 2 ^ (prefixWord ++ tailWord_1171672).sum := by decide
  have hdescent : baseEnd_1171672 < baseStart_1171672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171685 : List Nat := [1, 3, 1, 4, 2, 1, 10]
def baseStart_1171685 : Nat := 118140960795 + 1171685 * 2 ^ 59
def prefixEnd_1171685 : Nat := 4983230072969 + 3 ^ 40 * 1171685 * 2
def baseEnd_1171685 : Nat := 14855248905267987919729

theorem tailTrace_1171685 : CollatzResearch.WordTrace tailWord_1171685 prefixEnd_1171685 14855248905267987919729 := by
  unfold tailWord_1171685
  simp only [CollatzResearch.WordTrace]
  refine ⟨42734862760192827711708509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28489908506795218474472339 42734862760192827711708509)
  ·
    refine ⟨16025573535072310391890691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42734862760192827711708509 16025573535072310391890691)
    ·
      refine ⟨24038360302608465587836037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16025573535072310391890691 24038360302608465587836037)
      ·
        refine ⟨4507192556739087297719257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24038360302608465587836037 4507192556739087297719257)
        ·
          refine ⟨3380394417554315473289443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4507192556739087297719257 3380394417554315473289443)
          ·
            refine ⟨5070591626331473209934165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3380394417554315473289443 5070591626331473209934165)
            ·
              refine ⟨14855248905267987919729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5070591626331473209934165 14855248905267987919729)
              ·
                rfl

theorem cell22_1171685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 10].length) (baseStart_1171685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171685 prefixEnd_1171685 := by exact prefixLift 1171685
  have htrace : WordTrace (prefixWord ++ tailWord_1171685) baseStart_1171685 baseEnd_1171685 := by
    simpa [prefixWord, tailWord_1171685, baseEnd_1171685] using wordTrace_append hprefix tailTrace_1171685
  have hstable : (prefixWord ++ tailWord_1171685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171685).length < 2 ^ (prefixWord ++ tailWord_1171685).sum := by decide
  have hdescent : baseEnd_1171685 < baseStart_1171685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171687 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 4, 4]
def baseStart_1171687 : Nat := 118140960795 + 1171687 * 2 ^ 59
def prefixEnd_1171687 : Nat := 4983230072969 + 3 ^ 40 * 1171687 * 2
def baseEnd_1171687 : Nat := 401092405083108335282677

theorem tailTrace_1171687 : CollatzResearch.WordTrace tailWord_1171687 prefixEnd_1171687 401092405083108335282677 := by
  unfold tailWord_1171687
  simp only [CollatzResearch.WordTrace]
  refine ⟨42734935706185582053281315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28489957137457054702187543 42734935706185582053281315)
  ·
    refine ⟨64102403559278373079921973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42734935706185582053281315 64102403559278373079921973)
    ·
      refine ⟨6009600333682347476242685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64102403559278373079921973 6009600333682347476242685)
      ·
        refine ⟨2253600125130880303591007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6009600333682347476242685 2253600125130880303591007)
        ·
          refine ⟨3380400187696320455386511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2253600125130880303591007 3380400187696320455386511)
          ·
            refine ⟨5070600281544480683079767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3380400187696320455386511 5070600281544480683079767)
            ·
              refine ⟨7605900422316721024619651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5070600281544480683079767 7605900422316721024619651)
              ·
                refine ⟨11408850633475081536929477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7605900422316721024619651 11408850633475081536929477)
                ·
                  refine ⟨2139159493776577788174277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11408850633475081536929477 2139159493776577788174277)
                  ·
                    refine ⟨401092405083108335282677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2139159493776577788174277 401092405083108335282677)
                    ·
                      rfl

theorem cell22_1171687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_1171687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171687 prefixEnd_1171687 := by exact prefixLift 1171687
  have htrace : WordTrace (prefixWord ++ tailWord_1171687) baseStart_1171687 baseEnd_1171687 := by
    simpa [prefixWord, tailWord_1171687, baseEnd_1171687] using wordTrace_append hprefix tailTrace_1171687
  have hstable : (prefixWord ++ tailWord_1171687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171687).length < 2 ^ (prefixWord ++ tailWord_1171687).sum := by decide
  have hdescent : baseEnd_1171687 < baseStart_1171687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171706 : List Nat := [3, 1, 1, 1, 1, 7, 2, 1, 2, 3]
def baseStart_1171706 : Nat := 118140960795 + 1171706 * 2 ^ 59
def prefixEnd_1171706 : Nat := 4983230072969 + 3 ^ 40 * 1171706 * 2
def baseEnd_1171706 : Nat := 401098909171398619057619

theorem tailTrace_1171706 : CollatzResearch.WordTrace tailWord_1171706 prefixEnd_1171706 401098909171398619057619 := by
  unfold tailWord_1171706
  simp only [CollatzResearch.WordTrace]
  refine ⟨10683907173279187074555743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28490419128744498865481981 10683907173279187074555743)
  ·
    refine ⟨16025860759918780611833615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10683907173279187074555743 16025860759918780611833615)
    ·
      refine ⟨24038791139878170917750423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16025860759918780611833615 24038791139878170917750423)
      ·
        refine ⟨36058186709817256376625635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24038791139878170917750423 36058186709817256376625635)
        ·
          refine ⟨54087280064725884564938453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36058186709817256376625635 54087280064725884564938453)
          ·
            refine ⟨1267670626517012919490745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 54087280064725884564938453 1267670626517012919490745)
            ·
              refine ⟨950752969887759689618059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1267670626517012919490745 950752969887759689618059)
              ·
                refine ⟨1426129454831639534427089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 950752969887759689618059 1426129454831639534427089)
                ·
                  refine ⟨1069597091123729650820317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1426129454831639534427089 1069597091123729650820317)
                  ·
                    refine ⟨401098909171398619057619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1069597091123729650820317 401098909171398619057619)
                    ·
                      rfl

theorem cell22_1171706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_1171706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171706 prefixEnd_1171706 := by exact prefixLift 1171706
  have htrace : WordTrace (prefixWord ++ tailWord_1171706) baseStart_1171706 baseEnd_1171706 := by
    simpa [prefixWord, tailWord_1171706, baseEnd_1171706] using wordTrace_append hprefix tailTrace_1171706
  have hstable : (prefixWord ++ tailWord_1171706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171706).length < 2 ^ (prefixWord ++ tailWord_1171706).sum := by decide
  have hdescent : baseEnd_1171706 < baseStart_1171706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171747 : List Nat := [1, 1, 1, 4, 2, 2, 4, 2, 5]
def baseStart_1171747 : Nat := 118140960795 + 1171747 * 2 ^ 59
def prefixEnd_1171747 : Nat := 4983230072969 + 3 ^ 40 * 1171747 * 2
def baseEnd_1171747 : Nat := 133704314769762726260831

theorem tailTrace_1171747 : CollatzResearch.WordTrace tailWord_1171747 prefixEnd_1171747 133704314769762726260831 := by
  unfold tailWord_1171747
  simp only [CollatzResearch.WordTrace]
  refine ⟨42737124085968212300465495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28491416057312141533643663 42737124085968212300465495)
  ·
    refine ⟨64105686128952318450698243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42737124085968212300465495 64105686128952318450698243)
    ·
      refine ⟨96158529193428477676047365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64105686128952318450698243 96158529193428477676047365)
      ·
        refine ⟨18029724223767839564258881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96158529193428477676047365 18029724223767839564258881)
        ·
          refine ⟨13522293167825879673194161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18029724223767839564258881 13522293167825879673194161)
          ·
            refine ⟨10141719875869409754895621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13522293167825879673194161 10141719875869409754895621)
            ·
              refine ⟨1901572476725514329042929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10141719875869409754895621 1901572476725514329042929)
              ·
                refine ⟨1426179357544135746782197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1901572476725514329042929 1426179357544135746782197)
                ·
                  refine ⟨133704314769762726260831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1426179357544135746782197 133704314769762726260831)
                  ·
                    rfl

theorem cell22_1171747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 5].length) (baseStart_1171747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171747 prefixEnd_1171747 := by exact prefixLift 1171747
  have htrace : WordTrace (prefixWord ++ tailWord_1171747) baseStart_1171747 baseEnd_1171747 := by
    simpa [prefixWord, tailWord_1171747, baseEnd_1171747] using wordTrace_append hprefix tailTrace_1171747
  have hstable : (prefixWord ++ tailWord_1171747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171747).length < 2 ^ (prefixWord ++ tailWord_1171747).sum := by decide
  have hdescent : baseEnd_1171747 < baseStart_1171747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171764 : List Nat := [2, 5, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1171764 : Nat := 118140960795 + 1171764 * 2 ^ 59
def prefixEnd_1171764 : Nat := 4983230072969 + 3 ^ 40 * 1171764 * 2
def baseEnd_1171764 : Nat := 133706254585568600369147

theorem tailTrace_1171764 : CollatzResearch.WordTrace tailWord_1171764 prefixEnd_1171764 133706254585568600369147 := by
  unfold tailWord_1171764
  simp only [CollatzResearch.WordTrace]
  refine ⟨21368872063453312101917173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28491829417937749469222897 21368872063453312101917173)
  ·
    refine ⟨2003331755948748009554735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21368872063453312101917173 2003331755948748009554735)
    ·
      refine ⟨3004997633923122014332103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2003331755948748009554735 3004997633923122014332103)
      ·
        refine ⟨4507496450884683021498155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3004997633923122014332103 4507496450884683021498155)
        ·
          refine ⟨6761244676327024532247233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4507496450884683021498155 6761244676327024532247233)
          ·
            refine ⟨5070933507245268399185425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6761244676327024532247233 5070933507245268399185425)
            ·
              refine ⟨3803200130433951299389069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5070933507245268399185425 3803200130433951299389069)
              ·
                refine ⟨1426200048912731737270901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3803200130433951299389069 1426200048912731737270901)
                ·
                  refine ⟨133706254585568600369147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1426200048912731737270901 133706254585568600369147)
                  ·
                    rfl

theorem cell22_1171764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1171764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171764 prefixEnd_1171764 := by exact prefixLift 1171764
  have htrace : WordTrace (prefixWord ++ tailWord_1171764) baseStart_1171764 baseEnd_1171764 := by
    simpa [prefixWord, tailWord_1171764, baseEnd_1171764] using wordTrace_append hprefix tailTrace_1171764
  have hstable : (prefixWord ++ tailWord_1171764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171764).length < 2 ^ (prefixWord ++ tailWord_1171764).sum := by decide
  have hdescent : baseEnd_1171764 < baseStart_1171764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1171824 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 1, 5]
def baseStart_1171824 : Nat := 118140960795 + 1171824 * 2 ^ 59
def prefixEnd_1171824 : Nat := 4983230072969 + 3 ^ 40 * 1171824 * 2
def baseEnd_1171824 : Nat := 401139302982885644607257

theorem tailTrace_1171824 : CollatzResearch.WordTrace tailWord_1171824 prefixEnd_1171824 401139302982885644607257 := by
  unfold tailWord_1171824
  simp only [CollatzResearch.WordTrace]
  refine ⟨21369966253344627225509263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28493288337792836300679017 21369966253344627225509263)
  ·
    refine ⟨32054949380016940838263895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21369966253344627225509263 32054949380016940838263895)
    ·
      refine ⟨48082424070025411257395843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32054949380016940838263895 48082424070025411257395843)
      ·
        refine ⟨72123636105038116886093765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48082424070025411257395843 72123636105038116886093765)
        ·
          refine ⟨13523181769694646916142581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72123636105038116886093765 13523181769694646916142581)
          ·
            refine ⟨1267798290908873148388367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13523181769694646916142581 1267798290908873148388367)
            ·
              refine ⟨1901697436363309722582551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267798290908873148388367 1901697436363309722582551)
              ·
                refine ⟨2852546154544964583873827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1901697436363309722582551 2852546154544964583873827)
                ·
                  refine ⟨4278819231817446875810741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2852546154544964583873827 4278819231817446875810741)
                  ·
                    refine ⟨401139302982885644607257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4278819231817446875810741 401139302982885644607257)
                    ·
                      rfl

theorem cell22_1171824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 1, 5].length) (baseStart_1171824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1171824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1171824 prefixEnd_1171824 := by exact prefixLift 1171824
  have htrace : WordTrace (prefixWord ++ tailWord_1171824) baseStart_1171824 baseEnd_1171824 := by
    simpa [prefixWord, tailWord_1171824, baseEnd_1171824] using wordTrace_append hprefix tailTrace_1171824
  have hstable : (prefixWord ++ tailWord_1171824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1171824).length < 2 ^ (prefixWord ++ tailWord_1171824).sum := by decide
  have hdescent : baseEnd_1171824 < baseStart_1171824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1171824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
