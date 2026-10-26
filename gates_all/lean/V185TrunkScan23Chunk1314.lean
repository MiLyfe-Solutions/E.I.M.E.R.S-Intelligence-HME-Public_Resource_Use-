import V185TrunkScan23Chunk1313

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7781951 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 3, 2, 2]
def baseStart_7781951 : Nat := 118140960795 + 7781951 * 2 ^ 59
def prefixEnd_7781951 : Nat := 4983230072969 + 3 ^ 40 * 7781951 * 2
def baseEnd_7781951 : Nat := 3995881292736587814623965

theorem tailTrace_7781951 : CollatzResearch.WordTrace tailWord_7781951 prefixEnd_7781951 3995881292736587814623965 := by
  unfold tailWord_7781951
  simp only [CollatzResearch.WordTrace]
  refine ⟨283831070630328053264721707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189220713753552035509814471 283831070630328053264721707)
  ·
    refine ⟨425746605945492079897082561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283831070630328053264721707 425746605945492079897082561)
    ·
      refine ⟨319309954459119059922811921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425746605945492079897082561 319309954459119059922811921)
      ·
        refine ⟨239482465844339294942108941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319309954459119059922811921 239482465844339294942108941)
        ·
          refine ⟨89805924691627235603290853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239482465844339294942108941 89805924691627235603290853)
          ·
            refine ⟨16838610879680106675617035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89805924691627235603290853 16838610879680106675617035)
            ·
              refine ⟨25257916319520160013425553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16838610879680106675617035 25257916319520160013425553)
              ·
                refine ⟨18943437239640120010069165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25257916319520160013425553 18943437239640120010069165)
                ·
                  refine ⟨7103788964865045003775937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18943437239640120010069165 7103788964865045003775937)
                  ·
                    refine ⟨5327841723648783752831953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7103788964865045003775937 5327841723648783752831953)
                    ·
                      refine ⟨3995881292736587814623965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5327841723648783752831953 3995881292736587814623965)
                      ·
                        rfl

theorem cell23_7781951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 2, 2].length) (baseStart_7781951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781951 prefixEnd_7781951 := by exact prefixLift 7781951
  have htrace : WordTrace (prefixWord ++ tailWord_7781951) baseStart_7781951 baseEnd_7781951 := by
    simpa [prefixWord, tailWord_7781951, baseEnd_7781951] using wordTrace_append hprefix tailTrace_7781951
  have hstable : (prefixWord ++ tailWord_7781951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781951).length < 2 ^ (prefixWord ++ tailWord_7781951).sum := by decide
  have hdescent : baseEnd_7781951 < baseStart_7781951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781957 : List Nat := [1, 3, 1, 1, 1, 4, 5, 7]
def baseStart_7781957 : Nat := 118140960795 + 7781957 * 2 ^ 59
def prefixEnd_7781957 : Nat := 4983230072969 + 3 ^ 40 * 7781957 * 2
def baseEnd_7781957 : Nat := 147995717541500547820331

theorem tailTrace_7781957 : CollatzResearch.WordTrace tailWord_7781957 prefixEnd_7781957 147995717541500547820331 := by
  unfold tailWord_7781957
  simp only [CollatzResearch.WordTrace]
  refine ⟨283831289468306316289440125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189220859645537544192960083 283831289468306316289440125)
  ·
    refine ⟨106436733550614868608540047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283831289468306316289440125 106436733550614868608540047)
    ·
      refine ⟨159655100325922302912810071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106436733550614868608540047 159655100325922302912810071)
      ·
        refine ⟨239482650488883454369215107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159655100325922302912810071 239482650488883454369215107)
        ·
          refine ⟨359223975733325181553822661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239482650488883454369215107 359223975733325181553822661)
          ·
            refine ⟨67354495449998471541341749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 359223975733325181553822661 67354495449998471541341749)
            ·
              refine ⟨6314483948437356707000789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67354495449998471541341749 6314483948437356707000789)
              ·
                refine ⟨147995717541500547820331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6314483948437356707000789 147995717541500547820331)
                ·
                  rfl

theorem cell23_7781957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 7].length) (baseStart_7781957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781957 prefixEnd_7781957 := by exact prefixLift 7781957
  have htrace : WordTrace (prefixWord ++ tailWord_7781957) baseStart_7781957 baseEnd_7781957 := by
    simpa [prefixWord, tailWord_7781957, baseEnd_7781957] using wordTrace_append hprefix tailTrace_7781957
  have hstable : (prefixWord ++ tailWord_7781957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781957).length < 2 ^ (prefixWord ++ tailWord_7781957).sum := by decide
  have hdescent : baseEnd_7781957 < baseStart_7781957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781965 : List Nat := [1, 6, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_7781965 : Nat := 118140960795 + 7781965 * 2 ^ 59
def prefixEnd_7781965 : Nat := 4983230072969 + 3 ^ 40 * 7781965 * 2
def baseEnd_7781965 : Nat := 1331962827155250253282967

theorem tailTrace_7781965 : CollatzResearch.WordTrace tailWord_7781965 prefixEnd_7781965 1331962827155250253282967 := by
  unfold tailWord_7781965
  simp only [CollatzResearch.WordTrace]
  refine ⟨283831581252277333655731349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189221054168184889103820899 283831581252277333655731349)
  ·
    refine ⟨13304605371200500015112407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 283831581252277333655731349 13304605371200500015112407)
    ·
      refine ⟨19956908056800750022668611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13304605371200500015112407 19956908056800750022668611)
      ·
        refine ⟨29935362085201125034002917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19956908056800750022668611 29935362085201125034002917)
        ·
          refine ⟨5612880390975210943875547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29935362085201125034002917 5612880390975210943875547)
          ·
            refine ⟨8419320586462816415813321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5612880390975210943875547 8419320586462816415813321)
            ·
              refine ⟨6314490439847112311859991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8419320586462816415813321 6314490439847112311859991)
              ·
                refine ⟨9471735659770668467789987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6314490439847112311859991 9471735659770668467789987)
                ·
                  refine ⟨14207603489656002701684981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9471735659770668467789987 14207603489656002701684981)
                  ·
                    refine ⟨1331962827155250253282967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14207603489656002701684981 1331962827155250253282967)
                    ·
                      rfl

theorem cell23_7781965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_7781965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781965 prefixEnd_7781965 := by exact prefixLift 7781965
  have htrace : WordTrace (prefixWord ++ tailWord_7781965) baseStart_7781965 baseEnd_7781965 := by
    simpa [prefixWord, tailWord_7781965, baseEnd_7781965] using wordTrace_append hprefix tailTrace_7781965
  have hstable : (prefixWord ++ tailWord_7781965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781965).length < 2 ^ (prefixWord ++ tailWord_7781965).sum := by decide
  have hdescent : baseEnd_7781965 < baseStart_7781965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781968 : List Nat := [2, 1, 1, 1, 1, 3, 6, 3, 1, 2, 2]
def baseStart_7781968 : Nat := 118140960795 + 7781968 * 2 ^ 59
def prefixEnd_7781968 : Nat := 4983230072969 + 3 ^ 40 * 7781968 * 2
def baseEnd_7781968 : Nat := 3995890021907714248111387

theorem tailTrace_7781968 : CollatzResearch.WordTrace tailWord_7781968 prefixEnd_7781968 3995890021907714248111387 := by
  unfold tailWord_7781968
  simp only [CollatzResearch.WordTrace]
  refine ⟨141915845335633232584045279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189221127114177643445393705 141915845335633232584045279)
  ·
    refine ⟨212873768003449848876067919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141915845335633232584045279 212873768003449848876067919)
    ·
      refine ⟨319310652005174773314101879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212873768003449848876067919 319310652005174773314101879)
      ·
        refine ⟨478965978007762159971152819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319310652005174773314101879 478965978007762159971152819)
        ·
          refine ⟨718448967011643239956729229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478965978007762159971152819 718448967011643239956729229)
          ·
            refine ⟨269418362629366214983773461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 718448967011643239956729229 269418362629366214983773461)
            ·
              refine ⟨12628985748251541327364381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 269418362629366214983773461 12628985748251541327364381)
              ·
                refine ⟨4735869655594327997761643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12628985748251541327364381 4735869655594327997761643)
                ·
                  refine ⟨7103804483391491996642465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4735869655594327997761643 7103804483391491996642465)
                  ·
                    refine ⟨5327853362543618997481849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7103804483391491996642465 5327853362543618997481849)
                    ·
                      refine ⟨3995890021907714248111387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5327853362543618997481849 3995890021907714248111387)
                      ·
                        rfl

theorem cell23_7781968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 1, 2, 2].length) (baseStart_7781968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781968 prefixEnd_7781968 := by exact prefixLift 7781968
  have htrace : WordTrace (prefixWord ++ tailWord_7781968) baseStart_7781968 baseEnd_7781968 := by
    simpa [prefixWord, tailWord_7781968, baseEnd_7781968] using wordTrace_append hprefix tailTrace_7781968
  have hstable : (prefixWord ++ tailWord_7781968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781968).length < 2 ^ (prefixWord ++ tailWord_7781968).sum := by decide
  have hdescent : baseEnd_7781968 < baseStart_7781968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7781998 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 1, 2, 4]
def baseStart_7781998 : Nat := 118140960795 + 7781998 * 2 ^ 59
def prefixEnd_7781998 : Nat := 4983230072969 + 3 ^ 40 * 7781998 * 2
def baseEnd_7781998 : Nat := 3995905426327349130736249

theorem tailTrace_7781998 : CollatzResearch.WordTrace tailWord_7781998 prefixEnd_7781998 3995905426327349130736249 := by
  unfold tailWord_7781998
  simp only [CollatzResearch.WordTrace]
  refine ⟨35479098107644722536460331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189221856574105186861121765 35479098107644722536460331)
  ·
    refine ⟨53218647161467083804690497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35479098107644722536460331 53218647161467083804690497)
    ·
      refine ⟨39913985371100312853517873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53218647161467083804690497 39913985371100312853517873)
      ·
        refine ⟨29935489028325234640138405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39913985371100312853517873 29935489028325234640138405)
        ·
          refine ⟨5612904192810981495025951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29935489028325234640138405 5612904192810981495025951)
          ·
            refine ⟨8419356289216472242538927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5612904192810981495025951 8419356289216472242538927)
            ·
              refine ⟨12629034433824708363808391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8419356289216472242538927 12629034433824708363808391)
              ·
                refine ⟨18943551650737062545712587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12629034433824708363808391 18943551650737062545712587)
                ·
                  refine ⟨28415327476105593818568881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18943551650737062545712587 28415327476105593818568881)
                  ·
                    refine ⟨21311495607079195363926661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28415327476105593818568881 21311495607079195363926661)
                    ·
                      refine ⟨3995905426327349130736249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21311495607079195363926661 3995905426327349130736249)
                      ·
                        rfl

theorem cell23_7781998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_7781998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7781998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7781998 prefixEnd_7781998 := by exact prefixLift 7781998
  have htrace : WordTrace (prefixWord ++ tailWord_7781998) baseStart_7781998 baseEnd_7781998 := by
    simpa [prefixWord, tailWord_7781998, baseEnd_7781998] using wordTrace_append hprefix tailTrace_7781998
  have hstable : (prefixWord ++ tailWord_7781998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7781998).length < 2 ^ (prefixWord ++ tailWord_7781998).sum := by decide
  have hdescent : baseEnd_7781998 < baseStart_7781998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7781998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782011 : List Nat := [1, 1, 1, 1, 1, 4, 6, 2, 1, 3, 2]
def baseStart_7782011 : Nat := 118140960795 + 7782011 * 2 ^ 59
def prefixEnd_7782011 : Nat := 4983230072969 + 3 ^ 40 * 7782011 * 2
def baseEnd_7782011 : Nat := 3995912101575857579873689

theorem tailTrace_7782011 : CollatzResearch.WordTrace tailWord_7782011 prefixEnd_7782011 3995912101575857579873689 := by
  unfold tailWord_7782011
  simp only [CollatzResearch.WordTrace]
  refine ⟨283833259010110683511905887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189222172673407122341270591 283833259010110683511905887)
  ·
    refine ⟨425749888515166025267858831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283833259010110683511905887 425749888515166025267858831)
    ·
      refine ⟨638624832772749037901788247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425749888515166025267858831 638624832772749037901788247)
      ·
        refine ⟨957937249159123556852682371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638624832772749037901788247 957937249159123556852682371)
        ·
          refine ⟨1436905873738685335279023557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957937249159123556852682371 1436905873738685335279023557)
          ·
            refine ⟨269419851326003500364816917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1436905873738685335279023557 269419851326003500364816917)
            ·
              refine ⟨12629055530906414079600793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 269419851326003500364816917 12629055530906414079600793)
              ·
                refine ⟨9471791648179810559700595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12629055530906414079600793 9471791648179810559700595)
                ·
                  refine ⟨14207687472269715839550893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9471791648179810559700595 14207687472269715839550893)
                  ·
                    refine ⟨5327882802101143439831585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14207687472269715839550893 5327882802101143439831585)
                    ·
                      refine ⟨3995912101575857579873689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5327882802101143439831585 3995912101575857579873689)
                      ·
                        rfl

theorem cell23_7782011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 3, 2].length) (baseStart_7782011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782011 prefixEnd_7782011 := by exact prefixLift 7782011
  have htrace : WordTrace (prefixWord ++ tailWord_7782011) baseStart_7782011 baseEnd_7782011 := by
    simpa [prefixWord, tailWord_7782011, baseEnd_7782011] using wordTrace_append hprefix tailTrace_7782011
  have hstable : (prefixWord ++ tailWord_7782011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782011).length < 2 ^ (prefixWord ++ tailWord_7782011).sum := by decide
  have hdescent : baseEnd_7782011 < baseStart_7782011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782027 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 5]
def baseStart_7782027 : Nat := 118140960795 + 7782027 * 2 ^ 59
def prefixEnd_7782027 : Nat := 4983230072969 + 3 ^ 40 * 7782027 * 2
def baseEnd_7782027 : Nat := 3995920317266329517273615

theorem tailTrace_7782027 : CollatzResearch.WordTrace tailWord_7782027 prefixEnd_7782027 3995920317266329517273615 := by
  unfold tailWord_7782027
  simp only [CollatzResearch.WordTrace]
  refine ⟨283833842578052718244488335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189222561718701812162992223 283833842578052718244488335)
  ·
    refine ⟨425750763867079077366732503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283833842578052718244488335 425750763867079077366732503)
    ·
      refine ⟨638626145800618616050098755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425750763867079077366732503 638626145800618616050098755)
      ·
        refine ⟨957939218700927924075148133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638626145800618616050098755 957939218700927924075148133)
        ·
          refine ⟨179613603506423985764090275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 957939218700927924075148133 179613603506423985764090275)
          ·
            refine ⟨269420405259635978646135413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179613603506423985764090275 269420405259635978646135413)
            ·
              refine ⟨25258162993090872998075195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269420405259635978646135413 25258162993090872998075195)
              ·
                refine ⟨37887244489636309497112793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25258162993090872998075195 37887244489636309497112793)
                ·
                  refine ⟨28415433367227232122834595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37887244489636309497112793 28415433367227232122834595)
                  ·
                    refine ⟨42623150050840848184251893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28415433367227232122834595 42623150050840848184251893)
                    ·
                      refine ⟨3995920317266329517273615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42623150050840848184251893 3995920317266329517273615)
                      ·
                        rfl

theorem cell23_7782027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 5].length) (baseStart_7782027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782027 prefixEnd_7782027 := by exact prefixLift 7782027
  have htrace : WordTrace (prefixWord ++ tailWord_7782027) baseStart_7782027 baseEnd_7782027 := by
    simpa [prefixWord, tailWord_7782027, baseEnd_7782027] using wordTrace_append hprefix tailTrace_7782027
  have hstable : (prefixWord ++ tailWord_7782027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782027).length < 2 ^ (prefixWord ++ tailWord_7782027).sum := by decide
  have hdescent : baseEnd_7782027 < baseStart_7782027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782037 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_7782037 : Nat := 118140960795 + 7782037 * 2 ^ 59
def prefixEnd_7782037 : Nat := 4983230072969 + 3 ^ 40 * 7782037 * 2
def baseEnd_7782037 : Nat := 3995925452072874478148569

theorem tailTrace_7782037 : CollatzResearch.WordTrace tailWord_7782037 prefixEnd_7782037 3995925452072874478148569 := by
  unfold tailWord_7782037
  simp only [CollatzResearch.WordTrace]
  refine ⟨283834207308016489952352365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189222804872010993301568243 283834207308016489952352365)
  ·
    refine ⟨106437827740506183732132137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283834207308016489952352365 106437827740506183732132137)
    ·
      refine ⟨79828370805379637799099103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106437827740506183732132137 79828370805379637799099103)
      ·
        refine ⟨119742556208069456698648655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79828370805379637799099103 119742556208069456698648655)
        ·
          refine ⟨179613834312104185047972983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119742556208069456698648655 179613834312104185047972983)
          ·
            refine ⟨269420751468156277571959475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179613834312104185047972983 269420751468156277571959475)
            ·
              refine ⟨404131127202234416357939213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269420751468156277571959475 404131127202234416357939213)
              ·
                refine ⟨151549172700837906134227205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404131127202234416357939213 151549172700837906134227205)
                ·
                  refine ⟨28415469881407107400167601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151549172700837906134227205 28415469881407107400167601)
                  ·
                    refine ⟨21311602411055330550125701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28415469881407107400167601 21311602411055330550125701)
                    ·
                      refine ⟨3995925452072874478148569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21311602411055330550125701 3995925452072874478148569)
                      ·
                        rfl

theorem cell23_7782037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_7782037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782037 prefixEnd_7782037 := by exact prefixLift 7782037
  have htrace : WordTrace (prefixWord ++ tailWord_7782037) baseStart_7782037 baseEnd_7782037 := by
    simpa [prefixWord, tailWord_7782037, baseEnd_7782037] using wordTrace_append hprefix tailTrace_7782037
  have hstable : (prefixWord ++ tailWord_7782037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782037).length < 2 ^ (prefixWord ++ tailWord_7782037).sum := by decide
  have hdescent : baseEnd_7782037 < baseStart_7782037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782062 : List Nat := [4, 1, 4, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_7782062 : Nat := 118140960795 + 7782062 * 2 ^ 59
def prefixEnd_7782062 : Nat := 4983230072969 + 3 ^ 40 * 7782062 * 2
def baseEnd_7782062 : Nat := 3995938289089236880335955

theorem tailTrace_7782062 : CollatzResearch.WordTrace tailWord_7782062 prefixEnd_7782062 3995938289089236880335955 := by
  unfold tailWord_7782062
  simp only [CollatzResearch.WordTrace]
  refine ⟨35479389891615739902751555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189223412755283946148008293 35479389891615739902751555)
  ·
    refine ⟨53219084837423609854127333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35479389891615739902751555 53219084837423609854127333)
    ·
      refine ⟨9978578407016926847648875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53219084837423609854127333 9978578407016926847648875)
      ·
        refine ⟨14967867610525390271473313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9978578407016926847648875 14967867610525390271473313)
        ·
          refine ⟨11225900707894042703604985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14967867610525390271473313 11225900707894042703604985)
          ·
            refine ⟨8419425530920532027703739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11225900707894042703604985 8419425530920532027703739)
            ·
              refine ⟨12629138296380798041555609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8419425530920532027703739 12629138296380798041555609)
              ·
                refine ⟨9471853722285598531166707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12629138296380798041555609 9471853722285598531166707)
                ·
                  refine ⟨14207780583428397796750061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9471853722285598531166707 14207780583428397796750061)
                  ·
                    refine ⟨5327917718785649173781273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14207780583428397796750061 5327917718785649173781273)
                    ·
                      refine ⟨3995938289089236880335955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5327917718785649173781273 3995938289089236880335955)
                      ·
                        rfl

theorem cell23_7782062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_7782062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782062 prefixEnd_7782062 := by exact prefixLift 7782062
  have htrace : WordTrace (prefixWord ++ tailWord_7782062) baseStart_7782062 baseEnd_7782062 := by
    simpa [prefixWord, tailWord_7782062, baseEnd_7782062] using wordTrace_append hprefix tailTrace_7782062
  have hstable : (prefixWord ++ tailWord_7782062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782062).length < 2 ^ (prefixWord ++ tailWord_7782062).sum := by decide
  have hdescent : baseEnd_7782062 < baseStart_7782062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782087 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_7782087 : Nat := 118140960795 + 7782087 * 2 ^ 59
def prefixEnd_7782087 : Nat := 4983230072969 + 3 ^ 40 * 7782087 * 2
def baseEnd_7782087 : Nat := 3995951126105599282523339

theorem tailTrace_7782087 : CollatzResearch.WordTrace tailWord_7782087 prefixEnd_7782087 3995951126105599282523339 := by
  unfold tailWord_7782087
  simp only [CollatzResearch.WordTrace]
  refine ⟨283836030957835348491672515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189224020638556898994448343 283836030957835348491672515)
  ·
    refine ⟨425754046436753022737508773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283836030957835348491672515 425754046436753022737508773)
    ·
      refine ⟨79828883706891191763282895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425754046436753022737508773 79828883706891191763282895)
      ·
        refine ⟨119743325560336787644924343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79828883706891191763282895 119743325560336787644924343)
        ·
          refine ⟨179614988340505181467386515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119743325560336787644924343 179614988340505181467386515)
          ·
            refine ⟨269422482510757772201079773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179614988340505181467386515 269422482510757772201079773)
            ·
              refine ⟨101033430941534164575404915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269422482510757772201079773 101033430941534164575404915)
              ·
                refine ⟨151550146412301246863107373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101033430941534164575404915 151550146412301246863107373)
                ·
                  refine ⟨56831304904612967573665265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151550146412301246863107373 56831304904612967573665265)
                  ·
                    refine ⟨42623478678459725680248949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56831304904612967573665265 42623478678459725680248949)
                    ·
                      refine ⟨3995951126105599282523339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42623478678459725680248949 3995951126105599282523339)
                      ·
                        rfl

theorem cell23_7782087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_7782087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782087 prefixEnd_7782087 := by exact prefixLift 7782087
  have htrace : WordTrace (prefixWord ++ tailWord_7782087) baseStart_7782087 baseEnd_7782087 := by
    simpa [prefixWord, tailWord_7782087, baseEnd_7782087] using wordTrace_append hprefix tailTrace_7782087
  have hstable : (prefixWord ++ tailWord_7782087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782087).length < 2 ^ (prefixWord ++ tailWord_7782087).sum := by decide
  have hdescent : baseEnd_7782087 < baseStart_7782087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782094 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 2, 5]
def baseStart_7782094 : Nat := 118140960795 + 7782094 * 2 ^ 59
def prefixEnd_7782094 : Nat := 4983230072969 + 3 ^ 40 * 7782094 * 2
def baseEnd_7782094 : Nat := 1331984906823393585045269

theorem tailTrace_7782094 : CollatzResearch.WordTrace tailWord_7782094 prefixEnd_7782094 1331984906823393585045269 := by
  unfold tailWord_7782094
  simp only [CollatzResearch.WordTrace]
  refine ⟨35479535783601248585897167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189224190845873325791451557 35479535783601248585897167)
  ·
    refine ⟨53219303675401872878845751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35479535783601248585897167 53219303675401872878845751)
    ·
      refine ⟨79828955513102809318268627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53219303675401872878845751 79828955513102809318268627)
      ·
        refine ⟨119743433269654213977402941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79828955513102809318268627 119743433269654213977402941)
        ·
          refine ⟨44903787476120330241526103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119743433269654213977402941 44903787476120330241526103)
          ·
            refine ⟨67355681214180495362289155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44903787476120330241526103 67355681214180495362289155)
            ·
              refine ⟨101033521821270743043433733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67355681214180495362289155 101033521821270743043433733)
              ·
                refine ⟨18943785341488264320643825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101033521821270743043433733 18943785341488264320643825)
                ·
                  refine ⟨14207839006116198240482869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18943785341488264320643825 14207839006116198240482869)
                  ·
                    refine ⟨1331984906823393585045269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14207839006116198240482869 1331984906823393585045269)
                    ·
                      rfl

theorem cell23_7782094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_7782094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782094 prefixEnd_7782094 := by exact prefixLift 7782094
  have htrace : WordTrace (prefixWord ++ tailWord_7782094) baseStart_7782094 baseEnd_7782094 := by
    simpa [prefixWord, tailWord_7782094, baseEnd_7782094] using wordTrace_append hprefix tailTrace_7782094
  have hstable : (prefixWord ++ tailWord_7782094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782094).length < 2 ^ (prefixWord ++ tailWord_7782094).sum := by decide
  have hdescent : baseEnd_7782094 < baseStart_7782094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782098 : List Nat := [3, 2, 2, 2, 2, 1, 4, 2, 5]
def baseStart_7782098 : Nat := 118140960795 + 7782098 * 2 ^ 59
def prefixEnd_7782098 : Nat := 4983230072969 + 3 ^ 40 * 7782098 * 2
def baseEnd_7782098 : Nat := 443995197154755415498421

theorem tailTrace_7782098 : CollatzResearch.WordTrace tailWord_7782098 prefixEnd_7782098 443995197154755415498421 := by
  unfold tailWord_7782098
  simp only [CollatzResearch.WordTrace]
  refine ⟨70959108040198874342580737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189224288107196998246881965 70959108040198874342580737)
  ·
    refine ⟨53219331030149155756935553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70959108040198874342580737 53219331030149155756935553)
    ·
      refine ⟨39914498272611866817701665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53219331030149155756935553 39914498272611866817701665)
      ·
        refine ⟨29935873704458900113276249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39914498272611866817701665 29935873704458900113276249)
        ·
          refine ⟨22451905278344175084957187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29935873704458900113276249 22451905278344175084957187)
          ·
            refine ⟨33677857917516262627435781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22451905278344175084957187 33677857917516262627435781)
            ·
              refine ⟨6314598359534299242644209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33677857917516262627435781 6314598359534299242644209)
              ·
                refine ⟨4735948769650724431983157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6314598359534299242644209 4735948769650724431983157)
                ·
                  refine ⟨443995197154755415498421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4735948769650724431983157 443995197154755415498421)
                  ·
                    rfl

theorem cell23_7782098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_7782098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782098 prefixEnd_7782098 := by exact prefixLift 7782098
  have htrace : WordTrace (prefixWord ++ tailWord_7782098) baseStart_7782098 baseEnd_7782098 := by
    simpa [prefixWord, tailWord_7782098, baseEnd_7782098] using wordTrace_append hprefix tailTrace_7782098
  have hstable : (prefixWord ++ tailWord_7782098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782098).length < 2 ^ (prefixWord ++ tailWord_7782098).sum := by decide
  have hdescent : baseEnd_7782098 < baseStart_7782098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782108 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_7782108 : Nat := 118140960795 + 7782108 * 2 ^ 59
def prefixEnd_7782108 : Nat := 4983230072969 + 3 ^ 40 * 7782108 * 2
def baseEnd_7782108 : Nat := 3995961909199343700360743

theorem tailTrace_7782108 : CollatzResearch.WordTrace tailWord_7782108 prefixEnd_7782108 3995961909199343700360743 := by
  unfold tailWord_7782108
  simp only [CollatzResearch.WordTrace]
  refine ⟨141918398445379634539093489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189224531260506179385457985 141918398445379634539093489)
  ·
    refine ⟨106438798834034725904320117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141918398445379634539093489 106438798834034725904320117)
    ·
      refine ⟨9978637390690755553530011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106438798834034725904320117 9978637390690755553530011)
      ·
        refine ⟨14967956086036133330295017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9978637390690755553530011 14967956086036133330295017)
        ·
          refine ⟨11225967064527099997721263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14967956086036133330295017 11225967064527099997721263)
          ·
            refine ⟨16838950596790649996581895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11225967064527099997721263 16838950596790649996581895)
            ·
              refine ⟨25258425895185974994872843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16838950596790649996581895 25258425895185974994872843)
              ·
                refine ⟨37887638842778962492309265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25258425895185974994872843 37887638842778962492309265)
                ·
                  refine ⟨28415729132084221869231949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37887638842778962492309265 28415729132084221869231949)
                  ·
                    refine ⟨10655898424531583200961981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28415729132084221869231949 10655898424531583200961981)
                    ·
                      refine ⟨3995961909199343700360743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10655898424531583200961981 3995961909199343700360743)
                      ·
                        rfl

theorem cell23_7782108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_7782108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782108 prefixEnd_7782108 := by exact prefixLift 7782108
  have htrace : WordTrace (prefixWord ++ tailWord_7782108) baseStart_7782108 baseEnd_7782108 := by
    simpa [prefixWord, tailWord_7782108, baseEnd_7782108] using wordTrace_append hprefix tailTrace_7782108
  have hstable : (prefixWord ++ tailWord_7782108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782108).length < 2 ^ (prefixWord ++ tailWord_7782108).sum := by decide
  have hdescent : baseEnd_7782108 < baseStart_7782108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782124 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 5, 4]
def baseStart_7782124 : Nat := 118140960795 + 7782124 * 2 ^ 59
def prefixEnd_7782124 : Nat := 4983230072969 + 3 ^ 40 * 7782124 * 2
def baseEnd_7782124 : Nat := 1331990041629938545920223

theorem tailTrace_7782124 : CollatzResearch.WordTrace tailWord_7782124 prefixEnd_7782124 1331990041629938545920223 := by
  unfold tailWord_7782124
  simp only [CollatzResearch.WordTrace]
  refine ⟨141918690229350651905384713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189224920305800869207179617 141918690229350651905384713)
  ·
    refine ⟨106439017672012988929038535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141918690229350651905384713 106439017672012988929038535)
    ·
      refine ⟨159658526508019483393557803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106439017672012988929038535 159658526508019483393557803)
      ·
        refine ⟨239487789762029225090336705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159658526508019483393557803 239487789762029225090336705)
        ·
          refine ⟨179615842321521918817752529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239487789762029225090336705 179615842321521918817752529)
          ·
            refine ⟨134711881741141439113314397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179615842321521918817752529 134711881741141439113314397)
            ·
              refine ⟨50516955652928039667492899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134711881741141439113314397 50516955652928039667492899)
              ·
                refine ⟨75775433479392059501239349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50516955652928039667492899 75775433479392059501239349)
                ·
                  refine ⟨7103946888693005578241189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75775433479392059501239349 7103946888693005578241189)
                  ·
                    refine ⟨1331990041629938545920223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7103946888693005578241189 1331990041629938545920223)
                    ·
                      rfl

theorem cell23_7782124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_7782124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782124 prefixEnd_7782124 := by exact prefixLift 7782124
  have htrace : WordTrace (prefixWord ++ tailWord_7782124) baseStart_7782124 baseEnd_7782124 := by
    simpa [prefixWord, tailWord_7782124, baseEnd_7782124] using wordTrace_append hprefix tailTrace_7782124
  have hstable : (prefixWord ++ tailWord_7782124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782124).length < 2 ^ (prefixWord ++ tailWord_7782124).sum := by decide
  have hdescent : baseEnd_7782124 < baseStart_7782124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782154 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 8]
def baseStart_7782154 : Nat := 118140960795 + 7782154 * 2 ^ 59
def prefixEnd_7782154 : Nat := 4983230072969 + 3 ^ 40 * 7782154 * 2
def baseEnd_7782154 : Nat := 443998392145494502265059

theorem tailTrace_7782154 : CollatzResearch.WordTrace tailWord_7782154 prefixEnd_7782154 443998392145494502265059 := by
  unfold tailWord_7782154
  simp only [CollatzResearch.WordTrace]
  refine ⟨70959618662148154733590379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189225649765728412622907677 70959618662148154733590379)
  ·
    refine ⟨106439427993222232100385569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70959618662148154733590379 106439427993222232100385569)
    ·
      refine ⟨79829570994916674075289177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106439427993222232100385569 79829570994916674075289177)
      ·
        refine ⟨59872178246187505556466883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79829570994916674075289177 59872178246187505556466883)
        ·
          refine ⟨89808267369281258334700325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59872178246187505556466883 89808267369281258334700325)
          ·
            refine ⟨16839050131740235937756311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89808267369281258334700325 16839050131740235937756311)
            ·
              refine ⟨25258575197610353906634467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16839050131740235937756311 25258575197610353906634467)
              ·
                refine ⟨37887862796415530859951701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25258575197610353906634467 37887862796415530859951701)
                ·
                  refine ⟨443998392145494502265059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37887862796415530859951701 443998392145494502265059)
                  ·
                    rfl

theorem cell23_7782154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 8].length) (baseStart_7782154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782154 prefixEnd_7782154 := by exact prefixLift 7782154
  have htrace : WordTrace (prefixWord ++ tailWord_7782154) baseStart_7782154 baseEnd_7782154 := by
    simpa [prefixWord, tailWord_7782154, baseEnd_7782154] using wordTrace_append hprefix tailTrace_7782154
  have hstable : (prefixWord ++ tailWord_7782154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782154).length < 2 ^ (prefixWord ++ tailWord_7782154).sum := by decide
  have hdescent : baseEnd_7782154 < baseStart_7782154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782158 : List Nat := [4, 1, 1, 2, 1, 1, 4, 4, 1, 4]
def baseStart_7782158 : Nat := 118140960795 + 7782158 * 2 ^ 59
def prefixEnd_7782158 : Nat := 4983230072969 + 3 ^ 40 * 7782158 * 2
def baseEnd_7782158 : Nat := 1331995861077356168245171

theorem tailTrace_7782158 : CollatzResearch.WordTrace tailWord_7782158 prefixEnd_7782158 1331995861077356168245171 := by
  unfold tailWord_7782158
  simp only [CollatzResearch.WordTrace]
  refine ⟨35479827567572265952188391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189225747027052085078338085 35479827567572265952188391)
  ·
    refine ⟨53219741351358398928282587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35479827567572265952188391 53219741351358398928282587)
    ·
      refine ⟨79829612027037598392423881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53219741351358398928282587 79829612027037598392423881)
      ·
        refine ⟨59872209020278198794317911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79829612027037598392423881 59872209020278198794317911)
        ·
          refine ⟨89808313530417298191476867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59872209020278198794317911 89808313530417298191476867)
          ·
            refine ⟨134712470295625947287215301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89808313530417298191476867 134712470295625947287215301)
            ·
              refine ⟨25258588180429865116352869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134712470295625947287215301 25258588180429865116352869)
              ·
                refine ⟨4735985283830599709316163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25258588180429865116352869 4735985283830599709316163)
                ·
                  refine ⟨7103977925745899563974245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4735985283830599709316163 7103977925745899563974245)
                  ·
                    refine ⟨1331995861077356168245171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7103977925745899563974245 1331995861077356168245171)
                    ·
                      rfl

theorem cell23_7782158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_7782158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782158 prefixEnd_7782158 := by exact prefixLift 7782158
  have htrace : WordTrace (prefixWord ++ tailWord_7782158) baseStart_7782158 baseEnd_7782158 := by
    simpa [prefixWord, tailWord_7782158, baseEnd_7782158] using wordTrace_append hprefix tailTrace_7782158
  have hstable : (prefixWord ++ tailWord_7782158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782158).length < 2 ^ (prefixWord ++ tailWord_7782158).sum := by decide
  have hdescent : baseEnd_7782158 < baseStart_7782158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782224 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 3]
def baseStart_7782224 : Nat := 118140960795 + 7782224 * 2 ^ 59
def prefixEnd_7782224 : Nat := 4983230072969 + 3 ^ 40 * 7782224 * 2
def baseEnd_7782224 : Nat := 3996021472955265246510209

theorem tailTrace_7782224 : CollatzResearch.WordTrace tailWord_7782224 prefixEnd_7782224 3996021472955265246510209 := by
  unfold tailWord_7782224
  simp only [CollatzResearch.WordTrace]
  refine ⟨141920513879169510444704863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189227351838892680592939817 141920513879169510444704863)
  ·
    refine ⟨212880770818754265667057295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141920513879169510444704863 212880770818754265667057295)
    ·
      refine ⟨319321156228131398500585943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212880770818754265667057295 319321156228131398500585943)
      ·
        refine ⟨478981734342197097750878915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319321156228131398500585943 478981734342197097750878915)
        ·
          refine ⟨718472601513295646626318373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478981734342197097750878915 718472601513295646626318373)
          ·
            refine ⟨134713612783742933742434695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 718472601513295646626318373 134713612783742933742434695)
            ·
              refine ⟨202070419175614400613652043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134713612783742933742434695 202070419175614400613652043)
              ·
                refine ⟨303105628763421600920478065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202070419175614400613652043 303105628763421600920478065)
                ·
                  refine ⟨227329221572566200690358549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303105628763421600920478065 227329221572566200690358549)
                  ·
                    refine ⟨10656057261214040657360557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 227329221572566200690358549 10656057261214040657360557)
                    ·
                      refine ⟨3996021472955265246510209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10656057261214040657360557 3996021472955265246510209)
                      ·
                        rfl

theorem cell23_7782224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 3].length) (baseStart_7782224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782224 prefixEnd_7782224 := by exact prefixLift 7782224
  have htrace : WordTrace (prefixWord ++ tailWord_7782224) baseStart_7782224 baseEnd_7782224 := by
    simpa [prefixWord, tailWord_7782224, baseEnd_7782224] using wordTrace_append hprefix tailTrace_7782224
  have hstable : (prefixWord ++ tailWord_7782224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782224).length < 2 ^ (prefixWord ++ tailWord_7782224).sum := by decide
  have hdescent : baseEnd_7782224 < baseStart_7782224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782234 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6]
def baseStart_7782234 : Nat := 118140960795 + 7782234 * 2 ^ 59
def prefixEnd_7782234 : Nat := 4983230072969 + 3 ^ 40 * 7782234 * 2
def baseEnd_7782234 : Nat := 3996026607761810207385163

theorem tailTrace_7782234 : CollatzResearch.WordTrace tailWord_7782234 prefixEnd_7782234 3996026607761810207385163 := by
  unfold tailWord_7782234
  simp only [CollatzResearch.WordTrace]
  refine ⟨70960348122075698149318439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189227594992201861731515837 70960348122075698149318439)
  ·
    refine ⟨106440522183113547223977659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70960348122075698149318439 106440522183113547223977659)
    ·
      refine ⟨159660783274670320835966489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106440522183113547223977659 159660783274670320835966489)
      ·
        refine ⟨119745587456002740626974867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159660783274670320835966489 119745587456002740626974867)
        ·
          refine ⟨179618381184004110940462301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119745587456002740626974867 179618381184004110940462301)
          ·
            refine ⟨67356892944001541602673363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179618381184004110940462301 67356892944001541602673363)
            ·
              refine ⟨101035339416002312404010045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67356892944001541602673363 101035339416002312404010045)
              ·
                refine ⟨37888252281000867151503767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101035339416002312404010045 37888252281000867151503767)
                ·
                  refine ⟨56832378421501300727255651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37888252281000867151503767 56832378421501300727255651)
                  ·
                    refine ⟨85248567632251951090883477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56832378421501300727255651 85248567632251951090883477)
                    ·
                      refine ⟨3996026607761810207385163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85248567632251951090883477 3996026607761810207385163)
                      ·
                        rfl

theorem cell23_7782234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_7782234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782234 prefixEnd_7782234 := by exact prefixLift 7782234
  have htrace : WordTrace (prefixWord ++ tailWord_7782234) baseStart_7782234 baseEnd_7782234 := by
    simpa [prefixWord, tailWord_7782234, baseEnd_7782234] using wordTrace_append hprefix tailTrace_7782234
  have hstable : (prefixWord ++ tailWord_7782234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782234).length < 2 ^ (prefixWord ++ tailWord_7782234).sum := by decide
  have hdescent : baseEnd_7782234 < baseStart_7782234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782241 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 3, 2, 3]
def baseStart_7782241 : Nat := 118140960795 + 7782241 * 2 ^ 59
def prefixEnd_7782241 : Nat := 4983230072969 + 3 ^ 40 * 7782241 * 2
def baseEnd_7782241 : Nat := 3996030202126391679997631

theorem tailTrace_7782241 : CollatzResearch.WordTrace tailWord_7782241 prefixEnd_7782241 3996030202126391679997631 := by
  unfold tailWord_7782241
  simp only [CollatzResearch.WordTrace]
  refine ⟨283841647799277432792778577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189227765199518288528519051 283841647799277432792778577)
  ·
    refine ⟨212881235849458074594583933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283841647799277432792778577 212881235849458074594583933)
    ·
      refine ⟨79830463443546777972968975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212881235849458074594583933 79830463443546777972968975)
      ·
        refine ⟨119745695165320166959453463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79830463443546777972968975 119745695165320166959453463)
        ·
          refine ⟨179618542747980250439180195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119745695165320166959453463 179618542747980250439180195)
          ·
            refine ⟨269427814121970375658770293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179618542747980250439180195 269427814121970375658770293)
            ·
              refine ⟨25258857573934722718009715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269427814121970375658770293 25258857573934722718009715)
              ·
                refine ⟨37888286360902084077014573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25258857573934722718009715 37888286360902084077014573)
                ·
                  refine ⟨14208107385338281528880465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37888286360902084077014573 14208107385338281528880465)
                  ·
                    refine ⟨10656080539003711146660349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14208107385338281528880465 10656080539003711146660349)
                    ·
                      refine ⟨3996030202126391679997631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10656080539003711146660349 3996030202126391679997631)
                      ·
                        rfl

theorem cell23_7782241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_7782241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782241 prefixEnd_7782241 := by exact prefixLift 7782241
  have htrace : WordTrace (prefixWord ++ tailWord_7782241) baseStart_7782241 baseEnd_7782241 := by
    simpa [prefixWord, tailWord_7782241, baseEnd_7782241] using wordTrace_append hprefix tailTrace_7782241
  have hstable : (prefixWord ++ tailWord_7782241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782241).length < 2 ^ (prefixWord ++ tailWord_7782241).sum := by decide
  have hdescent : baseEnd_7782241 < baseStart_7782241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782284 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 1, 4, 5]
def baseStart_7782284 : Nat := 118140960795 + 7782284 * 2 ^ 59
def prefixEnd_7782284 : Nat := 4983230072969 + 3 ^ 40 * 7782284 * 2
def baseEnd_7782284 : Nat := 3996052281794535011759933

theorem tailTrace_7782284 : CollatzResearch.WordTrace tailWord_7782284 prefixEnd_7782284 3996052281794535011759933 := by
  unfold tailWord_7782284
  simp only [CollatzResearch.WordTrace]
  refine ⟨141921608069060825568296953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189228810758747767424395937 141921608069060825568296953)
  ·
    refine ⟨106441206051795619176222715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141921608069060825568296953 106441206051795619176222715)
    ·
      refine ⟨159661809077693428764334073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106441206051795619176222715 159661809077693428764334073)
      ·
        refine ⟨119746356808270071573250555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159661809077693428764334073 119746356808270071573250555)
        ·
          refine ⟨179619535212405107359875833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119746356808270071573250555 179619535212405107359875833)
          ·
            refine ⟨134714651409303830519906875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179619535212405107359875833 134714651409303830519906875)
            ·
              refine ⟨202071977113955745779860313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134714651409303830519906875 202071977113955745779860313)
              ·
                refine ⟨151553982835466809334895235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202071977113955745779860313 151553982835466809334895235)
                ·
                  refine ⟨227330974253200214002342853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151553982835466809334895235 227330974253200214002342853)
                  ·
                    refine ⟨42624557672475040125439285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 227330974253200214002342853 42624557672475040125439285)
                    ·
                      refine ⟨3996052281794535011759933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42624557672475040125439285 3996052281794535011759933)
                      ·
                        rfl

theorem cell23_7782284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_7782284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782284 prefixEnd_7782284 := by exact prefixLift 7782284
  have htrace : WordTrace (prefixWord ++ tailWord_7782284) baseStart_7782284 baseEnd_7782284 := by
    simpa [prefixWord, tailWord_7782284, baseEnd_7782284] using wordTrace_append hprefix tailTrace_7782284
  have hstable : (prefixWord ++ tailWord_7782284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782284).length < 2 ^ (prefixWord ++ tailWord_7782284).sum := by decide
  have hdescent : baseEnd_7782284 < baseStart_7782284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782304 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 3, 8]
def baseStart_7782304 : Nat := 118140960795 + 7782304 * 2 ^ 59
def prefixEnd_7782304 : Nat := 4983230072969 + 3 ^ 40 * 7782304 * 2
def baseEnd_7782304 : Nat := 1332020850469208311169947

theorem tailTrace_7782304 : CollatzResearch.WordTrace tailWord_7782304 prefixEnd_7782304 1332020850469208311169947 := by
  unfold tailWord_7782304
  simp only [CollatzResearch.WordTrace]
  refine ⟨141921972799024597276160983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189229297065366129701547977 141921972799024597276160983)
  ·
    refine ⟨212882959198536895914241475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141921972799024597276160983 212882959198536895914241475)
    ·
      refine ⟨319324438797805343871362213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212882959198536895914241475 319324438797805343871362213)
      ·
        refine ⟨59873332274588501975880415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319324438797805343871362213 59873332274588501975880415)
        ·
          refine ⟨89809998411882752963820623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59873332274588501975880415 89809998411882752963820623)
          ·
            refine ⟨134714997617824129445730935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89809998411882752963820623 134714997617824129445730935)
            ·
              refine ⟨202072496426736194168596403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134714997617824129445730935 202072496426736194168596403)
              ·
                refine ⟨303108744640104291252894605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202072496426736194168596403 303108744640104291252894605)
                ·
                  refine ⟨113665779240039109219835477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303108744640104291252894605 113665779240039109219835477)
                  ·
                    refine ⟨1332020850469208311169947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113665779240039109219835477 1332020850469208311169947)
                    ·
                      rfl

theorem cell23_7782304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 8].length) (baseStart_7782304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782304 prefixEnd_7782304 := by exact prefixLift 7782304
  have htrace : WordTrace (prefixWord ++ tailWord_7782304) baseStart_7782304 baseEnd_7782304 := by
    simpa [prefixWord, tailWord_7782304, baseEnd_7782304] using wordTrace_append hprefix tailTrace_7782304
  have hstable : (prefixWord ++ tailWord_7782304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782304).length < 2 ^ (prefixWord ++ tailWord_7782304).sum := by decide
  have hdescent : baseEnd_7782304 < baseStart_7782304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782321 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 2, 6]
def baseStart_7782321 : Nat := 118140960795 + 7782321 * 2 ^ 59
def prefixEnd_7782321 : Nat := 4983230072969 + 3 ^ 40 * 7782321 * 2
def baseEnd_7782321 : Nat := 1332023760192917122332421

theorem tailTrace_7782321 : CollatzResearch.WordTrace tailWord_7782321 prefixEnd_7782321 1332023760192917122332421 := by
  unfold tailWord_7782321
  simp only [CollatzResearch.WordTrace]
  refine ⟨283844565638987606455690817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189229710425991737637127211 283844565638987606455690817)
  ·
    refine ⟨212883424229240704841768113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283844565638987606455690817 212883424229240704841768113)
    ·
      refine ⟨159662568171930528631326085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212883424229240704841768113 159662568171930528631326085)
      ·
        refine ⟨29936731532236974118373641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159662568171930528631326085 29936731532236974118373641)
        ·
          refine ⟨22452548649177730588780231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29936731532236974118373641 22452548649177730588780231)
          ·
            refine ⟨33678822973766595883170347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22452548649177730588780231 33678822973766595883170347)
            ·
              refine ⟨50518234460649893824755521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33678822973766595883170347 50518234460649893824755521)
              ·
                refine ⟨37888675845487420368566641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50518234460649893824755521 37888675845487420368566641)
                ·
                  refine ⟨28416506884115565276424981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37888675845487420368566641 28416506884115565276424981)
                  ·
                    refine ⟨1332023760192917122332421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28416506884115565276424981 1332023760192917122332421)
                    ·
                      rfl

theorem cell23_7782321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_7782321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782321 prefixEnd_7782321 := by exact prefixLift 7782321
  have htrace : WordTrace (prefixWord ++ tailWord_7782321) baseStart_7782321 baseEnd_7782321 := by
    simpa [prefixWord, tailWord_7782321, baseEnd_7782321] using wordTrace_append hprefix tailTrace_7782321
  have hstable : (prefixWord ++ tailWord_7782321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782321).length < 2 ^ (prefixWord ++ tailWord_7782321).sum := by decide
  have hdescent : baseEnd_7782321 < baseStart_7782321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782385 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 7]
def baseStart_7782385 : Nat := 118140960795 + 7782385 * 2 ^ 59
def prefixEnd_7782385 : Nat := 4983230072969 + 3 ^ 40 * 7782385 * 2
def baseEnd_7782385 : Nat := 444011571482293235177441

theorem tailTrace_7782385 : CollatzResearch.WordTrace tailWord_7782385 prefixEnd_7782385 444011571482293235177441 := by
  unfold tailWord_7782385
  simp only [CollatzResearch.WordTrace]
  refine ⟨283846899910755745386020609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189231266607170496924013739 283846899910755745386020609)
  ·
    refine ⟨212885174933066809039515457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283846899910755745386020609 212885174933066809039515457)
    ·
      refine ⟨159663881199800106779636593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212885174933066809039515457 159663881199800106779636593)
      ·
        refine ⟨119747910899850080084727445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159663881199800106779636593 119747910899850080084727445)
        ·
          refine ⟨5613183323430472503971599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119747910899850080084727445 5613183323430472503971599)
          ·
            refine ⟨8419774985145708755957399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5613183323430472503971599 8419774985145708755957399)
            ·
              refine ⟨12629662477718563133936099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8419774985145708755957399 12629662477718563133936099)
              ·
                refine ⟨18944493716577844700904149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12629662477718563133936099 18944493716577844700904149)
                ·
                  refine ⟨444011571482293235177441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18944493716577844700904149 444011571482293235177441)
                  ·
                    rfl

theorem cell23_7782385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 7].length) (baseStart_7782385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782385 prefixEnd_7782385 := by exact prefixLift 7782385
  have htrace : WordTrace (prefixWord ++ tailWord_7782385) baseStart_7782385 baseEnd_7782385 := by
    simpa [prefixWord, tailWord_7782385, baseEnd_7782385] using wordTrace_append hprefix tailTrace_7782385
  have hstable : (prefixWord ++ tailWord_7782385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782385).length < 2 ^ (prefixWord ++ tailWord_7782385).sum := by decide
  have hdescent : baseEnd_7782385 < baseStart_7782385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782431 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 6]
def baseStart_7782431 : Nat := 118140960795 + 7782431 * 2 ^ 59
def prefixEnd_7782431 : Nat := 4983230072969 + 3 ^ 40 * 7782431 * 2
def baseEnd_7782431 : Nat := 3996127763450745936621757

theorem tailTrace_7782431 : CollatzResearch.WordTrace tailWord_7782431 prefixEnd_7782431 3996127763450745936621757 := by
  unfold tailWord_7782431
  simp only [CollatzResearch.WordTrace]
  refine ⟨283848577668589095242195147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189232385112392730161463431 283848577668589095242195147)
  ·
    refine ⟨425772866502883642863292721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283848577668589095242195147 425772866502883642863292721)
    ·
      refine ⟨319329649877162732147469541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425772866502883642863292721 319329649877162732147469541)
      ·
        refine ⟨59874309351968012277650539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319329649877162732147469541 59874309351968012277650539)
        ·
          refine ⟨89811464027952018416475809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59874309351968012277650539 89811464027952018416475809)
          ·
            refine ⟨67358598020964013812356857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89811464027952018416475809 67358598020964013812356857)
            ·
              refine ⟨50518948515723010359267643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67358598020964013812356857 50518948515723010359267643)
              ·
                refine ⟨75778422773584515538901465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50518948515723010359267643 75778422773584515538901465)
                ·
                  refine ⟨56833817080188386654176099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75778422773584515538901465 56833817080188386654176099)
                  ·
                    refine ⟨85250725620282579981264149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56833817080188386654176099 85250725620282579981264149)
                    ·
                      refine ⟨3996127763450745936621757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85250725620282579981264149 3996127763450745936621757)
                      ·
                        rfl

theorem cell23_7782431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_7782431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782431 prefixEnd_7782431 := by exact prefixLift 7782431
  have htrace : WordTrace (prefixWord ++ tailWord_7782431) baseStart_7782431 baseEnd_7782431 := by
    simpa [prefixWord, tailWord_7782431, baseEnd_7782431] using wordTrace_append hprefix tailTrace_7782431
  have hstable : (prefixWord ++ tailWord_7782431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782431).length < 2 ^ (prefixWord ++ tailWord_7782431).sum := by decide
  have hdescent : baseEnd_7782431 < baseStart_7782431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782462 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_7782462 : Nat := 118140960795 + 7782462 * 2 ^ 59
def prefixEnd_7782462 : Nat := 4983230072969 + 3 ^ 40 * 7782462 * 2
def baseEnd_7782462 : Nat := 1332047893783678438444705

theorem tailTrace_7782462 : CollatzResearch.WordTrace tailWord_7782462 prefixEnd_7782462 1332047893783678438444705 := by
  unfold tailWord_7782462
  simp only [CollatzResearch.WordTrace]
  refine ⟨35481213541434598442071705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189233138887651191691049093 35481213541434598442071705)
  ·
    refine ⟨26610910156075948831553779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35481213541434598442071705 26610910156075948831553779)
    ·
      refine ⟨39916365234113923247330669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26610910156075948831553779 39916365234113923247330669)
      ·
        refine ⟨14968636962792721217749001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39916365234113923247330669 14968636962792721217749001)
        ·
          refine ⟨11226477722094540913311751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14968636962792721217749001 11226477722094540913311751)
          ·
            refine ⟨16839716583141811369967627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11226477722094540913311751 16839716583141811369967627)
            ·
              refine ⟨25259574874712717054951441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16839716583141811369967627 25259574874712717054951441)
              ·
                refine ⟨18944681156034537791213581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25259574874712717054951441 18944681156034537791213581)
                ·
                  refine ⟨7104255433512951671705093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18944681156034537791213581 7104255433512951671705093)
                  ·
                    refine ⟨1332047893783678438444705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7104255433512951671705093 1332047893783678438444705)
                    ·
                      rfl

theorem cell23_7782462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_7782462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782462 prefixEnd_7782462 := by exact prefixLift 7782462
  have htrace : WordTrace (prefixWord ++ tailWord_7782462) baseStart_7782462 baseEnd_7782462 := by
    simpa [prefixWord, tailWord_7782462, baseEnd_7782462] using wordTrace_append hprefix tailTrace_7782462
  have hstable : (prefixWord ++ tailWord_7782462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782462).length < 2 ^ (prefixWord ++ tailWord_7782462).sum := by decide
  have hdescent : baseEnd_7782462 < baseStart_7782462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782481 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 2, 4, 5]
def baseStart_7782481 : Nat := 118140960795 + 7782481 * 2 ^ 59
def prefixEnd_7782481 : Nat := 4983230072969 + 3 ^ 40 * 7782481 * 2
def baseEnd_7782481 : Nat := 3996153437483470740996527

theorem tailTrace_7782481 : CollatzResearch.WordTrace tailWord_7782481 prefixEnd_7782481 3996153437483470740996527 := by
  unfold tailWord_7782481
  simp only [CollatzResearch.WordTrace]
  refine ⟨283850401318407953781515297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189233600878938635854343531 283850401318407953781515297)
  ·
    refine ⟨212887800988805965336136473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283850401318407953781515297 212887800988805965336136473)
    ·
      refine ⟨159665850741604474002102355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212887800988805965336136473 159665850741604474002102355)
      ·
        refine ⟨239498776112406711003153533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159665850741604474002102355 239498776112406711003153533)
        ·
          refine ⟨89812041042152516626182575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239498776112406711003153533 89812041042152516626182575)
          ·
            refine ⟨134718061563228774939273863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89812041042152516626182575 134718061563228774939273863)
            ·
              refine ⟨202077092344843162408910795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134718061563228774939273863 202077092344843162408910795)
              ·
                refine ⟨303115638517264743613366193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202077092344843162408910795 303115638517264743613366193)
                ·
                  refine ⟨227336728887948557710024645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303115638517264743613366193 227336728887948557710024645)
                  ·
                    refine ⟨42625636666490354570629621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 227336728887948557710024645 42625636666490354570629621)
                    ·
                      refine ⟨3996153437483470740996527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42625636666490354570629621 3996153437483470740996527)
                      ·
                        rfl

theorem cell23_7782481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_7782481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782481 prefixEnd_7782481 := by exact prefixLift 7782481
  have htrace : WordTrace (prefixWord ++ tailWord_7782481) baseStart_7782481 baseEnd_7782481 := by
    simpa [prefixWord, tailWord_7782481, baseEnd_7782481] using wordTrace_append hprefix tailTrace_7782481
  have hstable : (prefixWord ++ tailWord_7782481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782481).length < 2 ^ (prefixWord ++ tailWord_7782481).sum := by decide
  have hdescent : baseEnd_7782481 < baseStart_7782481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782525 : List Nat := [1, 4, 1, 1, 3, 2, 1, 4, 1, 1, 4]
def baseStart_7782525 : Nat := 118140960795 + 7782525 * 2 ^ 59
def prefixEnd_7782525 : Nat := 4983230072969 + 3 ^ 40 * 7782525 * 2
def baseEnd_7782525 : Nat := 3996176030632268568846325

theorem tailTrace_7782525 : CollatzResearch.WordTrace tailWord_7782525 prefixEnd_7782525 3996176030632268568846325 := by
  unfold tailWord_7782525
  simp only [CollatzResearch.WordTrace]
  refine ⟨283852006130248549296117029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189234670753499032864078019 283852006130248549296117029)
  ·
    refine ⟨53222251149421602993021943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283852006130248549296117029 53222251149421602993021943)
    ·
      refine ⟨79833376724132404489532915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53222251149421602993021943 79833376724132404489532915)
      ·
        refine ⟨119750065086198606734299373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79833376724132404489532915 119750065086198606734299373)
        ·
          refine ⟨44906274407324477525362265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119750065086198606734299373 44906274407324477525362265)
          ·
            refine ⟨33679705805493358144021699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44906274407324477525362265 33679705805493358144021699)
            ·
              refine ⟨50519558708240037216032549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33679705805493358144021699 50519558708240037216032549)
              ·
                refine ⟨9472417257795006978006103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50519558708240037216032549 9472417257795006978006103)
                ·
                  refine ⟨14208625886692510467009155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9472417257795006978006103 14208625886692510467009155)
                  ·
                    refine ⟨21312938830038765700513733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14208625886692510467009155 21312938830038765700513733)
                    ·
                      refine ⟨3996176030632268568846325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21312938830038765700513733 3996176030632268568846325)
                      ·
                        rfl

theorem cell23_7782525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_7782525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782525 prefixEnd_7782525 := by exact prefixLift 7782525
  have htrace : WordTrace (prefixWord ++ tailWord_7782525) baseStart_7782525 baseEnd_7782525 := by
    simpa [prefixWord, tailWord_7782525, baseEnd_7782525] using wordTrace_append hprefix tailTrace_7782525
  have hstable : (prefixWord ++ tailWord_7782525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782525).length < 2 ^ (prefixWord ++ tailWord_7782525).sum := by decide
  have hdescent : baseEnd_7782525 < baseStart_7782525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782536 : List Nat := [2, 1, 3, 4, 1, 3, 1, 3, 1, 1, 3]
def baseStart_7782536 : Nat := 118140960795 + 7782536 * 2 ^ 59
def prefixEnd_7782536 : Nat := 4983230072969 + 3 ^ 40 * 7782536 * 2
def baseEnd_7782536 : Nat := 3996181678919468025808775

theorem tailTrace_7782536 : CollatzResearch.WordTrace tailWord_7782536 prefixEnd_7782536 3996181678919468025808775 := by
  unfold tailWord_7782536
  simp only [CollatzResearch.WordTrace]
  refine ⟨141926203666604349087383731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189234938222139132116511641 141926203666604349087383731)
  ·
    refine ⟨212889305499906523631075597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141926203666604349087383731 212889305499906523631075597)
    ·
      refine ⟨79833489562464946361653349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212889305499906523631075597 79833489562464946361653349)
      ·
        refine ⟨14968779292962177442810003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79833489562464946361653349 14968779292962177442810003)
        ·
          refine ⟨22453168939443266164215005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14968779292962177442810003 22453168939443266164215005)
          ·
            refine ⟨8419938352291224811580627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22453168939443266164215005 8419938352291224811580627)
            ·
              refine ⟨12629907528436837217370941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8419938352291224811580627 12629907528436837217370941)
              ·
                refine ⟨4736215323163813956514103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12629907528436837217370941 4736215323163813956514103)
                ·
                  refine ⟨7104322984745720934771155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4736215323163813956514103 7104322984745720934771155)
                  ·
                    refine ⟨10656484477118581402156733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7104322984745720934771155 10656484477118581402156733)
                    ·
                      refine ⟨3996181678919468025808775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10656484477118581402156733 3996181678919468025808775)
                      ·
                        rfl

theorem cell23_7782536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_7782536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782536 prefixEnd_7782536 := by exact prefixLift 7782536
  have htrace : WordTrace (prefixWord ++ tailWord_7782536) baseStart_7782536 baseEnd_7782536 := by
    simpa [prefixWord, tailWord_7782536, baseEnd_7782536] using wordTrace_append hprefix tailTrace_7782536
  have hstable : (prefixWord ++ tailWord_7782536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782536).length < 2 ^ (prefixWord ++ tailWord_7782536).sum := by decide
  have hdescent : baseEnd_7782536 < baseStart_7782536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782559 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 3, 2, 2]
def baseStart_7782559 : Nat := 118140960795 + 7782559 * 2 ^ 59
def prefixEnd_7782559 : Nat := 4983230072969 + 3 ^ 40 * 7782559 * 2
def baseEnd_7782559 : Nat := 3996193488974521435821169

theorem tailTrace_7782559 : CollatzResearch.WordTrace tailWord_7782559 prefixEnd_7782559 3996193488974521435821169 := by
  unfold tailWord_7782559
  simp only [CollatzResearch.WordTrace]
  refine ⟨283853246212125373102854731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189235497474750248735236487 283853246212125373102854731)
  ·
    refine ⟨425779869318188059654282097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283853246212125373102854731 425779869318188059654282097)
    ·
      refine ⟨319334901988641044740711573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425779869318188059654282097 319334901988641044740711573)
      ·
        refine ⟨14968823530717548972220855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 319334901988641044740711573 14968823530717548972220855)
        ·
          refine ⟨22453235296076323458331283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14968823530717548972220855 22453235296076323458331283)
          ·
            refine ⟨33679852944114485187496925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22453235296076323458331283 33679852944114485187496925)
            ·
              refine ⟨12629944854042931945311347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33679852944114485187496925 12629944854042931945311347)
              ·
                refine ⟨18944917281064397917967021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12629944854042931945311347 18944917281064397917967021)
                ·
                  refine ⟨7104343980399149219237633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18944917281064397917967021 7104343980399149219237633)
                  ·
                    refine ⟨5328257985299361914428225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7104343980399149219237633 5328257985299361914428225)
                    ·
                      refine ⟨3996193488974521435821169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5328257985299361914428225 3996193488974521435821169)
                      ·
                        rfl

theorem cell23_7782559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_7782559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782559 prefixEnd_7782559 := by exact prefixLift 7782559
  have htrace : WordTrace (prefixWord ++ tailWord_7782559) baseStart_7782559 baseEnd_7782559 := by
    simpa [prefixWord, tailWord_7782559, baseEnd_7782559] using wordTrace_append hprefix tailTrace_7782559
  have hstable : (prefixWord ++ tailWord_7782559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782559).length < 2 ^ (prefixWord ++ tailWord_7782559).sum := by decide
  have hdescent : baseEnd_7782559 < baseStart_7782559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782615 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 5, 4, 2]
def baseStart_7782615 : Nat := 118140960795 + 7782615 * 2 ^ 59
def prefixEnd_7782615 : Nat := 4983230072969 + 3 ^ 40 * 7782615 * 2
def baseEnd_7782615 : Nat := 3996222243891173216720911

theorem tailTrace_7782615 : CollatzResearch.WordTrace tailWord_7782615 prefixEnd_7782615 3996222243891173216720911 := by
  unfold tailWord_7782615
  simp only [CollatzResearch.WordTrace]
  refine ⟨283855288699922494666893299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189236859133281663111262199 283855288699922494666893299)
  ·
    refine ⟨425782933049883742000339949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283855288699922494666893299 425782933049883742000339949)
    ·
      refine ⟨159668599893706403250127481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425782933049883742000339949 159668599893706403250127481)
      ·
        refine ⟨119751449920279802437595611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159668599893706403250127481 119751449920279802437595611)
        ·
          refine ⟨179627174880419703656393417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119751449920279802437595611 179627174880419703656393417)
          ·
            refine ⟨134720381160314777742295063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179627174880419703656393417 134720381160314777742295063)
            ·
              refine ⟨202080571740472166613442595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134720381160314777742295063 202080571740472166613442595)
              ·
                refine ⟨303120857610708249920163893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202080571740472166613442595 303120857610708249920163893)
                ·
                  refine ⟨28417580401003898430015365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 303120857610708249920163893 28417580401003898430015365)
                  ·
                    refine ⟨5328296325188230955627881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28417580401003898430015365 5328296325188230955627881)
                    ·
                      refine ⟨3996222243891173216720911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5328296325188230955627881 3996222243891173216720911)
                      ·
                        rfl

theorem cell23_7782615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_7782615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782615 prefixEnd_7782615 := by exact prefixLift 7782615
  have htrace : WordTrace (prefixWord ++ tailWord_7782615) baseStart_7782615 baseEnd_7782615 := by
    simpa [prefixWord, tailWord_7782615, baseEnd_7782615] using wordTrace_append hprefix tailTrace_7782615
  have hstable : (prefixWord ++ tailWord_7782615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782615).length < 2 ^ (prefixWord ++ tailWord_7782615).sum := by decide
  have hdescent : baseEnd_7782615 < baseStart_7782615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782618 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5]
def baseStart_7782618 : Nat := 118140960795 + 7782618 * 2 ^ 59
def prefixEnd_7782618 : Nat := 4983230072969 + 3 ^ 40 * 7782618 * 2
def baseEnd_7782618 : Nat := 3996223784333136704983397

theorem tailTrace_7782618 : CollatzResearch.WordTrace tailWord_7782618 prefixEnd_7782618 3996223784333136704983397 := by
  unfold tailWord_7782618
  simp only [CollatzResearch.WordTrace]
  refine ⟨70963849529727906544813127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189236932079274417452835005 70963849529727906544813127)
  ·
    refine ⟨106445774294591859817219691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70963849529727906544813127 106445774294591859817219691)
    ·
      refine ⟨159668661441887789725829537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106445774294591859817219691 159668661441887789725829537)
      ·
        refine ⟨119751496081415842294372153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159668661441887789725829537 119751496081415842294372153)
        ·
          refine ⟨89813622061061881720779115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119751496081415842294372153 89813622061061881720779115)
          ·
            refine ⟨134720433091592822581168673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89813622061061881720779115 134720433091592822581168673)
            ·
              refine ⟨101040324818694616935876505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134720433091592822581168673 101040324818694616935876505)
              ·
                refine ⟨75780243614020962701907379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101040324818694616935876505 75780243614020962701907379)
                ·
                  refine ⟨113670365421031444052861069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75780243614020962701907379 113670365421031444052861069)
                  ·
                    refine ⟨42626387032886791519822901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113670365421031444052861069 42626387032886791519822901)
                    ·
                      refine ⟨3996223784333136704983397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42626387032886791519822901 3996223784333136704983397)
                      ·
                        rfl

theorem cell23_7782618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_7782618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782618 prefixEnd_7782618 := by exact prefixLift 7782618
  have htrace : WordTrace (prefixWord ++ tailWord_7782618) baseStart_7782618 baseEnd_7782618 := by
    simpa [prefixWord, tailWord_7782618, baseEnd_7782618] using wordTrace_append hprefix tailTrace_7782618
  have hstable : (prefixWord ++ tailWord_7782618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782618).length < 2 ^ (prefixWord ++ tailWord_7782618).sum := by decide
  have hdescent : baseEnd_7782618 < baseStart_7782618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782632 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 1, 4, 2]
def baseStart_7782632 : Nat := 118140960795 + 7782632 * 2 ^ 59
def prefixEnd_7782632 : Nat := 4983230072969 + 3 ^ 40 * 7782632 * 2
def baseEnd_7782632 : Nat := 3996230973062299650208333

theorem tailTrace_7782632 : CollatzResearch.WordTrace tailWord_7782632 prefixEnd_7782632 3996230973062299650208333 := by
  unfold tailWord_7782632
  simp only [CollatzResearch.WordTrace]
  refine ⟨141927954370430453285131075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189237272493907271046841433 141927954370430453285131075)
  ·
    refine ⟨212891931555645679927696613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141927954370430453285131075 212891931555645679927696613)
    ·
      refine ⟨39917237166683564986443115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212891931555645679927696613 39917237166683564986443115)
      ·
        refine ⟨59875855750025347479664673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39917237166683564986443115 59875855750025347479664673)
        ·
          refine ⟨44906891812519010609748505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59875855750025347479664673 44906891812519010609748505)
          ·
            refine ⟨33680168859389257957311379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44906891812519010609748505 33680168859389257957311379)
            ·
              refine ⟨50520253289083886935967069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33680168859389257957311379 50520253289083886935967069)
              ·
                refine ⟨18945094983406457600987651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50520253289083886935967069 18945094983406457600987651)
                ·
                  refine ⟨28417642475109686401481477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18945094983406457600987651 28417642475109686401481477)
                  ·
                    refine ⟨5328307964083066200277777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28417642475109686401481477 5328307964083066200277777)
                    ·
                      refine ⟨3996230973062299650208333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5328307964083066200277777 3996230973062299650208333)
                      ·
                        rfl

theorem cell23_7782632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_7782632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782632 prefixEnd_7782632 := by exact prefixLift 7782632
  have htrace : WordTrace (prefixWord ++ tailWord_7782632) baseStart_7782632 baseEnd_7782632 := by
    simpa [prefixWord, tailWord_7782632, baseEnd_7782632] using wordTrace_append hprefix tailTrace_7782632
  have hstable : (prefixWord ++ tailWord_7782632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782632).length < 2 ^ (prefixWord ++ tailWord_7782632).sum := by decide
  have hdescent : baseEnd_7782632 < baseStart_7782632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782665 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 2, 3, 3]
def baseStart_7782665 : Nat := 118140960795 + 7782665 * 2 ^ 59
def prefixEnd_7782665 : Nat := 4983230072969 + 3 ^ 40 * 7782665 * 2
def baseEnd_7782665 : Nat := 3996247917923898021095681

theorem tailTrace_7782665 : CollatzResearch.WordTrace tailWord_7782665 prefixEnd_7782665 3996247917923898021095681 := by
  unfold tailWord_7782665
  simp only [CollatzResearch.WordTrace]
  refine ⟨283857112349741353206213449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189238074899827568804142299 283857112349741353206213449)
  ·
    refine ⟨212892834262306014904660087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283857112349741353206213449 212892834262306014904660087)
    ·
      refine ⟨319339251393459022356990131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212892834262306014904660087 319339251393459022356990131)
      ·
        refine ⟨479008877090188533535485197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319339251393459022356990131 479008877090188533535485197)
        ·
          refine ⟨179628328908820700075806949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479008877090188533535485197 179628328908820700075806949)
          ·
            refine ⟨33680311670403881264213803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179628328908820700075806949 33680311670403881264213803)
            ·
              refine ⟨50520467505605821896320705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33680311670403881264213803 50520467505605821896320705)
              ·
                refine ⟨37890350629204366422240529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50520467505605821896320705 37890350629204366422240529)
                ·
                  refine ⟨28417762971903274816680397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37890350629204366422240529 28417762971903274816680397)
                  ·
                    refine ⟨10656661114463728056255149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28417762971903274816680397 10656661114463728056255149)
                    ·
                      refine ⟨3996247917923898021095681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10656661114463728056255149 3996247917923898021095681)
                      ·
                        rfl

theorem cell23_7782665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 3, 3].length) (baseStart_7782665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782665 prefixEnd_7782665 := by exact prefixLift 7782665
  have htrace : WordTrace (prefixWord ++ tailWord_7782665) baseStart_7782665 baseEnd_7782665 := by
    simpa [prefixWord, tailWord_7782665, baseEnd_7782665] using wordTrace_append hprefix tailTrace_7782665
  have hstable : (prefixWord ++ tailWord_7782665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782665).length < 2 ^ (prefixWord ++ tailWord_7782665).sum := by decide
  have hdescent : baseEnd_7782665 < baseStart_7782665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782675 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 1, 7, 2]
def baseStart_7782675 : Nat := 118140960795 + 7782675 * 2 ^ 59
def prefixEnd_7782675 : Nat := 4983230072969 + 3 ^ 40 * 7782675 * 2
def baseEnd_7782675 : Nat := 3996253052730442981970635

theorem tailTrace_7782675 : CollatzResearch.WordTrace tailWord_7782675 prefixEnd_7782675 3996253052730442981970635 := by
  unfold tailWord_7782675
  simp only [CollatzResearch.WordTrace]
  refine ⟨283857477079705124914077479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189238318053136749942718319 283857477079705124914077479)
  ·
    refine ⟨425786215619557687371116219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283857477079705124914077479 425786215619557687371116219)
    ·
      refine ⟨638679323429336531056674329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425786215619557687371116219 638679323429336531056674329)
      ·
        refine ⟨479009492572002398292505747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 638679323429336531056674329 479009492572002398292505747)
        ·
          refine ⟨718514238858003597438758621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479009492572002398292505747 718514238858003597438758621)
          ·
            refine ⟨269442839571751349039534483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 718514238858003597438758621 269442839571751349039534483)
            ·
              refine ⟨404164259357627023559301725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269442839571751349039534483 404164259357627023559301725)
              ·
                refine ⟨151561597259110133834738147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404164259357627023559301725 151561597259110133834738147)
                ·
                  refine ⟨227342395888665200752107221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151561597259110133834738147 227342395888665200752107221)
                  ·
                    refine ⟨5328337403640590642627513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 227342395888665200752107221 5328337403640590642627513)
                    ·
                      refine ⟨3996253052730442981970635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5328337403640590642627513 3996253052730442981970635)
                      ·
                        rfl

theorem cell23_7782675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 7, 2].length) (baseStart_7782675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782675 prefixEnd_7782675 := by exact prefixLift 7782675
  have htrace : WordTrace (prefixWord ++ tailWord_7782675) baseStart_7782675 baseEnd_7782675 := by
    simpa [prefixWord, tailWord_7782675, baseEnd_7782675] using wordTrace_append hprefix tailTrace_7782675
  have hstable : (prefixWord ++ tailWord_7782675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782675).length < 2 ^ (prefixWord ++ tailWord_7782675).sum := by decide
  have hdescent : baseEnd_7782675 < baseStart_7782675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782706 : List Nat := [3, 2, 1, 1, 6, 1, 1, 3, 5]
def baseStart_7782706 : Nat := 118140960795 + 7782706 * 2 ^ 59
def prefixEnd_7782706 : Nat := 4983230072969 + 3 ^ 40 * 7782706 * 2
def baseEnd_7782706 : Nat := 444029885625636928964777

theorem tailTrace_7782706 : CollatzResearch.WordTrace tailWord_7782706 prefixEnd_7782706 444029885625636928964777 := by
  unfold tailWord_7782706
  simp only [CollatzResearch.WordTrace]
  refine ⟨70964651935648204302113993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189239071828395211472303981 70964651935648204302113993)
  ·
    refine ⟨53223488951736153226585495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70964651935648204302113993 53223488951736153226585495)
    ·
      refine ⟨79835233427604229839878243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53223488951736153226585495 79835233427604229839878243)
      ·
        refine ⟨119752850141406344759817365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79835233427604229839878243 119752850141406344759817365)
        ·
          refine ⟨5613414850378422410616439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119752850141406344759817365 5613414850378422410616439)
          ·
            refine ⟨8420122275567633615924659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5613414850378422410616439 8420122275567633615924659)
            ·
              refine ⟨12630183413351450423886989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8420122275567633615924659 12630183413351450423886989)
              ·
                refine ⟨4736318780006793908957621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12630183413351450423886989 4736318780006793908957621)
                ·
                  refine ⟨444029885625636928964777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4736318780006793908957621 444029885625636928964777)
                  ·
                    rfl

theorem cell23_7782706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_7782706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782706 prefixEnd_7782706 := by exact prefixLift 7782706
  have htrace : WordTrace (prefixWord ++ tailWord_7782706) baseStart_7782706 baseEnd_7782706 := by
    simpa [prefixWord, tailWord_7782706, baseEnd_7782706] using wordTrace_append hprefix tailTrace_7782706
  have hstable : (prefixWord ++ tailWord_7782706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782706).length < 2 ^ (prefixWord ++ tailWord_7782706).sum := by decide
  have hdescent : baseEnd_7782706 < baseStart_7782706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782759 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_7782759 : Nat := 118140960795 + 7782759 * 2 ^ 59
def prefixEnd_7782759 : Nat := 4983230072969 + 3 ^ 40 * 7782759 * 2
def baseEnd_7782759 : Nat := 3996296185105420653320249

theorem tailTrace_7782759 : CollatzResearch.WordTrace tailWord_7782759 prefixEnd_7782759 3996296185105420653320249 := by
  unfold tailWord_7782759
  simp only [CollatzResearch.WordTrace]
  refine ⟨283860540811400807260135331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189240360540933871506756887 283860540811400807260135331)
  ·
    refine ⟨425790811217101210890202997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283860540811400807260135331 425790811217101210890202997)
    ·
      refine ⟨39917888551603238520956531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 425790811217101210890202997 39917888551603238520956531)
      ·
        refine ⟨59876832827404857781434797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39917888551603238520956531 59876832827404857781434797)
        ·
          refine ⟨22453812310276821668038049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59876832827404857781434797 22453812310276821668038049)
          ·
            refine ⟨16840359232707616251028537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22453812310276821668038049 16840359232707616251028537)
            ·
              refine ⟨12630269424530712188271403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16840359232707616251028537 12630269424530712188271403)
              ·
                refine ⟨18945404136796068282407105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12630269424530712188271403 18945404136796068282407105)
                ·
                  refine ⟨14209053102597051211805329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18945404136796068282407105 14209053102597051211805329)
                  ·
                    refine ⟨10656789826947788408853997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14209053102597051211805329 10656789826947788408853997)
                    ·
                      refine ⟨3996296185105420653320249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10656789826947788408853997 3996296185105420653320249)
                      ·
                        rfl

theorem cell23_7782759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_7782759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782759 prefixEnd_7782759 := by exact prefixLift 7782759
  have htrace : WordTrace (prefixWord ++ tailWord_7782759) baseStart_7782759 baseEnd_7782759 := by
    simpa [prefixWord, tailWord_7782759, baseEnd_7782759] using wordTrace_append hprefix tailTrace_7782759
  have hstable : (prefixWord ++ tailWord_7782759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782759).length < 2 ^ (prefixWord ++ tailWord_7782759).sum := by decide
  have hdescent : baseEnd_7782759 < baseStart_7782759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782816 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 2, 3, 2]
def baseStart_7782816 : Nat := 118140960795 + 7782816 * 2 ^ 59
def prefixEnd_7782816 : Nat := 4983230072969 + 3 ^ 40 * 7782816 * 2
def baseEnd_7782816 : Nat := 3996325453502726930307487

theorem tailTrace_7782816 : CollatzResearch.WordTrace tailWord_7782816 prefixEnd_7782816 3996325453502726930307487 := by
  unfold tailWord_7782816
  simp only [CollatzResearch.WordTrace]
  refine ⟨141931309886097152997480151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189241746514796203996640201 141931309886097152997480151)
  ·
    refine ⟨212896964829145729496220227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141931309886097152997480151 212896964829145729496220227)
    ·
      refine ⟨319345447243718594244330341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212896964829145729496220227 319345447243718594244330341)
      ·
        refine ⟨59877271358197236420811939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319345447243718594244330341 59877271358197236420811939)
        ·
          refine ⟨89815907037295854631217909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59877271358197236420811939 89815907037295854631217909)
          ·
            refine ⟨8420241284746486371676679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89815907037295854631217909 8420241284746486371676679)
            ·
              refine ⟨12630361927119729557515019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8420241284746486371676679 12630361927119729557515019)
              ·
                refine ⟨18945542890679594336272529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12630361927119729557515019 18945542890679594336272529)
                ·
                  refine ⟨14209157168009695752204397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18945542890679594336272529 14209157168009695752204397)
                  ·
                    refine ⟨5328433938003635907076649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14209157168009695752204397 5328433938003635907076649)
                    ·
                      refine ⟨3996325453502726930307487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5328433938003635907076649 3996325453502726930307487)
                      ·
                        rfl

theorem cell23_7782816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_7782816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782816 prefixEnd_7782816 := by exact prefixLift 7782816
  have htrace : WordTrace (prefixWord ++ tailWord_7782816) baseStart_7782816 baseEnd_7782816 := by
    simpa [prefixWord, tailWord_7782816, baseEnd_7782816] using wordTrace_append hprefix tailTrace_7782816
  have hstable : (prefixWord ++ tailWord_7782816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782816).length < 2 ^ (prefixWord ++ tailWord_7782816).sum := by decide
  have hdescent : baseEnd_7782816 < baseStart_7782816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782823 : List Nat := [1, 1, 6, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_7782823 : Nat := 118140960795 + 7782823 * 2 ^ 59
def prefixEnd_7782823 : Nat := 4983230072969 + 3 ^ 40 * 7782823 * 2
def baseEnd_7782823 : Nat := 3996329047867308402919955

theorem tailTrace_7782823 : CollatzResearch.WordTrace tailWord_7782823 prefixEnd_7782823 3996329047867308402919955 := by
  unfold tailWord_7782823
  simp only [CollatzResearch.WordTrace]
  refine ⟨283862875083168946190465123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189241916722112630793643415 283862875083168946190465123)
  ·
    refine ⟨425794312624753419285697685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283862875083168946190465123 425794312624753419285697685)
    ·
      refine ⟨19959108404285316529017079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 425794312624753419285697685 19959108404285316529017079)
      ·
        refine ⟨29938662606427974793525619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19959108404285316529017079 29938662606427974793525619)
        ·
          refine ⟨44907993909641962190288429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29938662606427974793525619 44907993909641962190288429)
          ·
            refine ⟨16840497716115735821358161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44907993909641962190288429 16840497716115735821358161)
            ·
              refine ⟨12630373287086801866018621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16840497716115735821358161 12630373287086801866018621)
              ·
                refine ⟨4736389982657550699756983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12630373287086801866018621 4736389982657550699756983)
                ·
                  refine ⟨7104584973986326049635475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4736389982657550699756983 7104584973986326049635475)
                  ·
                    refine ⟨10656877460979489074453213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7104584973986326049635475 10656877460979489074453213)
                    ·
                      refine ⟨3996329047867308402919955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10656877460979489074453213 3996329047867308402919955)
                      ·
                        rfl

theorem cell23_7782823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_7782823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782823 prefixEnd_7782823 := by exact prefixLift 7782823
  have htrace : WordTrace (prefixWord ++ tailWord_7782823) baseStart_7782823 baseEnd_7782823 := by
    simpa [prefixWord, tailWord_7782823, baseEnd_7782823] using wordTrace_append hprefix tailTrace_7782823
  have hstable : (prefixWord ++ tailWord_7782823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782823).length < 2 ^ (prefixWord ++ tailWord_7782823).sum := by decide
  have hdescent : baseEnd_7782823 < baseStart_7782823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782839 : List Nat := [1, 1, 3, 1, 3, 3, 3, 2, 2, 4]
def baseStart_7782839 : Nat := 118140960795 + 7782839 * 2 ^ 59
def prefixEnd_7782839 : Nat := 4983230072969 + 3 ^ 40 * 7782839 * 2
def baseEnd_7782839 : Nat := 1332112421185926780106627

theorem tailTrace_7782839 : CollatzResearch.WordTrace tailWord_7782839 prefixEnd_7782839 1332112421185926780106627 := by
  unfold tailWord_7782839
  simp only [CollatzResearch.WordTrace]
  refine ⟨283863458651110980923047571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189242305767407320615365047 283863458651110980923047571)
  ·
    refine ⟨425795187976666471384571357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283863458651110980923047571 425795187976666471384571357)
    ·
      refine ⟨159673195491249926769214259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425795187976666471384571357 159673195491249926769214259)
      ·
        refine ⟨239509793236874890153821389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159673195491249926769214259 239509793236874890153821389)
        ·
          refine ⟨89816172463828083807683021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239509793236874890153821389 89816172463828083807683021)
          ·
            refine ⟨33681064673935531427881133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89816172463828083807683021 33681064673935531427881133)
            ·
              refine ⟨12630399252725824285455425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33681064673935531427881133 12630399252725824285455425)
              ·
                refine ⟨9472799439544368214091569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12630399252725824285455425 9472799439544368214091569)
                ·
                  refine ⟨7104599579658276160568677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9472799439544368214091569 7104599579658276160568677)
                  ·
                    refine ⟨1332112421185926780106627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7104599579658276160568677 1332112421185926780106627)
                    ·
                      rfl

theorem cell23_7782839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_7782839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782839 prefixEnd_7782839 := by exact prefixLift 7782839
  have htrace : WordTrace (prefixWord ++ tailWord_7782839) baseStart_7782839 baseEnd_7782839 := by
    simpa [prefixWord, tailWord_7782839, baseEnd_7782839] using wordTrace_append hprefix tailTrace_7782839
  have hstable : (prefixWord ++ tailWord_7782839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782839).length < 2 ^ (prefixWord ++ tailWord_7782839).sum := by decide
  have hdescent : baseEnd_7782839 < baseStart_7782839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782846 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2]
def baseStart_7782846 : Nat := 118140960795 + 7782846 * 2 ^ 59
def prefixEnd_7782846 : Nat := 4983230072969 + 3 ^ 40 * 7782846 * 2
def baseEnd_7782846 : Nat := 3996340857922361812932349

theorem tailTrace_7782846 : CollatzResearch.WordTrace tailWord_7782846 prefixEnd_7782846 3996340857922361812932349 := by
  unfold tailWord_7782846
  simp only [CollatzResearch.WordTrace]
  refine ⟨35482964245260702639819049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189242475974723747412368261 35482964245260702639819049)
  ·
    refine ⟨26612223183945526979864287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35482964245260702639819049 26612223183945526979864287)
    ·
      refine ⟨39918334775918290469796431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26612223183945526979864287 39918334775918290469796431)
      ·
        refine ⟨59877502163877435704694647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39918334775918290469796431 59877502163877435704694647)
        ·
          refine ⟨89816253245816153557041971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59877502163877435704694647 89816253245816153557041971)
          ·
            refine ⟨134724379868724230335562957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89816253245816153557041971 134724379868724230335562957)
            ·
              refine ⟨50521642450771586375836109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134724379868724230335562957 50521642450771586375836109)
              ·
                refine ⟨18945615919039344890938541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50521642450771586375836109 18945615919039344890938541)
                ·
                  refine ⟨7104605969639754334101953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18945615919039344890938541 7104605969639754334101953)
                  ·
                    refine ⟨5328454477229815750576465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7104605969639754334101953 5328454477229815750576465)
                    ·
                      refine ⟨3996340857922361812932349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5328454477229815750576465 3996340857922361812932349)
                      ·
                        rfl

theorem cell23_7782846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_7782846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782846 prefixEnd_7782846 := by exact prefixLift 7782846
  have htrace : WordTrace (prefixWord ++ tailWord_7782846) baseStart_7782846 baseEnd_7782846 := by
    simpa [prefixWord, tailWord_7782846, baseEnd_7782846] using wordTrace_append hprefix tailTrace_7782846
  have hstable : (prefixWord ++ tailWord_7782846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782846).length < 2 ^ (prefixWord ++ tailWord_7782846).sum := by decide
  have hdescent : baseEnd_7782846 < baseStart_7782846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782856 : List Nat := [2, 1, 3, 1, 3, 3, 3, 1, 2, 4]
def baseStart_7782856 : Nat := 118140960795 + 7782856 * 2 ^ 59
def prefixEnd_7782856 : Nat := 4983230072969 + 3 ^ 40 * 7782856 * 2
def baseEnd_7782856 : Nat := 1332115330909635591269101

theorem tailTrace_7782856 : CollatzResearch.WordTrace tailWord_7782856 prefixEnd_7782856 1332115330909635591269101 := by
  unfold tailWord_7782856
  simp only [CollatzResearch.WordTrace]
  refine ⟨141932039346024696413208211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189242719128032928550944281 141932039346024696413208211)
  ·
    refine ⟨212898059019037044619812317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141932039346024696413208211 212898059019037044619812317)
    ·
      refine ⟨79836772132138891732429619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212898059019037044619812317 79836772132138891732429619)
      ·
        refine ⟨119755158198208337598644429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79836772132138891732429619 119755158198208337598644429)
        ·
          refine ⟨44908184324328126599491661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119755158198208337598644429 44908184324328126599491661)
          ·
            refine ⟨16840569121623047474809373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44908184324328126599491661 16840569121623047474809373)
            ·
              refine ⟨6315213420608642803053515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16840569121623047474809373 6315213420608642803053515)
              ·
                refine ⟨9472820130912964204580273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6315213420608642803053515 9472820130912964204580273)
                ·
                  refine ⟨7104615098184723153435205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9472820130912964204580273 7104615098184723153435205)
                  ·
                    refine ⟨1332115330909635591269101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7104615098184723153435205 1332115330909635591269101)
                    ·
                      rfl

theorem cell23_7782856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_7782856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782856 prefixEnd_7782856 := by exact prefixLift 7782856
  have htrace : WordTrace (prefixWord ++ tailWord_7782856) baseStart_7782856 baseEnd_7782856 := by
    simpa [prefixWord, tailWord_7782856, baseEnd_7782856] using wordTrace_append hprefix tailTrace_7782856
  have hstable : (prefixWord ++ tailWord_7782856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782856).length < 2 ^ (prefixWord ++ tailWord_7782856).sum := by decide
  have hdescent : baseEnd_7782856 < baseStart_7782856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782865 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 2, 7]
def baseStart_7782865 : Nat := 118140960795 + 7782865 * 2 ^ 59
def prefixEnd_7782865 : Nat := 4983230072969 + 3 ^ 40 * 7782865 * 2
def baseEnd_7782865 : Nat := 1332116871351599079531587

theorem tailTrace_7782865 : CollatzResearch.WordTrace tailWord_7782865 prefixEnd_7782865 1332116871351599079531587 := by
  unfold tailWord_7782865
  simp only [CollatzResearch.WordTrace]
  refine ⟨283864406949016787363494049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189242937966011191575662699 283864406949016787363494049)
  ·
    refine ⟨212898305211762590522620537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283864406949016787363494049 212898305211762590522620537)
    ·
      refine ⟨159673728908821942891965403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212898305211762590522620537 159673728908821942891965403)
      ·
        refine ⟨239510593363232914337948105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159673728908821942891965403 239510593363232914337948105)
        ·
          refine ⟨179632945022424685753461079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239510593363232914337948105 179632945022424685753461079)
          ·
            refine ⟨269449417533637028630191619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179632945022424685753461079 269449417533637028630191619)
            ·
              refine ⟨404174126300455542945287429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269449417533637028630191619 404174126300455542945287429)
              ·
                refine ⟨75782648681335414302241393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 404174126300455542945287429 75782648681335414302241393)
                ·
                  refine ⟨56836986511001560726681045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75782648681335414302241393 56836986511001560726681045)
                  ·
                    refine ⟨1332116871351599079531587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56836986511001560726681045 1332116871351599079531587)
                    ·
                      rfl

theorem cell23_7782865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_7782865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782865 prefixEnd_7782865 := by exact prefixLift 7782865
  have htrace : WordTrace (prefixWord ++ tailWord_7782865) baseStart_7782865 baseEnd_7782865 := by
    simpa [prefixWord, tailWord_7782865, baseEnd_7782865] using wordTrace_append hprefix tailTrace_7782865
  have hstable : (prefixWord ++ tailWord_7782865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782865).length < 2 ^ (prefixWord ++ tailWord_7782865).sum := by decide
  have hdescent : baseEnd_7782865 < baseStart_7782865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782869 : List Nat := [1, 3, 2, 3, 1, 4, 2, 7]
def baseStart_7782869 : Nat := 118140960795 + 7782869 * 2 ^ 59
def prefixEnd_7782869 : Nat := 4983230072969 + 3 ^ 40 * 7782869 * 2
def baseEnd_7782869 : Nat := 148013061776941304553509

theorem tailTrace_7782869 : CollatzResearch.WordTrace tailWord_7782869 prefixEnd_7782869 148013061776941304553509 := by
  unfold tailWord_7782869
  simp only [CollatzResearch.WordTrace]
  refine ⟨283864552841002296046639661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189243035227334864031093107 283864552841002296046639661)
  ·
    refine ⟨106449207315375861017489873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283864552841002296046639661 106449207315375861017489873)
    ·
      refine ⟨79836905486531895763117405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106449207315375861017489873 79836905486531895763117405)
      ·
        refine ⟨29938839557449460911169027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79836905486531895763117405 29938839557449460911169027)
        ·
          refine ⟨44908259336174191366753541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29938839557449460911169027 44908259336174191366753541)
          ·
            refine ⟨8420298625532660881266289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44908259336174191366753541 8420298625532660881266289)
            ·
              refine ⟨6315223969149495660949717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8420298625532660881266289 6315223969149495660949717)
              ·
                refine ⟨148013061776941304553509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6315223969149495660949717 148013061776941304553509)
                ·
                  rfl

theorem cell23_7782869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 7].length) (baseStart_7782869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782869 prefixEnd_7782869 := by exact prefixLift 7782869
  have htrace : WordTrace (prefixWord ++ tailWord_7782869) baseStart_7782869 baseEnd_7782869 := by
    simpa [prefixWord, tailWord_7782869, baseEnd_7782869] using wordTrace_append hprefix tailTrace_7782869
  have hstable : (prefixWord ++ tailWord_7782869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782869).length < 2 ^ (prefixWord ++ tailWord_7782869).sum := by decide
  have hdescent : baseEnd_7782869 < baseStart_7782869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782879 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 4, 1, 3]
def baseStart_7782879 : Nat := 118140960795 + 7782879 * 2 ^ 59
def prefixEnd_7782879 : Nat := 4983230072969 + 3 ^ 40 * 7782879 * 2
def baseEnd_7782879 : Nat := 3996357802783960183819697

theorem tailTrace_7782879 : CollatzResearch.WordTrace tailWord_7782879 prefixEnd_7782879 3996357802783960183819697 := by
  unfold tailWord_7782879
  simp only [CollatzResearch.WordTrace]
  refine ⟨283864917570966067754503691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189243278380644045169669127 283864917570966067754503691)
  ·
    refine ⟨425797376356449101631755537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283864917570966067754503691 425797376356449101631755537)
    ·
      refine ⟨319348032267336826223816653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425797376356449101631755537 319348032267336826223816653)
      ·
        refine ⟨119755512100251309833931245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319348032267336826223816653 119755512100251309833931245)
        ·
          refine ⟨44908317037594241187724217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119755512100251309833931245 44908317037594241187724217)
          ·
            refine ⟨33681237778195680890793163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44908317037594241187724217 33681237778195680890793163)
            ·
              refine ⟨50521856667293521336189745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33681237778195680890793163 50521856667293521336189745)
              ·
                refine ⟨37891392500470141002142309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50521856667293521336189745 37891392500470141002142309)
                ·
                  refine ⟨7104636093838151437901683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37891392500470141002142309 7104636093838151437901683)
                  ·
                    refine ⟨10656954140757227156852525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7104636093838151437901683 10656954140757227156852525)
                    ·
                      refine ⟨3996357802783960183819697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10656954140757227156852525 3996357802783960183819697)
                      ·
                        rfl

theorem cell23_7782879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_7782879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782879 prefixEnd_7782879 := by exact prefixLift 7782879
  have htrace : WordTrace (prefixWord ++ tailWord_7782879) baseStart_7782879 baseEnd_7782879 := by
    simpa [prefixWord, tailWord_7782879, baseEnd_7782879] using wordTrace_append hprefix tailTrace_7782879
  have hstable : (prefixWord ++ tailWord_7782879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782879).length < 2 ^ (prefixWord ++ tailWord_7782879).sum := by decide
  have hdescent : baseEnd_7782879 < baseStart_7782879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782913 : List Nat := [1, 2, 4, 1, 3, 1, 4, 1, 2, 1, 3]
def baseStart_7782913 : Nat := 118140960795 + 7782913 * 2 ^ 59
def prefixEnd_7782913 : Nat := 4983230072969 + 3 ^ 40 * 7782913 * 2
def baseEnd_7782913 : Nat := 3996375261126213050794541

theorem tailTrace_7782913 : CollatzResearch.WordTrace tailWord_7782913 prefixEnd_7782913 3996375261126213050794541 := by
  unfold tailWord_7782913
  simp only [CollatzResearch.WordTrace]
  refine ⟨283866157652842891561241393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189244105101895261040827595 283866157652842891561241393)
  ·
    refine ⟨212899618239632168670931045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283866157652842891561241393 212899618239632168670931045)
    ·
      refine ⟨39918678419931031625799571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212899618239632168670931045 39918678419931031625799571)
      ·
        refine ⟨59878017629896547438699357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39918678419931031625799571 59878017629896547438699357)
        ·
          refine ⟨22454256611211205289512259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59878017629896547438699357 22454256611211205289512259)
          ·
            refine ⟨33681384916816807934268389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22454256611211205289512259 33681384916816807934268389)
            ·
              refine ⟨6315259671903151487675323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33681384916816807934268389 6315259671903151487675323)
              ·
                refine ⟨9472889507854727231512985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6315259671903151487675323 9472889507854727231512985)
                ·
                  refine ⟨7104667130891045423634739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9472889507854727231512985 7104667130891045423634739)
                  ·
                    refine ⟨10657000696336568135452109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7104667130891045423634739 10657000696336568135452109)
                    ·
                      refine ⟨3996375261126213050794541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10657000696336568135452109 3996375261126213050794541)
                      ·
                        rfl

theorem cell23_7782913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_7782913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782913 prefixEnd_7782913 := by exact prefixLift 7782913
  have htrace : WordTrace (prefixWord ++ tailWord_7782913) baseStart_7782913 baseEnd_7782913 := by
    simpa [prefixWord, tailWord_7782913, baseEnd_7782913] using wordTrace_append hprefix tailTrace_7782913
  have hstable : (prefixWord ++ tailWord_7782913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782913).length < 2 ^ (prefixWord ++ tailWord_7782913).sum := by decide
  have hdescent : baseEnd_7782913 < baseStart_7782913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782922 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_7782922 : Nat := 118140960795 + 7782922 * 2 ^ 59
def prefixEnd_7782922 : Nat := 4983230072969 + 3 ^ 40 * 7782922 * 2
def baseEnd_7782922 : Nat := 3996379882452103515581999

theorem tailTrace_7782922 : CollatzResearch.WordTrace tailWord_7782922 prefixEnd_7782922 3996379882452103515581999 := by
  unfold tailWord_7782922
  simp only [CollatzResearch.WordTrace]
  refine ⟨70966621477452571524579755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189244323939873524065546013 70966621477452571524579755)
  ·
    refine ⟨106449932216178857286869633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70966621477452571524579755 106449932216178857286869633)
    ·
      refine ⟨79837449162134142965152225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106449932216178857286869633 79837449162134142965152225)
      ·
        refine ⟨59878086871600607223864169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79837449162134142965152225 59878086871600607223864169)
        ·
          refine ⟨44908565153700455417898127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59878086871600607223864169 44908565153700455417898127)
          ·
            refine ⟨67362847730550683126847191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44908565153700455417898127 67362847730550683126847191)
            ·
              refine ⟨101044271595826024690270787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67362847730550683126847191 101044271595826024690270787)
              ·
                refine ⟨151566407393739037035406181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101044271595826024690270787 151566407393739037035406181)
                ·
                  refine ⟨28418701386326069444138659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151566407393739037035406181 28418701386326069444138659)
                  ·
                    refine ⟨42628052079489104166207989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28418701386326069444138659 42628052079489104166207989)
                    ·
                      refine ⟨3996379882452103515581999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42628052079489104166207989 3996379882452103515581999)
                      ·
                        rfl

theorem cell23_7782922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_7782922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782922 prefixEnd_7782922 := by exact prefixLift 7782922
  have htrace : WordTrace (prefixWord ++ tailWord_7782922) baseStart_7782922 baseEnd_7782922 := by
    simpa [prefixWord, tailWord_7782922, baseEnd_7782922] using wordTrace_append hprefix tailTrace_7782922
  have hstable : (prefixWord ++ tailWord_7782922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782922).length < 2 ^ (prefixWord ++ tailWord_7782922).sum := by decide
  have hdescent : baseEnd_7782922 < baseStart_7782922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782923 : List Nat := [1, 1, 1, 1, 7, 3, 1, 2, 1, 3, 2]
def baseStart_7782923 : Nat := 118140960795 + 7782923 * 2 ^ 59
def prefixEnd_7782923 : Nat := 4983230072969 + 3 ^ 40 * 7782923 * 2
def baseEnd_7782923 : Nat := 3996380395932758011669495

theorem tailTrace_7782923 : CollatzResearch.WordTrace tailWord_7782923 prefixEnd_7782923 3996380395932758011669495 := by
  unfold tailWord_7782923
  simp only [CollatzResearch.WordTrace]
  refine ⟨283866522382806663269105423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189244348255204442179403615 283866522382806663269105423)
  ·
    refine ⟨425799783574209994903658135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283866522382806663269105423 425799783574209994903658135)
    ·
      refine ⟨638699675361314992355487203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425799783574209994903658135 638699675361314992355487203)
      ·
        refine ⟨958049513041972488533230805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638699675361314992355487203 958049513041972488533230805)
        ·
          refine ⟨22454285461921230199997597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 958049513041972488533230805 22454285461921230199997597)
          ·
            refine ⟨8420357048220461324999099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22454285461921230199997597 8420357048220461324999099)
            ·
              refine ⟨12630535572330691987498649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8420357048220461324999099 12630535572330691987498649)
              ·
                refine ⟨9472901679248018990623987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12630535572330691987498649 9472901679248018990623987)
                ·
                  refine ⟨14209352518872028485935981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9472901679248018990623987 14209352518872028485935981)
                  ·
                    refine ⟨5328507194577010682225993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14209352518872028485935981 5328507194577010682225993)
                    ·
                      refine ⟨3996380395932758011669495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5328507194577010682225993 3996380395932758011669495)
                      ·
                        rfl

theorem cell23_7782923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 3, 2].length) (baseStart_7782923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782923 prefixEnd_7782923 := by exact prefixLift 7782923
  have htrace : WordTrace (prefixWord ++ tailWord_7782923) baseStart_7782923 baseEnd_7782923 := by
    simpa [prefixWord, tailWord_7782923, baseEnd_7782923] using wordTrace_append hprefix tailTrace_7782923
  have hstable : (prefixWord ++ tailWord_7782923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782923).length < 2 ^ (prefixWord ++ tailWord_7782923).sum := by decide
  have hdescent : baseEnd_7782923 < baseStart_7782923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782936 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 1, 4, 2]
def baseStart_7782936 : Nat := 118140960795 + 7782936 * 2 ^ 59
def prefixEnd_7782936 : Nat := 4983230072969 + 3 ^ 40 * 7782936 * 2
def baseEnd_7782936 : Nat := 3996387071181266460806935

theorem tailTrace_7782936 : CollatzResearch.WordTrace tailWord_7782936 prefixEnd_7782936 3996387071181266460806935 := by
  unfold tailWord_7782936
  simp only [CollatzResearch.WordTrace]
  refine ⟨141933498265879783244664331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189244664354506377659552441 141933498265879783244664331)
  ·
    refine ⟨212900247398819674866996497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141933498265879783244664331 212900247398819674866996497)
    ·
      refine ⟨159675185549114756150247373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212900247398819674866996497 159675185549114756150247373)
      ·
        refine ⟨59878194580918033556342765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159675185549114756150247373 59878194580918033556342765)
        ·
          refine ⟨22454322967844262583628537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59878194580918033556342765 22454322967844262583628537)
          ·
            refine ⟨16840742225883196937721403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22454322967844262583628537 16840742225883196937721403)
            ·
              refine ⟨25261113338824795406582105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16840742225883196937721403 25261113338824795406582105)
              ·
                refine ⟨18945835004118596554936579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25261113338824795406582105 18945835004118596554936579)
                ·
                  refine ⟨28418752506177894832404869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18945835004118596554936579 28418752506177894832404869)
                  ·
                    refine ⟨5328516094908355281075913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28418752506177894832404869 5328516094908355281075913)
                    ·
                      refine ⟨3996387071181266460806935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5328516094908355281075913 3996387071181266460806935)
                      ·
                        rfl

theorem cell23_7782936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_7782936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782936 prefixEnd_7782936 := by exact prefixLift 7782936
  have htrace : WordTrace (prefixWord ++ tailWord_7782936) baseStart_7782936 baseEnd_7782936 := by
    simpa [prefixWord, tailWord_7782936, baseEnd_7782936] using wordTrace_append hprefix tailTrace_7782936
  have hstable : (prefixWord ++ tailWord_7782936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782936).length < 2 ^ (prefixWord ++ tailWord_7782936).sum := by decide
  have hdescent : baseEnd_7782936 < baseStart_7782936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782966 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_7782966 : Nat := 118140960795 + 7782966 * 2 ^ 59
def prefixEnd_7782966 : Nat := 4983230072969 + 3 ^ 40 * 7782966 * 2
def baseEnd_7782966 : Nat := 3996402475600901343431797

theorem tailTrace_7782966 : CollatzResearch.WordTrace tailWord_7782966 prefixEnd_7782966 3996402475600901343431797 := by
  unfold tailWord_7782966
  simp only [CollatzResearch.WordTrace]
  refine ⟨17741755670103180100807547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189245393814433921075280501 17741755670103180100807547)
  ·
    refine ⟨26612633505154770151211321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17741755670103180100807547 26612633505154770151211321)
    ·
      refine ⟨19959475128866077613408491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26612633505154770151211321 19959475128866077613408491)
      ·
        refine ⟨29939212693299116420112737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19959475128866077613408491 29939212693299116420112737)
        ·
          refine ⟨22454409519974337315084553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29939212693299116420112737 22454409519974337315084553)
          ·
            refine ⟨16840807139980752986313415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22454409519974337315084553 16840807139980752986313415)
            ·
              refine ⟨25261210709971129479470123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16840807139980752986313415 25261210709971129479470123)
              ·
                refine ⟨37891816064956694219205185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25261210709971129479470123 37891816064956694219205185)
                ·
                  refine ⟨28418862048717520664403889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37891816064956694219205185 28418862048717520664403889)
                  ·
                    refine ⟨21314146536538140498302917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28418862048717520664403889 21314146536538140498302917)
                    ·
                      refine ⟨3996402475600901343431797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21314146536538140498302917 3996402475600901343431797)
                      ·
                        rfl

theorem cell23_7782966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_7782966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782966 prefixEnd_7782966 := by exact prefixLift 7782966
  have htrace : WordTrace (prefixWord ++ tailWord_7782966) baseStart_7782966 baseEnd_7782966 := by
    simpa [prefixWord, tailWord_7782966, baseEnd_7782966] using wordTrace_append hprefix tailTrace_7782966
  have hstable : (prefixWord ++ tailWord_7782966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782966).length < 2 ^ (prefixWord ++ tailWord_7782966).sum := by decide
  have hdescent : baseEnd_7782966 < baseStart_7782966 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7782969 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 2, 3, 3]
def baseStart_7782969 : Nat := 118140960795 + 7782969 * 2 ^ 59
def prefixEnd_7782969 : Nat := 4983230072969 + 3 ^ 40 * 7782969 * 2
def baseEnd_7782969 : Nat := 3996404016042864831694283

theorem tailTrace_7782969 : CollatzResearch.WordTrace tailWord_7782969 prefixEnd_7782969 3996404016042864831694283 := by
  unfold tailWord_7782969
  simp only [CollatzResearch.WordTrace]
  refine ⟨283868200140640013125279961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189245466760426675416853307 283868200140640013125279961)
  ·
    refine ⟨212901150105480009843959971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283868200140640013125279961 212901150105480009843959971)
    ·
      refine ⟨319351725158220014765939957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212901150105480009843959971 319351725158220014765939957)
      ·
        refine ⟨29939224233583126384306871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 319351725158220014765939957 29939224233583126384306871)
        ·
          refine ⟨44908836350374689576460307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29939224233583126384306871 44908836350374689576460307)
          ·
            refine ⟨67363254525562034364690461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44908836350374689576460307 67363254525562034364690461)
            ·
              refine ⟨25261220447085762886758923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67363254525562034364690461 25261220447085762886758923)
              ·
                refine ⟨37891830670628644330138385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25261220447085762886758923 37891830670628644330138385)
                ·
                  refine ⟨28418873002971483247603789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37891830670628644330138385 28418873002971483247603789)
                  ·
                    refine ⟨10657077376114306217851421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28418873002971483247603789 10657077376114306217851421)
                    ·
                      refine ⟨3996404016042864831694283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10657077376114306217851421 3996404016042864831694283)
                      ·
                        rfl

theorem cell23_7782969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_7782969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7782969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7782969 prefixEnd_7782969 := by exact prefixLift 7782969
  have htrace : WordTrace (prefixWord ++ tailWord_7782969) baseStart_7782969 baseEnd_7782969 := by
    simpa [prefixWord, tailWord_7782969, baseEnd_7782969] using wordTrace_append hprefix tailTrace_7782969
  have hstable : (prefixWord ++ tailWord_7782969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7782969).length < 2 ^ (prefixWord ++ tailWord_7782969).sum := by decide
  have hdescent : baseEnd_7782969 < baseStart_7782969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7782969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783052 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 1, 1, 8]
def baseStart_7783052 : Nat := 118140960795 + 7783052 * 2 ^ 59
def prefixEnd_7783052 : Nat := 4983230072969 + 3 ^ 40 * 7783052 * 2
def baseEnd_7783052 : Nat := 3996446634937188006956401

theorem tailTrace_7783052 : CollatzResearch.WordTrace tailWord_7783052 prefixEnd_7783052 3996446634937188006956401 := by
  unfold tailWord_7783052
  simp only [CollatzResearch.WordTrace]
  refine ⟨141935613699669659150275705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189247484932892878867034273 141935613699669659150275705)
  ·
    refine ⟨106451710274752244362706779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141935613699669659150275705 106451710274752244362706779)
    ·
      refine ⟨159677565412128366544060169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106451710274752244362706779 159677565412128366544060169)
      ·
        refine ⟨119758174059096274908045127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159677565412128366544060169 119758174059096274908045127)
        ·
          refine ⟨179637261088644412362067691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119758174059096274908045127 179637261088644412362067691)
          ·
            refine ⟨269455891632966618543101537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179637261088644412362067691 269455891632966618543101537)
            ·
              refine ⟨202091918724724963907326153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269455891632966618543101537 202091918724724963907326153)
              ·
                refine ⟨151568939043543722930494615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202091918724724963907326153 151568939043543722930494615)
                ·
                  refine ⟨227353408565315584395741923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151568939043543722930494615 227353408565315584395741923)
                  ·
                    refine ⟨341030112847973376593612885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 227353408565315584395741923 341030112847973376593612885)
                    ·
                      refine ⟨3996446634937188006956401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 341030112847973376593612885 3996446634937188006956401)
                      ·
                        rfl

theorem cell23_7783052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_7783052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783052 prefixEnd_7783052 := by exact prefixLift 7783052
  have htrace : WordTrace (prefixWord ++ tailWord_7783052) baseStart_7783052 baseEnd_7783052 := by
    simpa [prefixWord, tailWord_7783052, baseEnd_7783052] using wordTrace_append hprefix tailTrace_7783052
  have hstable : (prefixWord ++ tailWord_7783052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783052).length < 2 ^ (prefixWord ++ tailWord_7783052).sum := by decide
  have hdescent : baseEnd_7783052 < baseStart_7783052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783103 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 2, 3, 2]
def baseStart_7783103 : Nat := 118140960795 + 7783103 * 2 ^ 59
def prefixEnd_7783103 : Nat := 4983230072969 + 3 ^ 40 * 7783103 * 2
def baseEnd_7783103 : Nat := 3996472822450567307418667

theorem tailTrace_7783103 : CollatzResearch.WordTrace tailWord_7783103 prefixEnd_7783103 3996472822450567307418667 := by
  unfold tailWord_7783103
  simp only [CollatzResearch.WordTrace]
  refine ⟨283873087522154554010657963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189248725014769702673771975 283873087522154554010657963)
  ·
    refine ⟨425809631283231831015986945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283873087522154554010657963 425809631283231831015986945)
    ·
      refine ⟨319357223462423873261990209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425809631283231831015986945 319357223462423873261990209)
      ·
        refine ⟨239517917596817904946492657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319357223462423873261990209 239517917596817904946492657)
        ·
          refine ⟨179638438197613428709869493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239517917596817904946492657 179638438197613428709869493)
          ·
            refine ⟨16841103581026258941550265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179638438197613428709869493 16841103581026258941550265)
            ·
              refine ⟨12630827685769694206162699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16841103581026258941550265 12630827685769694206162699)
              ·
                refine ⟨18946241528654541309244049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12630827685769694206162699 18946241528654541309244049)
                ·
                  refine ⟨14209681146490905981933037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18946241528654541309244049 14209681146490905981933037)
                  ·
                    refine ⟨5328630429934089743224889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14209681146490905981933037 5328630429934089743224889)
                    ·
                      refine ⟨3996472822450567307418667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5328630429934089743224889 3996472822450567307418667)
                      ·
                        rfl

theorem cell23_7783103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 3, 2].length) (baseStart_7783103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783103 prefixEnd_7783103 := by exact prefixLift 7783103
  have htrace : WordTrace (prefixWord ++ tailWord_7783103) baseStart_7783103 baseEnd_7783103 := by
    simpa [prefixWord, tailWord_7783103, baseEnd_7783103] using wordTrace_append hprefix tailTrace_7783103
  have hstable : (prefixWord ++ tailWord_7783103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783103).length < 2 ^ (prefixWord ++ tailWord_7783103).sum := by decide
  have hdescent : baseEnd_7783103 < baseStart_7783103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783127 : List Nat := [1, 1, 3, 2, 1, 6, 2, 2, 1, 1, 3]
def baseStart_7783127 : Nat := 118140960795 + 7783127 * 2 ^ 59
def prefixEnd_7783127 : Nat := 4983230072969 + 3 ^ 40 * 7783127 * 2
def baseEnd_7783127 : Nat := 3996485145986275213518557

theorem tailTrace_7783127 : CollatzResearch.WordTrace tailWord_7783127 prefixEnd_7783127 3996485145986275213518557 := by
  unfold tailWord_7783127
  simp only [CollatzResearch.WordTrace]
  refine ⟨283873962874067606109531635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189249308582711737406354423 283873962874067606109531635)
  ·
    refine ⟨425810944311101409164297453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283873962874067606109531635 425810944311101409164297453)
    ·
      refine ⟨159679104116663028436611545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425810944311101409164297453 159679104116663028436611545)
      ·
        refine ⟨119759328087497271327458659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159679104116663028436611545 119759328087497271327458659)
        ·
          refine ⟨179638992131245906991187989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119759328087497271327458659 179638992131245906991187989)
          ·
            refine ⟨8420577756152151890211937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 179638992131245906991187989 8420577756152151890211937)
            ·
              refine ⟨6315433317114113917658953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8420577756152151890211937 6315433317114113917658953)
              ·
                refine ⟨4736574987835585438244215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6315433317114113917658953 4736574987835585438244215)
                ·
                  refine ⟨7104862481753378157366323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4736574987835585438244215 7104862481753378157366323)
                  ·
                    refine ⟨10657293722630067236049485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7104862481753378157366323 10657293722630067236049485)
                    ·
                      refine ⟨3996485145986275213518557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10657293722630067236049485 3996485145986275213518557)
                      ·
                        rfl

theorem cell23_7783127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_7783127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783127 prefixEnd_7783127 := by exact prefixLift 7783127
  have htrace : WordTrace (prefixWord ++ tailWord_7783127) baseStart_7783127 baseEnd_7783127 := by
    simpa [prefixWord, tailWord_7783127, baseEnd_7783127] using wordTrace_append hprefix tailTrace_7783127
  have hstable : (prefixWord ++ tailWord_7783127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783127).length < 2 ^ (prefixWord ++ tailWord_7783127).sum := by decide
  have hdescent : baseEnd_7783127 < baseStart_7783127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783129 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 4]
def baseStart_7783129 : Nat := 118140960795 + 7783129 * 2 ^ 59
def prefixEnd_7783129 : Nat := 4983230072969 + 3 ^ 40 * 7783129 * 2
def baseEnd_7783129 : Nat := 3996486172947584205693547

theorem tailTrace_7783129 : CollatzResearch.WordTrace tailWord_7783129 prefixEnd_7783129 3996486172947584205693547 := by
  unfold tailWord_7783129
  simp only [CollatzResearch.WordTrace]
  refine ⟨283874035820060360451104441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189249357213373573634069627 283874035820060360451104441)
  ·
    refine ⟨212905526865045270338328331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283874035820060360451104441 212905526865045270338328331)
    ·
      refine ⟨319358290297567905507492497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212905526865045270338328331 319358290297567905507492497)
      ·
        refine ⟨239518717723175929130619373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319358290297567905507492497 239518717723175929130619373)
        ·
          refine ⟨89819519146190973423982265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239518717723175929130619373 89819519146190973423982265)
          ·
            refine ⟨67364639359643230067986699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89819519146190973423982265 67364639359643230067986699)
            ·
              refine ⟨101046959039464845101980049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67364639359643230067986699 101046959039464845101980049)
              ·
                refine ⟨75785219279598633826485037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101046959039464845101980049 75785219279598633826485037)
                ·
                  refine ⟨28419457229849487684931889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75785219279598633826485037 28419457229849487684931889)
                  ·
                    refine ⟨21314592922387115763698917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28419457229849487684931889 21314592922387115763698917)
                    ·
                      refine ⟨3996486172947584205693547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21314592922387115763698917 3996486172947584205693547)
                      ·
                        rfl

theorem cell23_7783129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_7783129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783129 prefixEnd_7783129 := by exact prefixLift 7783129
  have htrace : WordTrace (prefixWord ++ tailWord_7783129) baseStart_7783129 baseEnd_7783129 := by
    simpa [prefixWord, tailWord_7783129, baseEnd_7783129] using wordTrace_append hprefix tailTrace_7783129
  have hstable : (prefixWord ++ tailWord_7783129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783129).length < 2 ^ (prefixWord ++ tailWord_7783129).sum := by decide
  have hdescent : baseEnd_7783129 < baseStart_7783129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783150 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 3, 2, 2]
def baseStart_7783150 : Nat := 118140960795 + 7783150 * 2 ^ 59
def prefixEnd_7783150 : Nat := 4983230072969 + 3 ^ 40 * 7783150 * 2
def baseEnd_7783150 : Nat := 3996496956041328623530951

theorem tailTrace_7783150 : CollatzResearch.WordTrace tailWord_7783150 prefixEnd_7783150 3996496956041328623530951 := by
  unfold tailWord_7783150
  simp only [CollatzResearch.WordTrace]
  refine ⟨35484350219123035129702363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189249867835322854025079269 35484350219123035129702363)
  ·
    refine ⟨53226525328684552694553545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35484350219123035129702363 53226525328684552694553545)
    ·
      refine ⟨39919893996513414520915159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53226525328684552694553545 39919893996513414520915159)
      ·
        refine ⟨59879840994770121781372739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39919893996513414520915159 59879840994770121781372739)
        ·
          refine ⟨89819761492155182672059109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59879840994770121781372739 89819761492155182672059109)
          ·
            refine ⟨16841205279779096751011083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89819761492155182672059109 16841205279779096751011083)
            ·
              refine ⟨25261807919668645126516625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16841205279779096751011083 25261807919668645126516625)
              ·
                refine ⟨18946355939751483844887469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25261807919668645126516625 18946355939751483844887469)
                ·
                  refine ⟨7104883477406806441832801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18946355939751483844887469 7104883477406806441832801)
                  ·
                    refine ⟨5328662608055104831374601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7104883477406806441832801 5328662608055104831374601)
                    ·
                      refine ⟨3996496956041328623530951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5328662608055104831374601 3996496956041328623530951)
                      ·
                        rfl

theorem cell23_7783150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_7783150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783150 prefixEnd_7783150 := by exact prefixLift 7783150
  have htrace : WordTrace (prefixWord ++ tailWord_7783150) baseStart_7783150 baseEnd_7783150 := by
    simpa [prefixWord, tailWord_7783150, baseEnd_7783150] using wordTrace_append hprefix tailTrace_7783150
  have hstable : (prefixWord ++ tailWord_7783150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783150).length < 2 ^ (prefixWord ++ tailWord_7783150).sum := by decide
  have hdescent : baseEnd_7783150 < baseStart_7783150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783170 : List Nat := [3, 4, 1, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_7783170 : Nat := 118140960795 + 7783170 * 2 ^ 59
def prefixEnd_7783170 : Nat := 4983230072969 + 3 ^ 40 * 7783170 * 2
def baseEnd_7783170 : Nat := 3996507225654418545280859

theorem tailTrace_7783170 : CollatzResearch.WordTrace tailWord_7783170 prefixEnd_7783170 3996507225654418545280859 := by
  unfold tailWord_7783170
  simp only [CollatzResearch.WordTrace]
  refine ⟨70968882803227956113336741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189250354141941216302231309 70968882803227956113336741)
  ·
    refine ⟨13306665525605241771250639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70968882803227956113336741 13306665525605241771250639)
    ·
      refine ⟨19959998288407862656875959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13306665525605241771250639 19959998288407862656875959)
      ·
        refine ⟨29939997432611793985313939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19959998288407862656875959 29939997432611793985313939)
        ·
          refine ⟨44909996148917690977970909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29939997432611793985313939 44909996148917690977970909)
          ·
            refine ⟨16841248555844134116739091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44909996148917690977970909 16841248555844134116739091)
            ·
              refine ⟨25261872833766201175108637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16841248555844134116739091 25261872833766201175108637)
              ·
                refine ⟨9473202312662325440665739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25261872833766201175108637 9473202312662325440665739)
                ·
                  refine ⟨14209803468993488160998609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9473202312662325440665739 14209803468993488160998609)
                  ·
                    refine ⟨10657352601745116120748957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14209803468993488160998609 10657352601745116120748957)
                    ·
                      refine ⟨3996507225654418545280859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10657352601745116120748957 3996507225654418545280859)
                      ·
                        rfl

theorem cell23_7783170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_7783170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783170 prefixEnd_7783170 := by exact prefixLift 7783170
  have htrace : WordTrace (prefixWord ++ tailWord_7783170) baseStart_7783170 baseEnd_7783170 := by
    simpa [prefixWord, tailWord_7783170, baseEnd_7783170] using wordTrace_append hprefix tailTrace_7783170
  have hstable : (prefixWord ++ tailWord_7783170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783170).length < 2 ^ (prefixWord ++ tailWord_7783170).sum := by decide
  have hdescent : baseEnd_7783170 < baseStart_7783170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783197 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 1, 2, 4]
def baseStart_7783197 : Nat := 118140960795 + 7783197 * 2 ^ 59
def prefixEnd_7783197 : Nat := 4983230072969 + 3 ^ 40 * 7783197 * 2
def baseEnd_7783197 : Nat := 3996521089632089939643235

theorem tailTrace_7783197 : CollatzResearch.WordTrace tailWord_7783197 prefixEnd_7783197 3996521089632089939643235 := by
  unfold tailWord_7783197
  simp only [CollatzResearch.WordTrace]
  refine ⟨283876515983814008064579845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189251010655876005376386563 283876515983814008064579845)
  ·
    refine ⟨53226846746965126512108721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283876515983814008064579845 53226846746965126512108721)
    ·
      refine ⟨39920135060223844884081541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53226846746965126512108721 39920135060223844884081541)
      ·
        refine ⟨7485025323791970915765289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39920135060223844884081541 7485025323791970915765289)
        ·
          refine ⟨5613768992843978186823967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7485025323791970915765289 5613768992843978186823967)
          ·
            refine ⟨8420653489265967280235951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5613768992843978186823967 8420653489265967280235951)
            ·
              refine ⟨12630980233898950920353927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8420653489265967280235951 12630980233898950920353927)
              ·
                refine ⟨18946470350848426380530891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12630980233898950920353927 18946470350848426380530891)
                ·
                  refine ⟨28419705526272639570796337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18946470350848426380530891 28419705526272639570796337)
                  ·
                    refine ⟨21314779144704479678097253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28419705526272639570796337 21314779144704479678097253)
                    ·
                      refine ⟨3996521089632089939643235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21314779144704479678097253 3996521089632089939643235)
                      ·
                        rfl

theorem cell23_7783197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_7783197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783197 prefixEnd_7783197 := by exact prefixLift 7783197
  have htrace : WordTrace (prefixWord ++ tailWord_7783197) baseStart_7783197 baseEnd_7783197 := by
    simpa [prefixWord, tailWord_7783197, baseEnd_7783197] using wordTrace_append hprefix tailTrace_7783197
  have hstable : (prefixWord ++ tailWord_7783197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783197).length < 2 ^ (prefixWord ++ tailWord_7783197).sum := by decide
  have hdescent : baseEnd_7783197 < baseStart_7783197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783209 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 4, 1, 5]
def baseStart_7783209 : Nat := 118140960795 + 7783209 * 2 ^ 59
def prefixEnd_7783209 : Nat := 4983230072969 + 3 ^ 40 * 7783209 * 2
def baseEnd_7783209 : Nat := 3996527251399943892693179

theorem tailTrace_7783209 : CollatzResearch.WordTrace tailWord_7783209 prefixEnd_7783209 3996527251399943892693179 := by
  unfold tailWord_7783209
  simp only [CollatzResearch.WordTrace]
  refine ⟨283876953659770534114016681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189251302439847022742677787 283876953659770534114016681)
  ·
    refine ⟨212907715244827900585512511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283876953659770534114016681 212907715244827900585512511)
    ·
      refine ⟨319361572867241850878268767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212907715244827900585512511 319361572867241850878268767)
      ·
        refine ⟨479042359300862776317403151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319361572867241850878268767 479042359300862776317403151)
        ·
          refine ⟨718563538951294164476104727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479042359300862776317403151 718563538951294164476104727)
          ·
            refine ⟨1077845308426941246714157091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718563538951294164476104727 1077845308426941246714157091)
            ·
              refine ⟨1616767962640411870071235637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077845308426941246714157091 1616767962640411870071235637)
              ·
                refine ⟨151571996497538612819178341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1616767962640411870071235637 151571996497538612819178341)
                ·
                  refine ⟨28419749343288489903595939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151571996497538612819178341 28419749343288489903595939)
                  ·
                    refine ⟨42629624014932734855393909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28419749343288489903595939 42629624014932734855393909)
                    ·
                      refine ⟨3996527251399943892693179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42629624014932734855393909 3996527251399943892693179)
                      ·
                        rfl

theorem cell23_7783209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_7783209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783209 prefixEnd_7783209 := by exact prefixLift 7783209
  have htrace : WordTrace (prefixWord ++ tailWord_7783209) baseStart_7783209 baseEnd_7783209 := by
    simpa [prefixWord, tailWord_7783209, baseEnd_7783209] using wordTrace_append hprefix tailTrace_7783209
  have hstable : (prefixWord ++ tailWord_7783209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783209).length < 2 ^ (prefixWord ++ tailWord_7783209).sum := by decide
  have hdescent : baseEnd_7783209 < baseStart_7783209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783223 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 6, 2, 2]
def baseStart_7783223 : Nat := 118140960795 + 7783223 * 2 ^ 59
def prefixEnd_7783223 : Nat := 4983230072969 + 3 ^ 40 * 7783223 * 2
def baseEnd_7783223 : Nat := 3996534440129106837918115

theorem tailTrace_7783223 : CollatzResearch.WordTrace tailWord_7783223 prefixEnd_7783223 3996534440129106837918115 := by
  unfold tailWord_7783223
  simp only [CollatzResearch.WordTrace]
  refine ⟨283877464281719814505026323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189251642854479876336684215 283877464281719814505026323)
  ·
    refine ⟨425816196422579721757539485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283877464281719814505026323 425816196422579721757539485)
    ·
      refine ⟨159681073658467395659077307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425816196422579721757539485 159681073658467395659077307)
      ·
        refine ⟨239521610487701093488615961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159681073658467395659077307 239521610487701093488615961)
        ·
          refine ⟨179641207865775820116461971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239521610487701093488615961 179641207865775820116461971)
          ·
            refine ⟨269461811798663730174692957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179641207865775820116461971 269461811798663730174692957)
            ·
              refine ⟨101048179424498898815509859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269461811798663730174692957 101048179424498898815509859)
              ·
                refine ⟨151572269136748348223264789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101048179424498898815509859 151572269136748348223264789)
                ·
                  refine ⟨7104950115785078822965537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151572269136748348223264789 7104950115785078822965537)
                  ·
                    refine ⟨5328712586838809117224153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7104950115785078822965537 5328712586838809117224153)
                    ·
                      refine ⟨3996534440129106837918115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5328712586838809117224153 3996534440129106837918115)
                      ·
                        rfl

theorem cell23_7783223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 2, 2].length) (baseStart_7783223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783223 prefixEnd_7783223 := by exact prefixLift 7783223
  have htrace : WordTrace (prefixWord ++ tailWord_7783223) baseStart_7783223 baseEnd_7783223 := by
    simpa [prefixWord, tailWord_7783223, baseEnd_7783223] using wordTrace_append hprefix tailTrace_7783223
  have hstable : (prefixWord ++ tailWord_7783223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783223).length < 2 ^ (prefixWord ++ tailWord_7783223).sum := by decide
  have hdescent : baseEnd_7783223 < baseStart_7783223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783239 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_7783239 : Nat := 118140960795 + 7783239 * 2 ^ 59
def prefixEnd_7783239 : Nat := 4983230072969 + 3 ^ 40 * 7783239 * 2
def baseEnd_7783239 : Nat := 3996542655819578775318041

theorem tailTrace_7783239 : CollatzResearch.WordTrace tailWord_7783239 prefixEnd_7783239 3996542655819578775318041 := by
  unfold tailWord_7783239
  simp only [CollatzResearch.WordTrace]
  refine ⟨283878047849661849237608771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189252031899774566158405847 283878047849661849237608771)
  ·
    refine ⟨425817071774492773856413157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283878047849661849237608771 425817071774492773856413157)
    ·
      refine ⟨79840700957717395098077467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425817071774492773856413157 79840700957717395098077467)
      ·
        refine ⟨119761051436576092647116201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79840700957717395098077467 119761051436576092647116201)
        ·
          refine ⟨89820788577432069485337151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119761051436576092647116201 89820788577432069485337151)
          ·
            refine ⟨134731182866148104228005727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89820788577432069485337151 134731182866148104228005727)
            ·
              refine ⟨202096774299222156342008591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134731182866148104228005727 202096774299222156342008591)
              ·
                refine ⟨303145161448833234513012887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202096774299222156342008591 303145161448833234513012887)
                ·
                  refine ⟨454717742173249851769519331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303145161448833234513012887 454717742173249851769519331)
                  ·
                    refine ⟨682076613259874777654278997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 454717742173249851769519331 682076613259874777654278997)
                    ·
                      refine ⟨3996542655819578775318041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 682076613259874777654278997 3996542655819578775318041)
                      ·
                        rfl

theorem cell23_7783239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_7783239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783239 prefixEnd_7783239 := by exact prefixLift 7783239
  have htrace : WordTrace (prefixWord ++ tailWord_7783239) baseStart_7783239 baseEnd_7783239 := by
    simpa [prefixWord, tailWord_7783239, baseEnd_7783239] using wordTrace_append hprefix tailTrace_7783239
  have hstable : (prefixWord ++ tailWord_7783239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783239).length < 2 ^ (prefixWord ++ tailWord_7783239).sum := by decide
  have hdescent : baseEnd_7783239 < baseStart_7783239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783240 : List Nat := [2, 1, 3, 1, 1, 3, 2, 4, 2, 2, 2]
def baseStart_7783240 : Nat := 118140960795 + 7783240 * 2 ^ 59
def prefixEnd_7783240 : Nat := 4983230072969 + 3 ^ 40 * 7783240 * 2
def baseEnd_7783240 : Nat := 3996543169300233271405537

theorem tailTrace_7783240 : CollatzResearch.WordTrace tailWord_7783240 prefixEnd_7783240 3996543169300233271405537 := by
  unfold tailWord_7783240
  simp only [CollatzResearch.WordTrace]
  refine ⟨141939042161329113204197587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189252056215105484272263449 141939042161329113204197587)
  ·
    refine ⟨212908563241993669806296381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141939042161329113204197587 212908563241993669806296381)
    ·
      refine ⟨79840711215747626177361143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212908563241993669806296381 79840711215747626177361143)
      ·
        refine ⟨119761066823621439266041715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79840711215747626177361143 119761066823621439266041715)
        ·
          refine ⟨179641600235432158899062573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119761066823621439266041715 179641600235432158899062573)
          ·
            refine ⟨67365600088287059587148465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179641600235432158899062573 67365600088287059587148465)
            ·
              refine ⟨50524200066215294690361349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67365600088287059587148465 50524200066215294690361349)
              ·
                refine ⟨9473287512415367754442753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50524200066215294690361349 9473287512415367754442753)
                ·
                  refine ⟨7104965634311525815832065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9473287512415367754442753 7104965634311525815832065)
                  ·
                    refine ⟨5328724225733644361874049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7104965634311525815832065 5328724225733644361874049)
                    ·
                      refine ⟨3996543169300233271405537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5328724225733644361874049 3996543169300233271405537)
                      ·
                        rfl

theorem cell23_7783240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_7783240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783240 prefixEnd_7783240 := by exact prefixLift 7783240
  have htrace : WordTrace (prefixWord ++ tailWord_7783240) baseStart_7783240 baseEnd_7783240 := by
    simpa [prefixWord, tailWord_7783240, baseEnd_7783240] using wordTrace_append hprefix tailTrace_7783240
  have hstable : (prefixWord ++ tailWord_7783240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783240).length < 2 ^ (prefixWord ++ tailWord_7783240).sum := by decide
  have hdescent : baseEnd_7783240 < baseStart_7783240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783256 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 2, 3, 3]
def baseStart_7783256 : Nat := 118140960795 + 7783256 * 2 ^ 59
def prefixEnd_7783256 : Nat := 4983230072969 + 3 ^ 40 * 7783256 * 2
def baseEnd_7783256 : Nat := 3996551384990705208805463

theorem tailTrace_7783256 : CollatzResearch.WordTrace tailWord_7783256 prefixEnd_7783256 3996551384990705208805463 := by
  unfold tailWord_7783256
  simp only [CollatzResearch.WordTrace]
  refine ⟨141939333945300130570488811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189252445260400174093985081 141939333945300130570488811)
  ·
    refine ⟨212909000917950195855733217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141939333945300130570488811 212909000917950195855733217)
    ·
      refine ⟨159681750688462646891799913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212909000917950195855733217 159681750688462646891799913)
      ·
        refine ⟨119761313016346985168849935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159681750688462646891799913 119761313016346985168849935)
        ·
          refine ⟨179641969524520477753274903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119761313016346985168849935 179641969524520477753274903)
          ·
            refine ⟨269462954286780716629912355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179641969524520477753274903 269462954286780716629912355)
            ·
              refine ⟨404194431430171074944868533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269462954286780716629912355 404194431430171074944868533)
              ·
                refine ⟨37893227946578538276081425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 404194431430171074944868533 37893227946578538276081425)
                ·
                  refine ⟨28419920959933903707061069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37893227946578538276081425 28419920959933903707061069)
                  ·
                    refine ⟨10657470359975213890147901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28419920959933903707061069 10657470359975213890147901)
                    ·
                      refine ⟨3996551384990705208805463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10657470359975213890147901 3996551384990705208805463)
                      ·
                        rfl

theorem cell23_7783256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_7783256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783256 prefixEnd_7783256 := by exact prefixLift 7783256
  have htrace : WordTrace (prefixWord ++ tailWord_7783256) baseStart_7783256 baseEnd_7783256 := by
    simpa [prefixWord, tailWord_7783256, baseEnd_7783256] using wordTrace_append hprefix tailTrace_7783256
  have hstable : (prefixWord ++ tailWord_7783256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783256).length < 2 ^ (prefixWord ++ tailWord_7783256).sum := by decide
  have hdescent : baseEnd_7783256 < baseStart_7783256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783257 : List Nat := [1, 2, 1, 2, 2, 4, 4, 1, 2, 2, 2]
def baseStart_7783257 : Nat := 118140960795 + 7783257 * 2 ^ 59
def prefixEnd_7783257 : Nat := 4983230072969 + 3 ^ 40 * 7783257 * 2
def baseEnd_7783257 : Nat := 3996551898471359704892959

theorem tailTrace_7783257 : CollatzResearch.WordTrace tailWord_7783257 prefixEnd_7783257 3996551898471359704892959 := by
  unfold tailWord_7783257
  simp only [CollatzResearch.WordTrace]
  refine ⟨283878704363596638311764025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189252469575731092207842683 283878704363596638311764025)
  ·
    refine ⟨212909028272697478733823019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283878704363596638311764025 212909028272697478733823019)
    ·
      refine ⟨319363542409046218100734529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212909028272697478733823019 319363542409046218100734529)
      ·
        refine ⟨239522656806784663575550897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319363542409046218100734529 239522656806784663575550897)
        ·
          refine ⟨179641992605088497681663173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239522656806784663575550897 179641992605088497681663173)
          ·
            refine ⟨33682873613454093315311845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179641992605088497681663173 33682873613454093315311845)
            ·
              refine ⟨6315538802522642496620971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33682873613454093315311845 6315538802522642496620971)
              ·
                refine ⟨9473308203783963744931457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6315538802522642496620971 9473308203783963744931457)
                ·
                  refine ⟨7104981152837972808698593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9473308203783963744931457 7104981152837972808698593)
                  ·
                    refine ⟨5328735864628479606523945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7104981152837972808698593 5328735864628479606523945)
                    ·
                      refine ⟨3996551898471359704892959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5328735864628479606523945 3996551898471359704892959)
                      ·
                        rfl

theorem cell23_7783257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 2, 2, 2].length) (baseStart_7783257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783257 prefixEnd_7783257 := by exact prefixLift 7783257
  have htrace : WordTrace (prefixWord ++ tailWord_7783257) baseStart_7783257 baseEnd_7783257 := by
    simpa [prefixWord, tailWord_7783257, baseEnd_7783257] using wordTrace_append hprefix tailTrace_7783257
  have hstable : (prefixWord ++ tailWord_7783257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783257).length < 2 ^ (prefixWord ++ tailWord_7783257).sum := by decide
  have hdescent : baseEnd_7783257 < baseStart_7783257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783296 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 4]
def baseStart_7783296 : Nat := 118140960795 + 7783296 * 2 ^ 59
def prefixEnd_7783296 : Nat := 4983230072969 + 3 ^ 40 * 7783296 * 2
def baseEnd_7783296 : Nat := 3996571924216885052305279

theorem tailTrace_7783296 : CollatzResearch.WordTrace tailWord_7783296 prefixEnd_7783296 3996571924216885052305279 := by
  unfold tailWord_7783296
  simp only [CollatzResearch.WordTrace]
  refine ⟨141940063405227673986216871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189253417873636898648289161 141940063405227673986216871)
  ·
    refine ⟨212910095107841510979325307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141940063405227673986216871 212910095107841510979325307)
    ·
      refine ⟨319365142661762266468987961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212910095107841510979325307 319365142661762266468987961)
      ·
        refine ⟨239523856996321699851740971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319365142661762266468987961 239523856996321699851740971)
        ·
          refine ⟨359285785494482549777611457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239523856996321699851740971 359285785494482549777611457)
          ·
            refine ⟨269464339120861912333208593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359285785494482549777611457 269464339120861912333208593)
            ·
              refine ⟨202098254340646434249906445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269464339120861912333208593 202098254340646434249906445)
              ·
                refine ⟨75786845377742412843714917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202098254340646434249906445 75786845377742412843714917)
                ·
                  refine ⟨14210033508326702408196547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75786845377742412843714917 14210033508326702408196547)
                  ·
                    refine ⟨21315050262490053612294821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14210033508326702408196547 21315050262490053612294821)
                    ·
                      refine ⟨3996571924216885052305279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21315050262490053612294821 3996571924216885052305279)
                      ·
                        rfl

theorem cell23_7783296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_7783296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783296 prefixEnd_7783296 := by exact prefixLift 7783296
  have htrace : WordTrace (prefixWord ++ tailWord_7783296) baseStart_7783296 baseEnd_7783296 := by
    simpa [prefixWord, tailWord_7783296, baseEnd_7783296] using wordTrace_append hprefix tailTrace_7783296
  have hstable : (prefixWord ++ tailWord_7783296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783296).length < 2 ^ (prefixWord ++ tailWord_7783296).sum := by decide
  have hdescent : baseEnd_7783296 < baseStart_7783296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783330 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_7783330 : Nat := 118140960795 + 7783330 * 2 ^ 59
def prefixEnd_7783330 : Nat := 4983230072969 + 3 ^ 40 * 7783330 * 2
def baseEnd_7783330 : Nat := 3996589382559137919280123

theorem tailTrace_7783330 : CollatzResearch.WordTrace tailWord_7783330 prefixEnd_7783330 3996589382559137919280123 := by
  unfold tailWord_7783330
  simp only [CollatzResearch.WordTrace]
  refine ⟨70970341723083042944792861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189254244594888114519447629 70970341723083042944792861)
  ·
    refine ⟨26613878146156141104297323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70970341723083042944792861 26613878146156141104297323)
    ·
      refine ⟨39920817219234211656445985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26613878146156141104297323 39920817219234211656445985)
      ·
        refine ⟨29940612914425658742334489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39920817219234211656445985 29940612914425658742334489)
        ·
          refine ⟨22455459685819244056750867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29940612914425658742334489 22455459685819244056750867)
          ·
            refine ⟨33683189528728866085126301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22455459685819244056750867 33683189528728866085126301)
            ·
              refine ⟨12631196073273324781922363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33683189528728866085126301 12631196073273324781922363)
              ·
                refine ⟨18946794109909987172883545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12631196073273324781922363 18946794109909987172883545)
                ·
                  refine ⟨14210095582432490379662659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18946794109909987172883545 14210095582432490379662659)
                  ·
                    refine ⟨21315143373648735569493989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14210095582432490379662659 21315143373648735569493989)
                    ·
                      refine ⟨3996589382559137919280123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21315143373648735569493989 3996589382559137919280123)
                      ·
                        rfl

theorem cell23_7783330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_7783330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783330 prefixEnd_7783330 := by exact prefixLift 7783330
  have htrace : WordTrace (prefixWord ++ tailWord_7783330) baseStart_7783330 baseEnd_7783330 := by
    simpa [prefixWord, tailWord_7783330, baseEnd_7783330] using wordTrace_append hprefix tailTrace_7783330
  have hstable : (prefixWord ++ tailWord_7783330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783330).length < 2 ^ (prefixWord ++ tailWord_7783330).sum := by decide
  have hdescent : baseEnd_7783330 < baseStart_7783330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783353 : List Nat := [1, 2, 1, 4, 2, 2, 3, 2, 6]
def baseStart_7783353 : Nat := 118140960795 + 7783353 * 2 ^ 59
def prefixEnd_7783353 : Nat := 4983230072969 + 3 ^ 40 * 7783353 * 2
def baseEnd_7783353 : Nat := 444066799179354592143613

theorem tailTrace_7783353 : CollatzResearch.WordTrace tailWord_7783353 prefixEnd_7783353 444066799179354592143613 := by
  unfold tailWord_7783353
  simp only [CollatzResearch.WordTrace]
  refine ⟨283882205771248846707258713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189254803847499231138172475 283882205771248846707258713)
  ·
    refine ⟨212911654328436635030444035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283882205771248846707258713 212911654328436635030444035)
    ·
      refine ⟨319367481492654952545666053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212911654328436635030444035 319367481492654952545666053)
      ·
        refine ⟨59881402779872803602312385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319367481492654952545666053 59881402779872803602312385)
        ·
          refine ⟨44911052084904602701734289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59881402779872803602312385 44911052084904602701734289)
          ·
            refine ⟨33683289063678452026300717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44911052084904602701734289 33683289063678452026300717)
            ·
              refine ⟨12631233398879419509862769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33683289063678452026300717 12631233398879419509862769)
              ·
                refine ⟨9473425049159564632397077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12631233398879419509862769 9473425049159564632397077)
                ·
                  refine ⟨444066799179354592143613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9473425049159564632397077 444066799179354592143613)
                  ·
                    rfl

theorem cell23_7783353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 6].length) (baseStart_7783353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783353 prefixEnd_7783353 := by exact prefixLift 7783353
  have htrace : WordTrace (prefixWord ++ tailWord_7783353) baseStart_7783353 baseEnd_7783353 := by
    simpa [prefixWord, tailWord_7783353, baseEnd_7783353] using wordTrace_append hprefix tailTrace_7783353
  have hstable : (prefixWord ++ tailWord_7783353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783353).length < 2 ^ (prefixWord ++ tailWord_7783353).sum := by decide
  have hdescent : baseEnd_7783353 < baseStart_7783353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783363 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 7, 1, 3]
def baseStart_7783363 : Nat := 118140960795 + 7783363 * 2 ^ 59
def prefixEnd_7783363 : Nat := 4983230072969 + 3 ^ 40 * 7783363 * 2
def baseEnd_7783363 : Nat := 3996606327420736290167471

theorem tailTrace_7783363 : CollatzResearch.WordTrace tailWord_7783363 prefixEnd_7783363 3996606327420736290167471 := by
  unfold tailWord_7783363
  simp only [CollatzResearch.WordTrace]
  refine ⟨283882570501212618415122743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189255047000808412276748495 283882570501212618415122743)
  ·
    refine ⟨425823855751818927622684115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283882570501212618415122743 425823855751818927622684115)
    ·
      refine ⟨638735783627728391434026173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425823855751818927622684115 638735783627728391434026173)
      ·
        refine ⟨239525918860398146787759815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 638735783627728391434026173 239525918860398146787759815)
        ·
          refine ⟨359288878290597220181639723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239525918860398146787759815 359288878290597220181639723)
          ·
            refine ⟨538933317435895830272459585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359288878290597220181639723 538933317435895830272459585)
            ·
              refine ⟨404199988076921872704344689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538933317435895830272459585 404199988076921872704344689)
              ·
                refine ⟨303149991057691404528258517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404199988076921872704344689 303149991057691404528258517)
                ·
                  refine ⟨7105077915414642293631059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 303149991057691404528258517 7105077915414642293631059)
                  ·
                    refine ⟨10657616873121963440446589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7105077915414642293631059 10657616873121963440446589)
                    ·
                      refine ⟨3996606327420736290167471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10657616873121963440446589 3996606327420736290167471)
                      ·
                        rfl

theorem cell23_7783363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 1, 3].length) (baseStart_7783363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783363 prefixEnd_7783363 := by exact prefixLift 7783363
  have htrace : WordTrace (prefixWord ++ tailWord_7783363) baseStart_7783363 baseEnd_7783363 := by
    simpa [prefixWord, tailWord_7783363, baseEnd_7783363] using wordTrace_append hprefix tailTrace_7783363
  have hstable : (prefixWord ++ tailWord_7783363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783363).length < 2 ^ (prefixWord ++ tailWord_7783363).sum := by decide
  have hdescent : baseEnd_7783363 < baseStart_7783363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783414 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_7783414 : Nat := 118140960795 + 7783414 * 2 ^ 59
def prefixEnd_7783414 : Nat := 4983230072969 + 3 ^ 40 * 7783414 * 2
def baseEnd_7783414 : Nat := 3996632514934115590629737

theorem tailTrace_7783414 : CollatzResearch.WordTrace tailWord_7783414 prefixEnd_7783414 3996632514934115590629737 := by
  unfold tailWord_7783414
  simp only [CollatzResearch.WordTrace]
  refine ⟨17742776914001740882826831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189256287082685236083486197 17742776914001740882826831)
  ·
    refine ⟨26614165371002611324240247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17742776914001740882826831 26614165371002611324240247)
    ·
      refine ⟨39921248056503916986360371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26614165371002611324240247 39921248056503916986360371)
      ·
        refine ⟨59881872084755875479540557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39921248056503916986360371 59881872084755875479540557)
        ·
          refine ⟨22455702031783453304827709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59881872084755875479540557 22455702031783453304827709)
          ·
            refine ⟨8420888261918794989310391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22455702031783453304827709 8420888261918794989310391)
            ·
              refine ⟨12631332392878192483965587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8420888261918794989310391 12631332392878192483965587)
              ·
                refine ⟨18946998589317288725948381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12631332392878192483965587 18946998589317288725948381)
                ·
                  refine ⟨7105124470993983272230643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18946998589317288725948381 7105124470993983272230643)
                  ·
                    refine ⟨10657686706490974908345965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7105124470993983272230643 10657686706490974908345965)
                    ·
                      refine ⟨3996632514934115590629737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10657686706490974908345965 3996632514934115590629737)
                      ·
                        rfl

theorem cell23_7783414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_7783414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783414 prefixEnd_7783414 := by exact prefixLift 7783414
  have htrace : WordTrace (prefixWord ++ tailWord_7783414) baseStart_7783414 baseEnd_7783414 := by
    simpa [prefixWord, tailWord_7783414, baseEnd_7783414] using wordTrace_append hprefix tailTrace_7783414
  have hstable : (prefixWord ++ tailWord_7783414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783414).length < 2 ^ (prefixWord ++ tailWord_7783414).sum := by decide
  have hdescent : baseEnd_7783414 < baseStart_7783414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783470 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_7783470 : Nat := 118140960795 + 7783470 * 2 ^ 59
def prefixEnd_7783470 : Nat := 4983230072969 + 3 ^ 40 * 7783470 * 2
def baseEnd_7783470 : Nat := 3996661269850767371529479

theorem tailTrace_7783470 : CollatzResearch.WordTrace tailWord_7783470 prefixEnd_7783470 3996661269850767371529479 := by
  unfold tailWord_7783470
  simp only [CollatzResearch.WordTrace]
  refine ⟨35485809138978121961158483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189257648741216650459511909 35485809138978121961158483)
  ·
    refine ⟨53228713708467182941737725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35485809138978121961158483 53228713708467182941737725)
    ·
      refine ⟨19960767640675193603151647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53228713708467182941737725 19960767640675193603151647)
      ·
        refine ⟨29941151461012790404727471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19960767640675193603151647 29941151461012790404727471)
        ·
          refine ⟨44911727191519185607091207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29941151461012790404727471 44911727191519185607091207)
          ·
            refine ⟨67367590787278778410636811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44911727191519185607091207 67367590787278778410636811)
            ·
              refine ⟨101051386180918167615955217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67367590787278778410636811 101051386180918167615955217)
              ·
                refine ⟨75788539635688625711966413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101051386180918167615955217 75788539635688625711966413)
                ·
                  refine ⟨28420702363383234641987405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75788539635688625711966413 28420702363383234641987405)
                  ·
                    refine ⟨10657763386268712990745277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28420702363383234641987405 10657763386268712990745277)
                    ·
                      refine ⟨3996661269850767371529479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10657763386268712990745277 3996661269850767371529479)
                      ·
                        rfl

theorem cell23_7783470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_7783470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783470 prefixEnd_7783470 := by exact prefixLift 7783470
  have htrace : WordTrace (prefixWord ++ tailWord_7783470) baseStart_7783470 baseEnd_7783470 := by
    simpa [prefixWord, tailWord_7783470, baseEnd_7783470] using wordTrace_append hprefix tailTrace_7783470
  have hstable : (prefixWord ++ tailWord_7783470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783470).length < 2 ^ (prefixWord ++ tailWord_7783470).sum := by decide
  have hdescent : baseEnd_7783470 < baseStart_7783470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783513 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 1, 6, 3]
def baseStart_7783513 : Nat := 118140960795 + 7783513 * 2 ^ 59
def prefixEnd_7783513 : Nat := 4983230072969 + 3 ^ 40 * 7783513 * 2
def baseEnd_7783513 : Nat := 3996683349518910703291781

theorem tailTrace_7783513 : CollatzResearch.WordTrace tailWord_7783513 prefixEnd_7783513 3996683349518910703291781 := by
  unfold tailWord_7783513
  simp only [CollatzResearch.WordTrace]
  refine ⟨283888041450669194033083193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189258694300446129355388795 283888041450669194033083193)
  ·
    refine ⟨212916031088001895524812395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283888041450669194033083193 212916031088001895524812395)
    ·
      refine ⟨319374046632002843287218593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212916031088001895524812395 319374046632002843287218593)
      ·
        refine ⟨239530534974002132465413945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319374046632002843287218593 239530534974002132465413945)
        ·
          refine ⟨179647901230501599349060459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239530534974002132465413945 179647901230501599349060459)
          ·
            refine ⟨269471851845752399023590689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179647901230501599349060459 269471851845752399023590689)
            ·
              refine ⟨202103888884314299267693017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269471851845752399023590689 202103888884314299267693017)
              ·
                refine ⟨151577916663235724450769763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202103888884314299267693017 151577916663235724450769763)
                ·
                  refine ⟨227366874994853586676154645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151577916663235724450769763 227366874994853586676154645)
                  ·
                    refine ⟨10657822265383761875444749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 227366874994853586676154645 10657822265383761875444749)
                    ·
                      refine ⟨3996683349518910703291781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10657822265383761875444749 3996683349518910703291781)
                      ·
                        rfl

theorem cell23_7783513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_7783513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783513 prefixEnd_7783513 := by exact prefixLift 7783513
  have htrace : WordTrace (prefixWord ++ tailWord_7783513) baseStart_7783513 baseEnd_7783513 := by
    simpa [prefixWord, tailWord_7783513, baseEnd_7783513] using wordTrace_append hprefix tailTrace_7783513
  have hstable : (prefixWord ++ tailWord_7783513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783513).length < 2 ^ (prefixWord ++ tailWord_7783513).sum := by decide
  have hdescent : baseEnd_7783513 < baseStart_7783513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783563 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 6, 5]
def baseStart_7783563 : Nat := 118140960795 + 7783563 * 2 ^ 59
def prefixEnd_7783563 : Nat := 4983230072969 + 3 ^ 40 * 7783563 * 2
def baseEnd_7783563 : Nat := 1332236341183878502555517

theorem tailTrace_7783563 : CollatzResearch.WordTrace tailWord_7783563 prefixEnd_7783563 1332236341183878502555517 := by
  unfold tailWord_7783563
  simp only [CollatzResearch.WordTrace]
  refine ⟨283889865100488052572403343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189259910066992035048268895 283889865100488052572403343)
  ·
    refine ⟨425834797650732078858605015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283889865100488052572403343 425834797650732078858605015)
    ·
      refine ⟨638752196476098118287907523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425834797650732078858605015 638752196476098118287907523)
      ·
        refine ⟨958128294714147177431861285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638752196476098118287907523 958128294714147177431861285)
        ·
          refine ⟨179649055258902595768473991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 958128294714147177431861285 179649055258902595768473991)
          ·
            refine ⟨269473582888353893652710987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179649055258902595768473991 269473582888353893652710987)
            ·
              refine ⟨404210374332530840479066481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269473582888353893652710987 404210374332530840479066481)
              ·
                refine ⟨303157780749398130359299861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404210374332530840479066481 303157780749398130359299861)
                ·
                  refine ⟨14210520972628037360592181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 303157780749398130359299861 14210520972628037360592181)
                  ·
                    refine ⟨1332236341183878502555517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14210520972628037360592181 1332236341183878502555517)
                    ·
                      rfl

theorem cell23_7783563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 5].length) (baseStart_7783563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783563 prefixEnd_7783563 := by exact prefixLift 7783563
  have htrace : WordTrace (prefixWord ++ tailWord_7783563) baseStart_7783563 baseEnd_7783563 := by
    simpa [prefixWord, tailWord_7783563, baseEnd_7783563] using wordTrace_append hprefix tailTrace_7783563
  have hstable : (prefixWord ++ tailWord_7783563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783563).length < 2 ^ (prefixWord ++ tailWord_7783563).sum := by decide
  have hdescent : baseEnd_7783563 < baseStart_7783563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783580 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 4, 5]
def baseStart_7783580 : Nat := 118140960795 + 7783580 * 2 ^ 59
def prefixEnd_7783580 : Nat := 4983230072969 + 3 ^ 40 * 7783580 * 2
def baseEnd_7783580 : Nat := 1332239250907587313717991

theorem tailTrace_7783580 : CollatzResearch.WordTrace tailWord_7783580 prefixEnd_7783580 1332239250907587313717991 := by
  unfold tailWord_7783580
  simp only [CollatzResearch.WordTrace]
  refine ⟨141945242570713232237886097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189260323427617642983848129 141945242570713232237886097)
  ·
    refine ⟨106458931928034924178414573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141945242570713232237886097 106458931928034924178414573)
    ·
      refine ⟨39922099473013096566905465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106458931928034924178414573 39922099473013096566905465)
      ·
        refine ⟨29941574604759822425179099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39922099473013096566905465 29941574604759822425179099)
        ·
          refine ⟨44912361907139733637768649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29941574604759822425179099 44912361907139733637768649)
          ·
            refine ⟨33684271430354800228326487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44912361907139733637768649 33684271430354800228326487)
            ·
              refine ⟨50526407145532200342489731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33684271430354800228326487 50526407145532200342489731)
              ·
                refine ⟨75789610718298300513734597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50526407145532200342489731 75789610718298300513734597)
                ·
                  refine ⟨14210552009680931346325237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75789610718298300513734597 14210552009680931346325237)
                  ·
                    refine ⟨1332239250907587313717991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14210552009680931346325237 1332239250907587313717991)
                    ·
                      rfl

theorem cell23_7783580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_7783580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783580 prefixEnd_7783580 := by exact prefixLift 7783580
  have htrace : WordTrace (prefixWord ++ tailWord_7783580) baseStart_7783580 baseEnd_7783580 := by
    simpa [prefixWord, tailWord_7783580, baseEnd_7783580] using wordTrace_append hprefix tailTrace_7783580
  have hstable : (prefixWord ++ tailWord_7783580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783580).length < 2 ^ (prefixWord ++ tailWord_7783580).sum := by decide
  have hdescent : baseEnd_7783580 < baseStart_7783580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783610 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 5, 4]
def baseStart_7783610 : Nat := 118140960795 + 7783610 * 2 ^ 59
def prefixEnd_7783610 : Nat := 4983230072969 + 3 ^ 40 * 7783610 * 2
def baseEnd_7783610 : Nat := 1332244385714132274592945

theorem tailTrace_7783610 : CollatzResearch.WordTrace tailWord_7783610 prefixEnd_7783610 1332244385714132274592945 := by
  unfold tailWord_7783610
  simp only [CollatzResearch.WordTrace]
  refine ⟨70972894832829444899841071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189261052887545186399576189 70972894832829444899841071)
  ·
    refine ⟨106459342249244167349761607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70972894832829444899841071 106459342249244167349761607)
    ·
      refine ⟨159689013373866251024642411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106459342249244167349761607 159689013373866251024642411)
      ·
        refine ⟨239533520060799376536963617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159689013373866251024642411 239533520060799376536963617)
        ·
          refine ⟨179650140045599532402722713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239533520060799376536963617 179650140045599532402722713)
          ·
            refine ⟨134737605034199649302042035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179650140045599532402722713 134737605034199649302042035)
            ·
              refine ⟨202106407551299473953063053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134737605034199649302042035 202106407551299473953063053)
              ·
                refine ⟨75789902831737302732398645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202106407551299473953063053 75789902831737302732398645)
                ·
                  refine ⟨7105303390475372131162373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75789902831737302732398645 7105303390475372131162373)
                  ·
                    refine ⟨1332244385714132274592945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7105303390475372131162373 1332244385714132274592945)
                    ·
                      rfl

theorem cell23_7783610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_7783610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783610 prefixEnd_7783610 := by exact prefixLift 7783610
  have htrace : WordTrace (prefixWord ++ tailWord_7783610) baseStart_7783610 baseEnd_7783610 := by
    simpa [prefixWord, tailWord_7783610, baseEnd_7783610] using wordTrace_append hprefix tailTrace_7783610
  have hstable : (prefixWord ++ tailWord_7783610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783610).length < 2 ^ (prefixWord ++ tailWord_7783610).sum := by decide
  have hdescent : baseEnd_7783610 < baseStart_7783610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783623 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 10]
def baseStart_7783623 : Nat := 118140960795 + 7783623 * 2 ^ 59
def prefixEnd_7783623 : Nat := 4983230072969 + 3 ^ 40 * 7783623 * 2
def baseEnd_7783623 : Nat := 444082203598989474768475

theorem tailTrace_7783623 : CollatzResearch.WordTrace tailWord_7783623 prefixEnd_7783623 444082203598989474768475 := by
  unfold tailWord_7783623
  simp only [CollatzResearch.WordTrace]
  refine ⟨283892053480270682819587523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189261368986847121879725015 283892053480270682819587523)
  ·
    refine ⟨425838080220406024229381285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283892053480270682819587523 425838080220406024229381285)
    ·
      refine ⟨79844640041326129543008991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425838080220406024229381285 79844640041326129543008991)
      ·
        refine ⟨119766960061989194314513487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79844640041326129543008991 119766960061989194314513487)
        ·
          refine ⟨179650440092983791471770231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119766960061989194314513487 179650440092983791471770231)
          ·
            refine ⟨269475660139475687207655347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179650440092983791471770231 269475660139475687207655347)
            ·
              refine ⟨404213490209213530811483021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269475660139475687207655347 404213490209213530811483021)
              ·
                refine ⟨151580058828455074054306133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404213490209213530811483021 151580058828455074054306133)
                ·
                  refine ⟨444082203598989474768475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 151580058828455074054306133 444082203598989474768475)
                  ·
                    rfl

theorem cell23_7783623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 10].length) (baseStart_7783623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783623 prefixEnd_7783623 := by exact prefixLift 7783623
  have htrace : WordTrace (prefixWord ++ tailWord_7783623) baseStart_7783623 baseEnd_7783623 := by
    simpa [prefixWord, tailWord_7783623, baseEnd_7783623] using wordTrace_append hprefix tailTrace_7783623
  have hstable : (prefixWord ++ tailWord_7783623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783623).length < 2 ^ (prefixWord ++ tailWord_7783623).sum := by decide
  have hdescent : baseEnd_7783623 < baseStart_7783623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783667 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 5, 1, 3]
def baseStart_7783667 : Nat := 118140960795 + 7783667 * 2 ^ 59
def prefixEnd_7783667 : Nat := 4983230072969 + 3 ^ 40 * 7783667 * 2
def baseEnd_7783667 : Nat := 3996762425539703100766073

theorem tailTrace_7783667 : CollatzResearch.WordTrace tailWord_7783667 prefixEnd_7783667 3996762425539703100766073 := by
  unfold tailWord_7783667
  simp only [CollatzResearch.WordTrace]
  refine ⟨283893658292111278334189255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189262438861407518889459503 283893658292111278334189255)
  ·
    refine ⟨425840487438166917501283883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283893658292111278334189255 425840487438166917501283883)
    ·
      refine ⟨638760731157250376251925825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425840487438166917501283883 638760731157250376251925825)
      ·
        refine ⟨479070548367937782188944369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 638760731157250376251925825 479070548367937782188944369)
        ·
          refine ⟨359302911275953336641708277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479070548367937782188944369 359302911275953336641708277)
          ·
            refine ⟨33684647932120625310160151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 359302911275953336641708277 33684647932120625310160151)
            ·
              refine ⟨50526971898180937965240227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33684647932120625310160151 50526971898180937965240227)
              ·
                refine ⟨75790457847271406947860341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50526971898180937965240227 75790457847271406947860341)
                ·
                  refine ⟨7105355423181694401361907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75790457847271406947860341 7105355423181694401361907)
                  ·
                    refine ⟨10658033134772541602042861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7105355423181694401361907 10658033134772541602042861)
                    ·
                      refine ⟨3996762425539703100766073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10658033134772541602042861 3996762425539703100766073)
                      ·
                        rfl

theorem cell23_7783667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 1, 3].length) (baseStart_7783667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783667 prefixEnd_7783667 := by exact prefixLift 7783667
  have htrace : WordTrace (prefixWord ++ tailWord_7783667) baseStart_7783667 baseEnd_7783667 := by
    simpa [prefixWord, tailWord_7783667, baseEnd_7783667] using wordTrace_append hprefix tailTrace_7783667
  have hstable : (prefixWord ++ tailWord_7783667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783667).length < 2 ^ (prefixWord ++ tailWord_7783667).sum := by decide
  have hdescent : baseEnd_7783667 < baseStart_7783667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783717 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 1, 6]
def baseStart_7783717 : Nat := 118140960795 + 7783717 * 2 ^ 59
def prefixEnd_7783717 : Nat := 4983230072969 + 3 ^ 40 * 7783717 * 2
def baseEnd_7783717 : Nat := 1332262699857475968380281

theorem tailTrace_7783717 : CollatzResearch.WordTrace tailWord_7783717 prefixEnd_7783717 1332262699857475968380281 := by
  unfold tailWord_7783717
  simp only [CollatzResearch.WordTrace]
  refine ⟨283895481941930136873509405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189263654627953424582339603 283895481941930136873509405)
  ·
    refine ⟨106460805728223801327566027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283895481941930136873509405 106460805728223801327566027)
    ·
      refine ⟨159691208592335701991349041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106460805728223801327566027 159691208592335701991349041)
      ·
        refine ⟨119768406444251776493511781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159691208592335701991349041 119768406444251776493511781)
        ·
          refine ⟨22456576208297208092533459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119768406444251776493511781 22456576208297208092533459)
          ·
            refine ⟨33684864312445812138800189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22456576208297208092533459 33684864312445812138800189)
            ·
              refine ⟨12631824117167179552050071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33684864312445812138800189 12631824117167179552050071)
              ·
                refine ⟨18947736175750769328075107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12631824117167179552050071 18947736175750769328075107)
                ·
                  refine ⟨28421604263626153992112661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18947736175750769328075107 28421604263626153992112661)
                  ·
                    refine ⟨1332262699857475968380281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28421604263626153992112661 1332262699857475968380281)
                    ·
                      rfl

theorem cell23_7783717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_7783717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783717 prefixEnd_7783717 := by exact prefixLift 7783717
  have htrace : WordTrace (prefixWord ++ tailWord_7783717) baseStart_7783717 baseEnd_7783717 := by
    simpa [prefixWord, tailWord_7783717, baseEnd_7783717] using wordTrace_append hprefix tailTrace_7783717
  have hstable : (prefixWord ++ tailWord_7783717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783717).length < 2 ^ (prefixWord ++ tailWord_7783717).sum := by decide
  have hdescent : baseEnd_7783717 < baseStart_7783717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783760 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 2, 7]
def baseStart_7783760 : Nat := 118140960795 + 7783760 * 2 ^ 59
def prefixEnd_7783760 : Nat := 4983230072969 + 3 ^ 40 * 7783760 * 2
def baseEnd_7783760 : Nat := 1332270059746857078967715

theorem tailTrace_7783760 : CollatzResearch.WordTrace tailWord_7783760 prefixEnd_7783760 1332270059746857078967715 := by
  unfold tailWord_7783760
  simp only [CollatzResearch.WordTrace]
  refine ⟨141948525140387177608662367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189264700187182903478216489 141948525140387177608662367)
  ·
    refine ⟨212922787710580766412993551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141948525140387177608662367 212922787710580766412993551)
    ·
      refine ⟨319384181565871149619490327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212922787710580766412993551 319384181565871149619490327)
      ·
        refine ⟨479076272348806724429235491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319384181565871149619490327 479076272348806724429235491)
        ·
          refine ⟨718614408523210086643853237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479076272348806724429235491 718614408523210086643853237)
          ·
            refine ⟨67370100799050945622861241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 718614408523210086643853237 67370100799050945622861241)
            ·
              refine ⟨50527575599288209217145931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67370100799050945622861241 50527575599288209217145931)
              ·
                refine ⟨75791363398932313825718897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50527575599288209217145931 75791363398932313825718897)
                ·
                  refine ⟨56843522549199235369289173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75791363398932313825718897 56843522549199235369289173)
                  ·
                    refine ⟨1332270059746857078967715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56843522549199235369289173 1332270059746857078967715)
                    ·
                      rfl

theorem cell23_7783760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 2, 7].length) (baseStart_7783760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783760 prefixEnd_7783760 := by exact prefixLift 7783760
  have htrace : WordTrace (prefixWord ++ tailWord_7783760) baseStart_7783760 baseEnd_7783760 := by
    simpa [prefixWord, tailWord_7783760, baseEnd_7783760] using wordTrace_append hprefix tailTrace_7783760
  have hstable : (prefixWord ++ tailWord_7783760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783760).length < 2 ^ (prefixWord ++ tailWord_7783760).sum := by decide
  have hdescent : baseEnd_7783760 < baseStart_7783760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783809 : List Nat := [1, 2, 4, 3, 3, 1, 2, 2, 1, 2, 2]
def baseStart_7783809 : Nat := 118140960795 + 7783809 * 2 ^ 59
def prefixEnd_7783809 : Nat := 4983230072969 + 3 ^ 40 * 7783809 * 2
def baseEnd_7783809 : Nat := 3996835339792641545190421

theorem tailTrace_7783809 : CollatzResearch.WordTrace tailWord_7783809 prefixEnd_7783809 3996835339792641545190421 := by
  unfold tailWord_7783809
  simp only [CollatzResearch.WordTrace]
  refine ⟨283898837457596836585858481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189265891638397891057238987 283898837457596836585858481)
  ·
    refine ⟨212924128093197627439393861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283898837457596836585858481 212924128093197627439393861)
    ·
      refine ⟨39923274017474555144886349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212924128093197627439393861 39923274017474555144886349)
      ·
        refine ⟨14971227756552958179332381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39923274017474555144886349 14971227756552958179332381)
        ·
          refine ⟨5614210408707359317249643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14971227756552958179332381 5614210408707359317249643)
          ·
            refine ⟨8421315613061038975874465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5614210408707359317249643 8421315613061038975874465)
            ·
              refine ⟨6315986709795779231905849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8421315613061038975874465 6315986709795779231905849)
              ·
                refine ⟨4736990032346834423929387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6315986709795779231905849 4736990032346834423929387)
                ·
                  refine ⟨7105485048520251635894081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4736990032346834423929387 7105485048520251635894081)
                  ·
                    refine ⟨5329113786390188726920561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7105485048520251635894081 5329113786390188726920561)
                    ·
                      refine ⟨3996835339792641545190421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5329113786390188726920561 3996835339792641545190421)
                      ·
                        rfl

theorem cell23_7783809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_7783809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783809 prefixEnd_7783809 := by exact prefixLift 7783809
  have htrace : WordTrace (prefixWord ++ tailWord_7783809) baseStart_7783809 baseEnd_7783809 := by
    simpa [prefixWord, tailWord_7783809, baseEnd_7783809] using wordTrace_append hprefix tailTrace_7783809
  have hstable : (prefixWord ++ tailWord_7783809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783809).length < 2 ^ (prefixWord ++ tailWord_7783809).sum := by decide
  have hdescent : baseEnd_7783809 < baseStart_7783809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783837 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 9]
def baseStart_7783837 : Nat := 118140960795 + 7783837 * 2 ^ 59
def prefixEnd_7783837 : Nat := 4983230072969 + 3 ^ 40 * 7783837 * 2
def baseEnd_7783837 : Nat := 444094413027885270626699

theorem tailTrace_7783837 : CollatzResearch.WordTrace tailWord_7783837 prefixEnd_7783837 444094413027885270626699 := by
  unfold tailWord_7783837
  simp only [CollatzResearch.WordTrace]
  refine ⟨283899858701495397367877765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189266572467663598245251843 283899858701495397367877765)
  ·
    refine ⟨53231223506530387006477081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283899858701495397367877765 53231223506530387006477081)
    ·
      refine ⟨39923417629897790254857811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53231223506530387006477081 39923417629897790254857811)
      ·
        refine ⟨59885126444846685382286717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39923417629897790254857811 59885126444846685382286717)
        ·
          refine ⟨22456922416817507018357519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59885126444846685382286717 22456922416817507018357519)
          ·
            refine ⟨33685383625226260527536279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22456922416817507018357519 33685383625226260527536279)
            ·
              refine ⟨50528075437839390791304419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33685383625226260527536279 50528075437839390791304419)
              ·
                refine ⟨75792113156759086186956629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50528075437839390791304419 75792113156759086186956629)
                ·
                  refine ⟨444094413027885270626699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75792113156759086186956629 444094413027885270626699)
                  ·
                    rfl

theorem cell23_7783837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_7783837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783837 prefixEnd_7783837 := by exact prefixLift 7783837
  have htrace : WordTrace (prefixWord ++ tailWord_7783837) baseStart_7783837 baseEnd_7783837 := by
    simpa [prefixWord, tailWord_7783837, baseEnd_7783837] using wordTrace_append hprefix tailTrace_7783837
  have hstable : (prefixWord ++ tailWord_7783837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783837).length < 2 ^ (prefixWord ++ tailWord_7783837).sum := by decide
  have hdescent : baseEnd_7783837 < baseStart_7783837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783865 : List Nat := [1, 2, 1, 4, 4, 2, 1, 2, 2, 2, 2]
def baseStart_7783865 : Nat := 118140960795 + 7783865 * 2 ^ 59
def prefixEnd_7783865 : Nat := 4983230072969 + 3 ^ 40 * 7783865 * 2
def baseEnd_7783865 : Nat := 3996864094709293326090163

theorem tailTrace_7783865 : CollatzResearch.WordTrace tailWord_7783865 prefixEnd_7783865 3996864094709293326090163 := by
  unfold tailWord_7783865
  simp only [CollatzResearch.WordTrace]
  refine ⟨283900879945393958149897049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189267253296929305433264699 283900879945393958149897049)
  ·
    refine ⟨212925659959045468612422787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283900879945393958149897049 212925659959045468612422787)
    ·
      refine ⟨319388489938568202918634181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212925659959045468612422787 319388489938568202918634181)
      ·
        refine ⟨59885341863481538047243909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 319388489938568202918634181 59885341863481538047243909)
        ·
          refine ⟨11228501599402788383858233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59885341863481538047243909 11228501599402788383858233)
          ·
            refine ⟨8421376199552091287893675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11228501599402788383858233 8421376199552091287893675)
            ·
              refine ⟨12632064299328136931840513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8421376199552091287893675 12632064299328136931840513)
              ·
                refine ⟨9474048224496102698880385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12632064299328136931840513 9474048224496102698880385)
                ·
                  refine ⟨7105536168372077024160289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9474048224496102698880385 7105536168372077024160289)
                  ·
                    refine ⟨5329152126279057768120217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7105536168372077024160289 5329152126279057768120217)
                    ·
                      refine ⟨3996864094709293326090163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5329152126279057768120217 3996864094709293326090163)
                      ·
                        rfl

theorem cell23_7783865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_7783865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783865 prefixEnd_7783865 := by exact prefixLift 7783865
  have htrace : WordTrace (prefixWord ++ tailWord_7783865) baseStart_7783865 baseEnd_7783865 := by
    simpa [prefixWord, tailWord_7783865, baseEnd_7783865] using wordTrace_append hprefix tailTrace_7783865
  have hstable : (prefixWord ++ tailWord_7783865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783865).length < 2 ^ (prefixWord ++ tailWord_7783865).sum := by decide
  have hdescent : baseEnd_7783865 < baseStart_7783865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783887 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 4]
def baseStart_7783887 : Nat := 118140960795 + 7783887 * 2 ^ 59
def prefixEnd_7783887 : Nat := 4983230072969 + 3 ^ 40 * 7783887 * 2
def baseEnd_7783887 : Nat := 3996875391283692240015061

theorem tailTrace_7783887 : CollatzResearch.WordTrace tailWord_7783887 prefixEnd_7783887 3996875391283692240015061 := by
  unfold tailWord_7783887
  simp only [CollatzResearch.WordTrace]
  refine ⟨283901682351314255907197915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189267788234209503938131943 283901682351314255907197915)
  ·
    refine ⟨425852523526971383860796873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283901682351314255907197915 425852523526971383860796873)
    ·
      refine ⟨319389392645228537895597655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425852523526971383860796873 319389392645228537895597655)
      ·
        refine ⟨479084088967842806843396483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319389392645228537895597655 479084088967842806843396483)
        ·
          refine ⟨718626133451764210265094725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479084088967842806843396483 718626133451764210265094725)
          ·
            refine ⟨134742400022205789424705261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 718626133451764210265094725 134742400022205789424705261)
            ·
              refine ⟨50528400008327171034264473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134742400022205789424705261 50528400008327171034264473)
              ·
                refine ⟨37896300006245378275698355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50528400008327171034264473 37896300006245378275698355)
                ·
                  refine ⟨56844450009368067413547533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37896300006245378275698355 56844450009368067413547533)
                  ·
                    refine ⟨21316668753513025280080325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56844450009368067413547533 21316668753513025280080325)
                    ·
                      refine ⟨3996875391283692240015061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21316668753513025280080325 3996875391283692240015061)
                      ·
                        rfl

theorem cell23_7783887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_7783887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783887 prefixEnd_7783887 := by exact prefixLift 7783887
  have htrace : WordTrace (prefixWord ++ tailWord_7783887) baseStart_7783887 baseEnd_7783887 := by
    simpa [prefixWord, tailWord_7783887, baseEnd_7783887] using wordTrace_append hprefix tailTrace_7783887
  have hstable : (prefixWord ++ tailWord_7783887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783887).length < 2 ^ (prefixWord ++ tailWord_7783887).sum := by decide
  have hdescent : baseEnd_7783887 < baseStart_7783887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783904 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 4, 4, 2]
def baseStart_7783904 : Nat := 118140960795 + 7783904 * 2 ^ 59
def prefixEnd_7783904 : Nat := 4983230072969 + 3 ^ 40 * 7783904 * 2
def baseEnd_7783904 : Nat := 3996884120454818673502483

theorem tailTrace_7783904 : CollatzResearch.WordTrace tailWord_7783904 prefixEnd_7783904 3996884120454818673502483 := by
  unfold tailWord_7783904
  simp only [CollatzResearch.WordTrace]
  refine ⟨141951151196126333905283383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189268201594835111873711177 141951151196126333905283383)
  ·
    refine ⟨212926726794189500857925075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141951151196126333905283383 212926726794189500857925075)
    ·
      refine ⟨319390090191284251286887613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212926726794189500857925075 319390090191284251286887613)
      ·
        refine ⟨119771283821731594232582855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319390090191284251286887613 119771283821731594232582855)
        ·
          refine ⟨179656925732597391348874283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119771283821731594232582855 179656925732597391348874283)
          ·
            refine ⟨269485388598896087023311425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179656925732597391348874283 269485388598896087023311425)
            ·
              refine ⟨202114041449172065267483569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269485388598896087023311425 202114041449172065267483569)
              ·
                refine ⟨151585531086879048950612677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202114041449172065267483569 151585531086879048950612677)
                ·
                  refine ⟨28422287078789821678239877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151585531086879048950612677 28422287078789821678239877)
                  ·
                    refine ⟨5329178827273091564669977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28422287078789821678239877 5329178827273091564669977)
                    ·
                      refine ⟨3996884120454818673502483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5329178827273091564669977 3996884120454818673502483)
                      ·
                        rfl

theorem cell23_7783904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_7783904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783904 prefixEnd_7783904 := by exact prefixLift 7783904
  have htrace : WordTrace (prefixWord ++ tailWord_7783904) baseStart_7783904 baseEnd_7783904 := by
    simpa [prefixWord, tailWord_7783904, baseEnd_7783904] using wordTrace_append hprefix tailTrace_7783904
  have hstable : (prefixWord ++ tailWord_7783904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783904).length < 2 ^ (prefixWord ++ tailWord_7783904).sum := by decide
  have hdescent : baseEnd_7783904 < baseStart_7783904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783982 : List Nat := [4, 1, 3, 1, 2, 3, 2, 2, 1, 4]
def baseStart_7783982 : Nat := 118140960795 + 7783982 * 2 ^ 59
def prefixEnd_7783982 : Nat := 4983230072969 + 3 ^ 40 * 7783982 * 2
def baseEnd_7783982 : Nat := 1332308057315289789442375

theorem tailTrace_7783982 : CollatzResearch.WordTrace tailWord_7783982 prefixEnd_7783982 1332308057315289789442375 := by
  unfold tailWord_7783982
  simp only [CollatzResearch.WordTrace]
  refine ⟨35488143410746260891488275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189270098190646724754604133 35488143410746260891488275)
  ·
    refine ⟨53232215116119391337232413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35488143410746260891488275 53232215116119391337232413)
    ·
      refine ⟨19962080668544771751462155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53232215116119391337232413 19962080668544771751462155)
      ·
        refine ⟨29943121002817157627193233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19962080668544771751462155 29943121002817157627193233)
        ·
          refine ⟨22457340752112868220394925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29943121002817157627193233 22457340752112868220394925)
          ·
            refine ⟨8421502782042325582648097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22457340752112868220394925 8421502782042325582648097)
            ·
              refine ⟨6316127086531744186986073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8421502782042325582648097 6316127086531744186986073)
              ·
                refine ⟨4737095314898808140239555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6316127086531744186986073 4737095314898808140239555)
                ·
                  refine ⟨7105642972348212210359333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4737095314898808140239555 7105642972348212210359333)
                  ·
                    refine ⟨1332308057315289789442375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7105642972348212210359333 1332308057315289789442375)
                    ·
                      rfl

theorem cell23_7783982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_7783982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783982 prefixEnd_7783982 := by exact prefixLift 7783982
  have htrace : WordTrace (prefixWord ++ tailWord_7783982) baseStart_7783982 baseEnd_7783982 := by
    simpa [prefixWord, tailWord_7783982, baseEnd_7783982] using wordTrace_append hprefix tailTrace_7783982
  have hstable : (prefixWord ++ tailWord_7783982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783982).length < 2 ^ (prefixWord ++ tailWord_7783982).sum := by decide
  have hdescent : baseEnd_7783982 < baseStart_7783982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7783994 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4]
def baseStart_7783994 : Nat := 118140960795 + 7783994 * 2 ^ 59
def prefixEnd_7783994 : Nat := 4983230072969 + 3 ^ 40 * 7783994 * 2
def baseEnd_7783994 : Nat := 3996930333713723321377069

theorem tailTrace_7783994 : CollatzResearch.WordTrace tailWord_7783994 prefixEnd_7783994 3996930333713723321377069 := by
  unfold tailWord_7783994
  simp only [CollatzResearch.WordTrace]
  refine ⟨70976396240481653295335759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189270389974617742120895357 70976396240481653295335759)
  ·
    refine ⟨106464594360722479943003639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70976396240481653295335759 106464594360722479943003639)
    ·
      refine ⟨159696891541083719914505459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106464594360722479943003639 159696891541083719914505459)
      ·
        refine ⟨239545337311625579871758189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159696891541083719914505459 239545337311625579871758189)
        ·
          refine ⟨89829501491859592451909321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239545337311625579871758189 89829501491859592451909321)
          ·
            refine ⟨67372126118894694338931991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89829501491859592451909321 67372126118894694338931991)
            ·
              refine ⟨101058189178342041508397987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67372126118894694338931991 101058189178342041508397987)
              ·
                refine ⟨151587283767513062262596981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101058189178342041508397987 151587283767513062262596981)
                ·
                  refine ⟨14211307853204349587118467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151587283767513062262596981 14211307853204349587118467)
                  ·
                    refine ⟨21316961779806524380677701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14211307853204349587118467 21316961779806524380677701)
                    ·
                      refine ⟨3996930333713723321377069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21316961779806524380677701 3996930333713723321377069)
                      ·
                        rfl

theorem cell23_7783994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_7783994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7783994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7783994 prefixEnd_7783994 := by exact prefixLift 7783994
  have htrace : WordTrace (prefixWord ++ tailWord_7783994) baseStart_7783994 baseEnd_7783994 := by
    simpa [prefixWord, tailWord_7783994, baseEnd_7783994] using wordTrace_append hprefix tailTrace_7783994
  have hstable : (prefixWord ++ tailWord_7783994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7783994).length < 2 ^ (prefixWord ++ tailWord_7783994).sum := by decide
  have hdescent : baseEnd_7783994 < baseStart_7783994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7783994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784028 : List Nat := [2, 2, 4, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_7784028 : Nat := 118140960795 + 7784028 * 2 ^ 59
def prefixEnd_7784028 : Nat := 4983230072969 + 3 ^ 40 * 7784028 * 2
def baseEnd_7784028 : Nat := 3996947792055976188351913

theorem tailTrace_7784028 : CollatzResearch.WordTrace tailWord_7784028 prefixEnd_7784028 3996947792055976188351913 := by
  unfold tailWord_7784028
  simp only [CollatzResearch.WordTrace]
  refine ⟨141953412521901718494040369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189271216695868957992053825 141953412521901718494040369)
  ·
    refine ⟨106465059391426288870530277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141953412521901718494040369 106465059391426288870530277)
    ·
      refine ⟨19962198635892429163224427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106465059391426288870530277 19962198635892429163224427)
      ·
        refine ⟨29943297953838643744836641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19962198635892429163224427 29943297953838643744836641)
        ·
          refine ⟨22457473465378982808627481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29943297953838643744836641 22457473465378982808627481)
          ·
            refine ⟨16843105099034237106470611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22457473465378982808627481 16843105099034237106470611)
            ·
              refine ⟨25264657648551355659705917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16843105099034237106470611 25264657648551355659705917)
              ·
                refine ⟨9474246618206758372389719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25264657648551355659705917 9474246618206758372389719)
                ·
                  refine ⟨14211369927310137558584579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9474246618206758372389719 14211369927310137558584579)
                  ·
                    refine ⟨21317054890965206337876869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14211369927310137558584579 21317054890965206337876869)
                    ·
                      refine ⟨3996947792055976188351913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21317054890965206337876869 3996947792055976188351913)
                      ·
                        rfl

theorem cell23_7784028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_7784028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784028 prefixEnd_7784028 := by exact prefixLift 7784028
  have htrace : WordTrace (prefixWord ++ tailWord_7784028) baseStart_7784028 baseEnd_7784028 := by
    simpa [prefixWord, tailWord_7784028, baseEnd_7784028] using wordTrace_append hprefix tailTrace_7784028
  have hstable : (prefixWord ++ tailWord_7784028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784028).length < 2 ^ (prefixWord ++ tailWord_7784028).sum := by decide
  have hdescent : baseEnd_7784028 < baseStart_7784028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784068 : List Nat := [2, 3, 2, 1, 4, 2, 2, 7]
def baseStart_7784068 : Nat := 118140960795 + 7784068 * 2 ^ 59
def prefixEnd_7784068 : Nat := 4983230072969 + 3 ^ 40 * 7784068 * 2
def baseEnd_7784068 : Nat := 148035864121561334513027

theorem tailTrace_7784068 : CollatzResearch.WordTrace tailWord_7784068 prefixEnd_7784068 148035864121561334513027 := by
  unfold tailWord_7784068
  simp only [CollatzResearch.WordTrace]
  refine ⟨141954141981829261909768429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189272189309105682546357905 141954141981829261909768429)
  ·
    refine ⟨53232803243185973216163161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141954141981829261909768429 53232803243185973216163161)
    ·
      refine ⟨39924602432389479912122371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53232803243185973216163161 39924602432389479912122371)
      ·
        refine ⟨59886903648584219868183557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39924602432389479912122371 59886903648584219868183557)
        ·
          refine ⟨11228794434109541225284417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59886903648584219868183557 11228794434109541225284417)
          ·
            refine ⟨8421595825582155918963313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11228794434109541225284417 8421595825582155918963313)
            ·
              refine ⟨6316196869186616939222485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8421595825582155918963313 6316196869186616939222485)
              ·
                refine ⟨148035864121561334513027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6316196869186616939222485 148035864121561334513027)
                ·
                  rfl

theorem cell23_7784068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 7].length) (baseStart_7784068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784068 prefixEnd_7784068 := by exact prefixLift 7784068
  have htrace : WordTrace (prefixWord ++ tailWord_7784068) baseStart_7784068 baseEnd_7784068 := by
    simpa [prefixWord, tailWord_7784068, baseEnd_7784068] using wordTrace_append hprefix tailTrace_7784068
  have hstable : (prefixWord ++ tailWord_7784068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784068).length < 2 ^ (prefixWord ++ tailWord_7784068).sum := by decide
  have hdescent : baseEnd_7784068 < baseStart_7784068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784078 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3]
def baseStart_7784078 : Nat := 118140960795 + 7784078 * 2 ^ 59
def prefixEnd_7784078 : Nat := 4983230072969 + 3 ^ 40 * 7784078 * 2
def baseEnd_7784078 : Nat := 3996973466088700992726683

theorem tailTrace_7784078 : CollatzResearch.WordTrace tailWord_7784078 prefixEnd_7784078 3996973466088700992726683 := by
  unfold tailWord_7784078
  simp only [CollatzResearch.WordTrace]
  refine ⟨35488581086702786940925111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189272432462414863684933925 35488581086702786940925111)
  ·
    refine ⟨53232871630054180411387667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35488581086702786940925111 53232871630054180411387667)
    ·
      refine ⟨79849307445081270617081501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53232871630054180411387667 79849307445081270617081501)
      ·
        refine ⟨29943490291905476481405563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79849307445081270617081501 29943490291905476481405563)
        ·
          refine ⟨44915235437858214722108345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29943490291905476481405563 44915235437858214722108345)
          ·
            refine ⟨33686426578393661041581259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44915235437858214722108345 33686426578393661041581259)
            ·
              refine ⟨50529639867590491562371889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33686426578393661041581259 50529639867590491562371889)
              ·
                refine ⟨37897229900692868671778917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50529639867590491562371889 37897229900692868671778917)
                ·
                  refine ⟨7105730606379912875958547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37897229900692868671778917 7105730606379912875958547)
                  ·
                    refine ⟨10658595909569869313937821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7105730606379912875958547 10658595909569869313937821)
                    ·
                      refine ⟨3996973466088700992726683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10658595909569869313937821 3996973466088700992726683)
                      ·
                        rfl

theorem cell23_7784078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_7784078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784078 prefixEnd_7784078 := by exact prefixLift 7784078
  have htrace : WordTrace (prefixWord ++ tailWord_7784078) baseStart_7784078 baseEnd_7784078 := by
    simpa [prefixWord, tailWord_7784078, baseEnd_7784078] using wordTrace_append hprefix tailTrace_7784078
  have hstable : (prefixWord ++ tailWord_7784078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784078).length < 2 ^ (prefixWord ++ tailWord_7784078).sum := by decide
  have hdescent : baseEnd_7784078 < baseStart_7784078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784151 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 3]
def baseStart_7784151 : Nat := 118140960795 + 7784151 * 2 ^ 59
def prefixEnd_7784151 : Nat := 4983230072969 + 3 ^ 40 * 7784151 * 2
def baseEnd_7784151 : Nat := 3997010950176479207113847

theorem tailTrace_7784151 : CollatzResearch.WordTrace tailWord_7784151 prefixEnd_7784151 3997010950176479207113847 := by
  unfold tailWord_7784151
  simp only [CollatzResearch.WordTrace]
  refine ⟨283911311222357828994808307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189274207481571885996538871 283911311222357828994808307)
  ·
    refine ⟨425866966833536743492212461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283911311222357828994808307 425866966833536743492212461)
    ·
      refine ⟨159700112562576278809579673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425866966833536743492212461 159700112562576278809579673)
      ·
        refine ⟨119775084421932209107184755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159700112562576278809579673 119775084421932209107184755)
        ·
          refine ⟨179662626632898313660777133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119775084421932209107184755 179662626632898313660777133)
          ·
            refine ⟨67373484987336867622791425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179662626632898313660777133 67373484987336867622791425)
            ·
              refine ⟨50530113740502650717093569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67373484987336867622791425 50530113740502650717093569)
              ·
                refine ⟨37897585305376988037820177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50530113740502650717093569 37897585305376988037820177)
                ·
                  refine ⟨28423188979032741028365133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37897585305376988037820177 28423188979032741028365133)
                  ·
                    refine ⟨10658695867137277885636925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28423188979032741028365133 10658695867137277885636925)
                    ·
                      refine ⟨3997010950176479207113847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10658695867137277885636925 3997010950176479207113847)
                      ·
                        rfl

theorem cell23_7784151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_7784151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784151 prefixEnd_7784151 := by exact prefixLift 7784151
  have htrace : WordTrace (prefixWord ++ tailWord_7784151) baseStart_7784151 baseEnd_7784151 := by
    simpa [prefixWord, tailWord_7784151, baseEnd_7784151] using wordTrace_append hprefix tailTrace_7784151
  have hstable : (prefixWord ++ tailWord_7784151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784151).length < 2 ^ (prefixWord ++ tailWord_7784151).sum := by decide
  have hdescent : baseEnd_7784151 < baseStart_7784151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784168 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_7784168 : Nat := 118140960795 + 7784168 * 2 ^ 59
def prefixEnd_7784168 : Nat := 4983230072969 + 3 ^ 40 * 7784168 * 2
def baseEnd_7784168 : Nat := 3997019679347605640601269

theorem tailTrace_7784168 : CollatzResearch.WordTrace tailWord_7784168 prefixEnd_7784168 3997019679347605640601269 := by
  unfold tailWord_7784168
  simp only [CollatzResearch.WordTrace]
  refine ⟨141955965631648120449088579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189274620842197493932118105 141955965631648120449088579)
  ·
    refine ⟨212933948447472180673632869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141955965631648120449088579 212933948447472180673632869)
    ·
      refine ⟨39925115333901033876306163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212933948447472180673632869 39925115333901033876306163)
      ·
        refine ⟨59887673000851550814459245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39925115333901033876306163 59887673000851550814459245)
        ·
          refine ⟨22457877375319331555422217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59887673000851550814459245 22457877375319331555422217)
          ·
            refine ⟨16843408031489498666566663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22457877375319331555422217 16843408031489498666566663)
            ·
              refine ⟨25265112047234247999849995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16843408031489498666566663 25265112047234247999849995)
              ·
                refine ⟨37897668070851371999774993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25265112047234247999849995 37897668070851371999774993)
                ·
                  refine ⟨28423251053138528999831245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37897668070851371999774993 28423251053138528999831245)
                  ·
                    refine ⟨10658719144926948374936717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28423251053138528999831245 10658719144926948374936717)
                    ·
                      refine ⟨3997019679347605640601269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10658719144926948374936717 3997019679347605640601269)
                      ·
                        rfl

theorem cell23_7784168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_7784168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784168 prefixEnd_7784168 := by exact prefixLift 7784168
  have htrace : WordTrace (prefixWord ++ tailWord_7784168) baseStart_7784168 baseEnd_7784168 := by
    simpa [prefixWord, tailWord_7784168, baseEnd_7784168] using wordTrace_append hprefix tailTrace_7784168
  have hstable : (prefixWord ++ tailWord_7784168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784168).length < 2 ^ (prefixWord ++ tailWord_7784168).sum := by decide
  have hdescent : baseEnd_7784168 < baseStart_7784168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784178 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 2, 5, 2]
def baseStart_7784178 : Nat := 118140960795 + 7784178 * 2 ^ 59
def prefixEnd_7784178 : Nat := 4983230072969 + 3 ^ 40 * 7784178 * 2
def baseEnd_7784178 : Nat := 3997024814154150601476223

theorem tailTrace_7784178 : CollatzResearch.WordTrace tailWord_7784178 prefixEnd_7784178 3997024814154150601476223 := by
  unfold tailWord_7784178
  simp only [CollatzResearch.WordTrace]
  refine ⟨70978073998315003151510297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189274863995506675070694125 70978073998315003151510297)
  ·
    refine ⟨53233555498736252363632723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70978073998315003151510297 53233555498736252363632723)
    ·
      refine ⟨79850333248104378545449085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53233555498736252363632723 79850333248104378545449085)
      ·
        refine ⟨29943874968039141954543407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79850333248104378545449085 29943874968039141954543407)
        ·
          refine ⟨44915812452058712931815111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29943874968039141954543407 44915812452058712931815111)
          ·
            refine ⟨67373718678088069397722667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44915812452058712931815111 67373718678088069397722667)
            ·
              refine ⟨101060578017132104096584001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67373718678088069397722667 101060578017132104096584001)
              ·
                refine ⟨75795433512849078072438001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101060578017132104096584001 75795433512849078072438001)
                ·
                  refine ⟨56846575134636808554328501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75795433512849078072438001 56846575134636808554328501)
                  ·
                    refine ⟨5329366418872200801968297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56846575134636808554328501 5329366418872200801968297)
                    ·
                      refine ⟨3997024814154150601476223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5329366418872200801968297 3997024814154150601476223)
                      ·
                        rfl

theorem cell23_7784178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_7784178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784178 prefixEnd_7784178 := by exact prefixLift 7784178
  have htrace : WordTrace (prefixWord ++ tailWord_7784178) baseStart_7784178 baseEnd_7784178 := by
    simpa [prefixWord, tailWord_7784178, baseEnd_7784178] using wordTrace_append hprefix tailTrace_7784178
  have hstable : (prefixWord ++ tailWord_7784178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784178).length < 2 ^ (prefixWord ++ tailWord_7784178).sum := by decide
  have hdescent : baseEnd_7784178 < baseStart_7784178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784184 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 1, 10]
def baseStart_7784184 : Nat := 118140960795 + 7784184 * 2 ^ 59
def prefixEnd_7784184 : Nat := 4983230072969 + 3 ^ 40 * 7784184 * 2
def baseEnd_7784184 : Nat := 1332342631679359192667065

theorem tailTrace_7784184 : CollatzResearch.WordTrace tailWord_7784184 prefixEnd_7784184 1332342631679359192667065 := by
  unfold tailWord_7784184
  simp only [CollatzResearch.WordTrace]
  refine ⟨141956257415619137815379803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189275009887492183753839737 141956257415619137815379803)
  ·
    refine ⟨212934386123428706723069705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141956257415619137815379803 212934386123428706723069705)
    ·
      refine ⟨159700789592571530042302279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212934386123428706723069705 159700789592571530042302279)
      ·
        refine ⟨239551184388857295063453419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159700789592571530042302279 239551184388857295063453419)
        ·
          refine ⟨359326776583285942595180129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239551184388857295063453419 359326776583285942595180129)
          ·
            refine ⟨269495082437464456946385097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359326776583285942595180129 269495082437464456946385097)
            ·
              refine ⟨202121311828098342709788823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269495082437464456946385097 202121311828098342709788823)
              ·
                refine ⟨303181967742147514064683235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202121311828098342709788823 303181967742147514064683235)
                ·
                  refine ⟨454772951613221271097024853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303181967742147514064683235 454772951613221271097024853)
                  ·
                    refine ⟨1332342631679359192667065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 454772951613221271097024853 1332342631679359192667065)
                    ·
                      rfl

theorem cell23_7784184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_7784184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784184 prefixEnd_7784184 := by exact prefixLift 7784184
  have htrace : WordTrace (prefixWord ++ tailWord_7784184) baseStart_7784184 baseEnd_7784184 := by
    simpa [prefixWord, tailWord_7784184, baseEnd_7784184] using wordTrace_append hprefix tailTrace_7784184
  have hstable : (prefixWord ++ tailWord_7784184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784184).length < 2 ^ (prefixWord ++ tailWord_7784184).sum := by decide
  have hdescent : baseEnd_7784184 < baseStart_7784184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784201 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 7, 4]
def baseStart_7784201 : Nat := 118140960795 + 7784201 * 2 ^ 59
def prefixEnd_7784201 : Nat := 4983230072969 + 3 ^ 40 * 7784201 * 2
def baseEnd_7784201 : Nat := 1332345541403068003829539

theorem tailTrace_7784201 : CollatzResearch.WordTrace tailWord_7784201 prefixEnd_7784201 1332345541403068003829539 := by
  unfold tailWord_7784201
  simp only [CollatzResearch.WordTrace]
  refine ⟨283913134872176687534128457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189275423248117791689418971 283913134872176687534128457)
  ·
    refine ⟨212934851154132515650596343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283913134872176687534128457 212934851154132515650596343)
    ·
      refine ⟨319402276731198773475894515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212934851154132515650596343 319402276731198773475894515)
      ·
        refine ⟨479103415096798160213841773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319402276731198773475894515 479103415096798160213841773)
        ·
          refine ⟨179663780661299310080190665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479103415096798160213841773 179663780661299310080190665)
          ·
            refine ⟨134747835495974482560142999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179663780661299310080190665 134747835495974482560142999)
            ·
              refine ⟨202121753243961723840214499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134747835495974482560142999 202121753243961723840214499)
              ·
                refine ⟨303182629865942585760321749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202121753243961723840214499 303182629865942585760321749)
                ·
                  refine ⟨7105842887483029353757541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 303182629865942585760321749 7105842887483029353757541)
                  ·
                    refine ⟨1332345541403068003829539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7105842887483029353757541 1332345541403068003829539)
                    ·
                      rfl

theorem cell23_7784201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 4].length) (baseStart_7784201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784201 prefixEnd_7784201 := by exact prefixLift 7784201
  have htrace : WordTrace (prefixWord ++ tailWord_7784201) baseStart_7784201 baseEnd_7784201 := by
    simpa [prefixWord, tailWord_7784201, baseEnd_7784201] using wordTrace_append hprefix tailTrace_7784201
  have hstable : (prefixWord ++ tailWord_7784201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784201).length < 2 ^ (prefixWord ++ tailWord_7784201).sum := by decide
  have hdescent : baseEnd_7784201 < baseStart_7784201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784218 : List Nat := [3, 1, 1, 3, 2, 2, 1, 3, 3, 4]
def baseStart_7784218 : Nat := 118140960795 + 7784218 * 2 ^ 59
def prefixEnd_7784218 : Nat := 4983230072969 + 3 ^ 40 * 7784218 * 2
def baseEnd_7784218 : Nat := 1332348451126776814992013

theorem tailTrace_7784218 : CollatzResearch.WordTrace tailWord_7784218 prefixEnd_7784218 1332348451126776814992013 := by
  unfold tailWord_7784218
  simp only [CollatzResearch.WordTrace]
  refine ⟨70978438728278774859374327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189275836608743399624998205 70978438728278774859374327)
  ·
    refine ⟨106467658092418162289061491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70978438728278774859374327 106467658092418162289061491)
    ·
      refine ⟨159701487138627243433592237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106467658092418162289061491 159701487138627243433592237)
      ·
        refine ⟨59888057676985216287597089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159701487138627243433592237 59888057676985216287597089)
        ·
          refine ⟨44916043257738912215697817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59888057676985216287597089 44916043257738912215697817)
          ·
            refine ⟨33687032443304184161773363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44916043257738912215697817 33687032443304184161773363)
            ·
              refine ⟨50530548664956276242660045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33687032443304184161773363 50530548664956276242660045)
              ·
                refine ⟨18948955749358603590997517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50530548664956276242660045 18948955749358603590997517)
                ·
                  refine ⟨7105858406009476346624069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18948955749358603590997517 7105858406009476346624069)
                  ·
                    refine ⟨1332348451126776814992013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7105858406009476346624069 1332348451126776814992013)
                    ·
                      rfl

theorem cell23_7784218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_7784218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784218 prefixEnd_7784218 := by exact prefixLift 7784218
  have htrace : WordTrace (prefixWord ++ tailWord_7784218) baseStart_7784218 baseEnd_7784218 := by
    simpa [prefixWord, tailWord_7784218, baseEnd_7784218] using wordTrace_append hprefix tailTrace_7784218
  have hstable : (prefixWord ++ tailWord_7784218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784218).length < 2 ^ (prefixWord ++ tailWord_7784218).sum := by decide
  have hdescent : baseEnd_7784218 < baseStart_7784218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784228 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 1, 4, 3]
def baseStart_7784228 : Nat := 118140960795 + 7784228 * 2 ^ 59
def prefixEnd_7784228 : Nat := 4983230072969 + 3 ^ 40 * 7784228 * 2
def baseEnd_7784228 : Nat := 3997050488186875405850993

theorem tailTrace_7784228 : CollatzResearch.WordTrace tailWord_7784228 prefixEnd_7784228 3997050488186875405850993 := by
  unfold tailWord_7784228
  simp only [CollatzResearch.WordTrace]
  refine ⟨141957059821539435572680669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189276079762052580763574225 141957059821539435572680669)
  ·
    refine ⟨53233897433077288339755251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141957059821539435572680669 53233897433077288339755251)
    ·
      refine ⟨79850846149615932509632877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53233897433077288339755251 79850846149615932509632877)
      ·
        refine ⟨29944067306105974691112329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79850846149615932509632877 29944067306105974691112329)
        ·
          refine ⟨22458050479579481018334247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29944067306105974691112329 22458050479579481018334247)
          ·
            refine ⟨33687075719369221527501371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22458050479579481018334247 33687075719369221527501371)
            ·
              refine ⟨50530613579053832291252057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33687075719369221527501371 50530613579053832291252057)
              ·
                refine ⟨37897960184290374218439043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50530613579053832291252057 37897960184290374218439043)
                ·
                  refine ⟨56846940276435561327658565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37897960184290374218439043 56846940276435561327658565)
                  ·
                    refine ⟨10658801301831667748935981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56846940276435561327658565 10658801301831667748935981)
                    ·
                      refine ⟨3997050488186875405850993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10658801301831667748935981 3997050488186875405850993)
                      ·
                        rfl

theorem cell23_7784228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_7784228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784228 prefixEnd_7784228 := by exact prefixLift 7784228
  have htrace : WordTrace (prefixWord ++ tailWord_7784228) baseStart_7784228 baseEnd_7784228 := by
    simpa [prefixWord, tailWord_7784228, baseEnd_7784228] using wordTrace_append hprefix tailTrace_7784228
  have hstable : (prefixWord ++ tailWord_7784228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784228).length < 2 ^ (prefixWord ++ tailWord_7784228).sum := by decide
  have hdescent : baseEnd_7784228 < baseStart_7784228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784262 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_7784262 : Nat := 118140960795 + 7784262 * 2 ^ 59
def prefixEnd_7784262 : Nat := 4983230072969 + 3 ^ 40 * 7784262 * 2
def baseEnd_7784262 : Nat := 3997067946529128272825837

theorem tailTrace_7784262 : CollatzResearch.WordTrace tailWord_7784262 prefixEnd_7784262 3997067946529128272825837 := by
  unfold tailWord_7784262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8872354991404865467253095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 189276906483303796634732693 8872354991404865467253095)
  ·
    refine ⟨13308532487107298200879643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8872354991404865467253095 13308532487107298200879643)
    ·
      refine ⟨19962798730660947301319465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13308532487107298200879643 19962798730660947301319465)
      ·
        refine ⟨14972099047995710475989599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19962798730660947301319465 14972099047995710475989599)
        ·
          refine ⟨22458148571993565713984399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14972099047995710475989599 22458148571993565713984399)
          ·
            refine ⟨33687222857990348570976599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22458148571993565713984399 33687222857990348570976599)
            ·
              refine ⟨50530834286985522856464899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33687222857990348570976599 50530834286985522856464899)
              ·
                refine ⟨75796251430478284284697349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50530834286985522856464899 75796251430478284284697349)
                ·
                  refine ⟨14211797143214678303380753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75796251430478284284697349 14211797143214678303380753)
                  ·
                    refine ⟨10658847857411008727535565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14211797143214678303380753 10658847857411008727535565)
                    ·
                      refine ⟨3997067946529128272825837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10658847857411008727535565 3997067946529128272825837)
                      ·
                        rfl

theorem cell23_7784262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_7784262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784262 prefixEnd_7784262 := by exact prefixLift 7784262
  have htrace : WordTrace (prefixWord ++ tailWord_7784262) baseStart_7784262 baseEnd_7784262 := by
    simpa [prefixWord, tailWord_7784262, baseEnd_7784262] using wordTrace_append hprefix tailTrace_7784262
  have hstable : (prefixWord ++ tailWord_7784262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784262).length < 2 ^ (prefixWord ++ tailWord_7784262).sum := by decide
  have hdescent : baseEnd_7784262 < baseStart_7784262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784302 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 2, 3, 2]
def baseStart_7784302 : Nat := 118140960795 + 7784302 * 2 ^ 59
def prefixEnd_7784302 : Nat := 4983230072969 + 3 ^ 40 * 7784302 * 2
def baseEnd_7784302 : Nat := 3997088485755308116325653

theorem tailTrace_7784302 : CollatzResearch.WordTrace tailWord_7784302 prefixEnd_7784302 3997088485755308116325653 := by
  unfold tailWord_7784302
  simp only [CollatzResearch.WordTrace]
  refine ⟨35489602330601347722944395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189277879096540521189036773 35489602330601347722944395)
  ·
    refine ⟨53234403495902021584416593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35489602330601347722944395 53234403495902021584416593)
    ·
      refine ⟨39925802621926516188312445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53234403495902021584416593 39925802621926516188312445)
      ·
        refine ⟨14972175983222443570617167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39925802621926516188312445 14972175983222443570617167)
        ·
          refine ⟨22458263974833665355925751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14972175983222443570617167 22458263974833665355925751)
          ·
            refine ⟨33687395962250498033888627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22458263974833665355925751 33687395962250498033888627)
            ·
              refine ⟨50531093943375747050832941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33687395962250498033888627 50531093943375747050832941)
              ·
                refine ⟨18949160228765905144062353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50531093943375747050832941 18949160228765905144062353)
                ·
                  refine ⟨14211870171574428858046765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18949160228765905144062353 14211870171574428858046765)
                  ·
                    refine ⟨5329451314340410821767537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14211870171574428858046765 5329451314340410821767537)
                    ·
                      refine ⟨3997088485755308116325653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5329451314340410821767537 3997088485755308116325653)
                      ·
                        rfl

theorem cell23_7784302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_7784302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784302 prefixEnd_7784302 := by exact prefixLift 7784302
  have htrace : WordTrace (prefixWord ++ tailWord_7784302) baseStart_7784302 baseEnd_7784302 := by
    simpa [prefixWord, tailWord_7784302, baseEnd_7784302] using wordTrace_append hprefix tailTrace_7784302
  have hstable : (prefixWord ++ tailWord_7784302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784302).length < 2 ^ (prefixWord ++ tailWord_7784302).sum := by decide
  have hdescent : baseEnd_7784302 < baseStart_7784302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784325 : List Nat := [1, 3, 1, 1, 3, 2, 4, 2, 2, 4]
def baseStart_7784325 : Nat := 118140960795 + 7784325 * 2 ^ 59
def prefixEnd_7784325 : Nat := 4983230072969 + 3 ^ 40 * 7784325 * 2
def baseEnd_7784325 : Nat := 1332366765270120508779349

theorem tailTrace_7784325 : CollatzResearch.WordTrace tailWord_7784325 prefixEnd_7784325 1332366765270120508779349 := by
  unfold tailWord_7784325
  simp only [CollatzResearch.WordTrace]
  refine ⟨283917657523727456711642429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189278438349151637807761619 283917657523727456711642429)
  ·
    refine ⟨106469121571397796266865911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283917657523727456711642429 106469121571397796266865911)
    ·
      refine ⟨159703682357096694400298867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106469121571397796266865911 159703682357096694400298867)
      ·
        refine ⟨239555523535645041600448301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159703682357096694400298867 239555523535645041600448301)
        ·
          refine ⟨89833321325866890600168113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239555523535645041600448301 89833321325866890600168113)
          ·
            refine ⟨67374990994400167950126085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89833321325866890600168113 67374990994400167950126085)
            ·
              refine ⟨12632810811450031490648641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67374990994400167950126085 12632810811450031490648641)
              ·
                refine ⟨9474608108587523617986481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12632810811450031490648641 9474608108587523617986481)
                ·
                  refine ⟨7105956081440642713489861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9474608108587523617986481 7105956081440642713489861)
                  ·
                    refine ⟨1332366765270120508779349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7105956081440642713489861 1332366765270120508779349)
                    ·
                      rfl

theorem cell23_7784325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_7784325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784325 prefixEnd_7784325 := by exact prefixLift 7784325
  have htrace : WordTrace (prefixWord ++ tailWord_7784325) baseStart_7784325 baseEnd_7784325 := by
    simpa [prefixWord, tailWord_7784325, baseEnd_7784325] using wordTrace_append hprefix tailTrace_7784325
  have hstable : (prefixWord ++ tailWord_7784325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784325).length < 2 ^ (prefixWord ++ tailWord_7784325).sum := by decide
  have hdescent : baseEnd_7784325 < baseStart_7784325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784366 : List Nat := [4, 1, 5, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_7784366 : Nat := 118140960795 + 7784366 * 2 ^ 59
def prefixEnd_7784366 : Nat := 4983230072969 + 3 ^ 40 * 7784366 * 2
def baseEnd_7784366 : Nat := 3997121348517195865925359

theorem tailTrace_7784366 : CollatzResearch.WordTrace tailWord_7784366 prefixEnd_7784366 3997121348517195865925359 := by
  unfold tailWord_7784366
  simp only [CollatzResearch.WordTrace]
  refine ⟨35489894114572365089235619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189279435277719280475923301 35489894114572365089235619)
  ·
    refine ⟨53234841171858547633853429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35489894114572365089235619 53234841171858547633853429)
    ·
      refine ⟨4990766359861738840673759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53234841171858547633853429 4990766359861738840673759)
      ·
        refine ⟨7486149539792608261010639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4990766359861738840673759 7486149539792608261010639)
        ·
          refine ⟨11229224309688912391515959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7486149539792608261010639 11229224309688912391515959)
          ·
            refine ⟨16843836464533368587273939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11229224309688912391515959 16843836464533368587273939)
            ·
              refine ⟨25265754696800052880910909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16843836464533368587273939 25265754696800052880910909)
              ·
                refine ⟨9474658011300019830341591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25265754696800052880910909 9474658011300019830341591)
                ·
                  refine ⟨14211987016950029745512387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9474658011300019830341591 14211987016950029745512387)
                  ·
                    refine ⟨21317980525425044618268581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14211987016950029745512387 21317980525425044618268581)
                    ·
                      refine ⟨3997121348517195865925359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21317980525425044618268581 3997121348517195865925359)
                      ·
                        rfl

theorem cell23_7784366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_7784366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784366 prefixEnd_7784366 := by exact prefixLift 7784366
  have htrace : WordTrace (prefixWord ++ tailWord_7784366) baseStart_7784366 baseEnd_7784366 := by
    simpa [prefixWord, tailWord_7784366, baseEnd_7784366] using wordTrace_append hprefix tailTrace_7784366
  have hstable : (prefixWord ++ tailWord_7784366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784366).length < 2 ^ (prefixWord ++ tailWord_7784366).sum := by decide
  have hdescent : baseEnd_7784366 < baseStart_7784366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784369 : List Nat := [1, 2, 2, 4, 2, 3, 2, 1, 1, 2, 3]
def baseStart_7784369 : Nat := 118140960795 + 7784369 * 2 ^ 59
def prefixEnd_7784369 : Nat := 4983230072969 + 3 ^ 40 * 7784369 * 2
def baseEnd_7784369 : Nat := 3997122888959159354187845

theorem tailTrace_7784369 : CollatzResearch.WordTrace tailWord_7784369 prefixEnd_7784369 3997122888959159354187845 := by
  unfold tailWord_7784369
  simp only [CollatzResearch.WordTrace]
  refine ⟨283919262335568052226244161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189279508223712034817496107 283919262335568052226244161)
  ·
    refine ⟨212939446751676039169683121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283919262335568052226244161 212939446751676039169683121)
    ·
      refine ⟨159704585063757029377262341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212939446751676039169683121 159704585063757029377262341)
      ·
        refine ⟨29944609699454443008236689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159704585063757029377262341 29944609699454443008236689)
        ·
          refine ⟨22458457274590832256177517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29944609699454443008236689 22458457274590832256177517)
          ·
            refine ⟨8421921477971562096066569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22458457274590832256177517 8421921477971562096066569)
            ·
              refine ⟨6316441108478671572049927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8421921477971562096066569 6316441108478671572049927)
              ·
                refine ⟨9474661662718007358074891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6316441108478671572049927 9474661662718007358074891)
                ·
                  refine ⟨14211992494077011037112337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9474661662718007358074891 14211992494077011037112337)
                  ·
                    refine ⟨10658994370557758277834253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14211992494077011037112337 10658994370557758277834253)
                    ·
                      refine ⟨3997122888959159354187845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10658994370557758277834253 3997122888959159354187845)
                      ·
                        rfl

theorem cell23_7784369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_7784369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784369 prefixEnd_7784369 := by exact prefixLift 7784369
  have htrace : WordTrace (prefixWord ++ tailWord_7784369) baseStart_7784369 baseEnd_7784369 := by
    simpa [prefixWord, tailWord_7784369, baseEnd_7784369] using wordTrace_append hprefix tailTrace_7784369
  have hstable : (prefixWord ++ tailWord_7784369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784369).length < 2 ^ (prefixWord ++ tailWord_7784369).sum := by decide
  have hdescent : baseEnd_7784369 < baseStart_7784369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784382 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_7784382 : Nat := 118140960795 + 7784382 * 2 ^ 59
def prefixEnd_7784382 : Nat := 4983230072969 + 3 ^ 40 * 7784382 * 2
def baseEnd_7784382 : Nat := 3997129564207667803325285

theorem tailTrace_7784382 : CollatzResearch.WordTrace tailWord_7784382 prefixEnd_7784382 3997129564207667803325285 := by
  unfold tailWord_7784382
  simp only [CollatzResearch.WordTrace]
  refine ⟨35489967060565119430808425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189279824323013970297644933 35489967060565119430808425)
  ·
    refine ⟨26617475295423839573106319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35489967060565119430808425 26617475295423839573106319)
    ·
      refine ⟨39926212943135759359659479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26617475295423839573106319 39926212943135759359659479)
      ·
        refine ⟨59889319414703639039489219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39926212943135759359659479 59889319414703639039489219)
        ·
          refine ⟨89833979122055458559233829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59889319414703639039489219 89833979122055458559233829)
          ·
            refine ⟨16843871085385398479856343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89833979122055458559233829 16843871085385398479856343)
            ·
              refine ⟨25265806628078097719784515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16843871085385398479856343 25265806628078097719784515)
              ·
                refine ⟨37898709942117146579676773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25265806628078097719784515 37898709942117146579676773)
                ·
                  refine ⟨7106008114146964983689395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37898709942117146579676773 7106008114146964983689395)
                  ·
                    refine ⟨10659012171220447475534093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7106008114146964983689395 10659012171220447475534093)
                    ·
                      refine ⟨3997129564207667803325285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10659012171220447475534093 3997129564207667803325285)
                      ·
                        rfl

theorem cell23_7784382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_7784382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784382 prefixEnd_7784382 := by exact prefixLift 7784382
  have htrace : WordTrace (prefixWord ++ tailWord_7784382) baseStart_7784382 baseEnd_7784382 := by
    simpa [prefixWord, tailWord_7784382, baseEnd_7784382] using wordTrace_append hprefix tailTrace_7784382
  have hstable : (prefixWord ++ tailWord_7784382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784382).length < 2 ^ (prefixWord ++ tailWord_7784382).sum := by decide
  have hdescent : baseEnd_7784382 < baseStart_7784382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784398 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 2, 6]
def baseStart_7784398 : Nat := 118140960795 + 7784398 * 2 ^ 59
def prefixEnd_7784398 : Nat := 4983230072969 + 3 ^ 40 * 7784398 * 2
def baseEnd_7784398 : Nat := 1332379259966046580241737

theorem tailTrace_7784398 : CollatzResearch.WordTrace tailWord_7784398 prefixEnd_7784398 1332379259966046580241737 := by
  unfold tailWord_7784398
  simp only [CollatzResearch.WordTrace]
  refine ⟨35490040006557873772381231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189280213368308660119366565 35490040006557873772381231)
  ·
    refine ⟨53235060009836810658571847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35490040006557873772381231 53235060009836810658571847)
    ·
      refine ⟨79852590014755215987857771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53235060009836810658571847 79852590014755215987857771)
      ·
        refine ⟨119778885022132823981786657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79852590014755215987857771 119778885022132823981786657)
        ·
          refine ⟨89834163766599617986339993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119778885022132823981786657 89834163766599617986339993)
          ·
            refine ⟨67375622824949713489754995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89834163766599617986339993 67375622824949713489754995)
            ·
              refine ⟨101063434237424570234632493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67375622824949713489754995 101063434237424570234632493)
              ·
                refine ⟨37898787839034213837987185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101063434237424570234632493 37898787839034213837987185)
                ·
                  refine ⟨28424090879275660378490389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37898787839034213837987185 28424090879275660378490389)
                  ·
                    refine ⟨1332379259966046580241737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28424090879275660378490389 1332379259966046580241737)
                    ·
                      rfl

theorem cell23_7784398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_7784398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784398 prefixEnd_7784398 := by exact prefixLift 7784398
  have htrace : WordTrace (prefixWord ++ tailWord_7784398) baseStart_7784398 baseEnd_7784398 := by
    simpa [prefixWord, tailWord_7784398, baseEnd_7784398] using wordTrace_append hprefix tailTrace_7784398
  have hstable : (prefixWord ++ tailWord_7784398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784398).length < 2 ^ (prefixWord ++ tailWord_7784398).sum := by decide
  have hdescent : baseEnd_7784398 < baseStart_7784398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784408 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 2, 1, 5]
def baseStart_7784408 : Nat := 118140960795 + 7784408 * 2 ^ 59
def prefixEnd_7784408 : Nat := 4983230072969 + 3 ^ 40 * 7784408 * 2
def baseEnd_7784408 : Nat := 3997142914704684701600165

theorem tailTrace_7784408 : CollatzResearch.WordTrace tailWord_7784408 prefixEnd_7784408 3997142914704684701600165 := by
  unfold tailWord_7784408
  simp only [CollatzResearch.WordTrace]
  refine ⟨141960342391213380943456939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189280456521617841257942585 141960342391213380943456939)
  ·
    refine ⟨212940513586820071415185409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141960342391213380943456939 212940513586820071415185409)
    ·
      refine ⟨159705385190115053561389057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212940513586820071415185409 159705385190115053561389057)
      ·
        refine ⟨119779038892586290171041793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159705385190115053561389057 119779038892586290171041793)
        ·
          refine ⟨89834279169439717628281345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119779038892586290171041793 89834279169439717628281345)
          ·
            refine ⟨67375709377079788221211009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89834279169439717628281345 67375709377079788221211009)
            ·
              refine ⟨50531782032809841165908257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67375709377079788221211009 50531782032809841165908257)
              ·
                refine ⟨37898836524607380874431193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50531782032809841165908257 37898836524607380874431193)
                ·
                  refine ⟨28424127393455535655823395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37898836524607380874431193 28424127393455535655823395)
                  ·
                    refine ⟨42636191090183303483735093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28424127393455535655823395 42636191090183303483735093)
                    ·
                      refine ⟨3997142914704684701600165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42636191090183303483735093 3997142914704684701600165)
                      ·
                        rfl

theorem cell23_7784408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_7784408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784408 prefixEnd_7784408 := by exact prefixLift 7784408
  have htrace : WordTrace (prefixWord ++ tailWord_7784408) baseStart_7784408 baseEnd_7784408 := by
    simpa [prefixWord, tailWord_7784408, baseEnd_7784408] using wordTrace_append hprefix tailTrace_7784408
  have hstable : (prefixWord ++ tailWord_7784408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784408).length < 2 ^ (prefixWord ++ tailWord_7784408).sum := by decide
  have hdescent : baseEnd_7784408 < baseStart_7784408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784409 : List Nat := [1, 2, 1, 2, 6, 1, 2, 2, 1, 3, 2]
def baseStart_7784409 : Nat := 118140960795 + 7784409 * 2 ^ 59
def prefixEnd_7784409 : Nat := 4983230072969 + 3 ^ 40 * 7784409 * 2
def baseEnd_7784409 : Nat := 3997143428185339197687661

theorem tailTrace_7784409 : CollatzResearch.WordTrace tailWord_7784409 prefixEnd_7784409 3997143428185339197687661 := by
  unfold tailWord_7784409
  simp only [CollatzResearch.WordTrace]
  refine ⟨283920721255423139057700281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189280480836948759371800187 283920721255423139057700281)
  ·
    refine ⟨212940540941567354293275211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283920721255423139057700281 212940540941567354293275211)
    ·
      refine ⟨319410811412351031439912817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212940540941567354293275211 319410811412351031439912817)
      ·
        refine ⟨239558108559263273579934613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319410811412351031439912817 239558108559263273579934613)
        ·
          refine ⟨11229286338715465949059435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 239558108559263273579934613 11229286338715465949059435)
          ·
            refine ⟨16843929508073198923589153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11229286338715465949059435 16843929508073198923589153)
            ·
              refine ⟨12632947131054899192691865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16843929508073198923589153 12632947131054899192691865)
              ·
                refine ⟨9474710348291174394518899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12632947131054899192691865 9474710348291174394518899)
                ·
                  refine ⟨14212065522436761591778349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9474710348291174394518899 14212065522436761591778349)
                  ·
                    refine ⟨5329524570913785596916881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14212065522436761591778349 5329524570913785596916881)
                    ·
                      refine ⟨3997143428185339197687661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5329524570913785596916881 3997143428185339197687661)
                      ·
                        rfl

theorem cell23_7784409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 3, 2].length) (baseStart_7784409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784409 prefixEnd_7784409 := by exact prefixLift 7784409
  have htrace : WordTrace (prefixWord ++ tailWord_7784409) baseStart_7784409 baseEnd_7784409 := by
    simpa [prefixWord, tailWord_7784409, baseEnd_7784409] using wordTrace_append hprefix tailTrace_7784409
  have hstable : (prefixWord ++ tailWord_7784409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784409).length < 2 ^ (prefixWord ++ tailWord_7784409).sum := by decide
  have hdescent : baseEnd_7784409 < baseStart_7784409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784445 : List Nat := [1, 4, 1, 1, 1, 2, 2, 6, 5]
def baseStart_7784445 : Nat := 118140960795 + 7784445 * 2 ^ 59
def prefixEnd_7784445 : Nat := 4983230072969 + 3 ^ 40 * 7784445 * 2
def baseEnd_7784445 : Nat := 444129101498766784093055

theorem tailTrace_7784445 : CollatzResearch.WordTrace tailWord_7784445 prefixEnd_7784445 444129101498766784093055 := by
  unfold tailWord_7784445
  simp only [CollatzResearch.WordTrace]
  refine ⟨283922034283292717206010789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189281356188861811470673859 283922034283292717206010789)
  ·
    refine ⟨53235381428117384476127023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283922034283292717206010789 53235381428117384476127023)
    ·
      refine ⟨79853072142176076714190535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53235381428117384476127023 79853072142176076714190535)
      ·
        refine ⟨119779608213264115071285803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79853072142176076714190535 119779608213264115071285803)
        ·
          refine ⟨179669412319896172606928705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119779608213264115071285803 179669412319896172606928705)
          ·
            refine ⟨134752059239922129455196529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179669412319896172606928705 134752059239922129455196529)
            ·
              refine ⟨101064044429941597091397397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134752059239922129455196529 101064044429941597091397397)
              ·
                refine ⟨4737377082653512363659253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101064044429941597091397397 4737377082653512363659253)
                ·
                  refine ⟨444129101498766784093055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4737377082653512363659253 444129101498766784093055)
                  ·
                    rfl

theorem cell23_7784445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_7784445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784445 prefixEnd_7784445 := by exact prefixLift 7784445
  have htrace : WordTrace (prefixWord ++ tailWord_7784445) baseStart_7784445 baseEnd_7784445 := by
    simpa [prefixWord, tailWord_7784445, baseEnd_7784445] using wordTrace_append hprefix tailTrace_7784445
  have hstable : (prefixWord ++ tailWord_7784445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784445).length < 2 ^ (prefixWord ++ tailWord_7784445).sum := by decide
  have hdescent : baseEnd_7784445 < baseStart_7784445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784512 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 2, 4, 2]
def baseStart_7784512 : Nat := 118140960795 + 7784512 * 2 ^ 59
def prefixEnd_7784512 : Nat := 4983230072969 + 3 ^ 40 * 7784512 * 2
def baseEnd_7784512 : Nat := 3997196316692752294699687

theorem tailTrace_7784512 : CollatzResearch.WordTrace tailWord_7784512 prefixEnd_7784512 3997196316692752294699687 := by
  unfold tailWord_7784512
  simp only [CollatzResearch.WordTrace]
  refine ⟨141962238987024993824349895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189282985316033325099133193 141962238987024993824349895)
  ·
    refine ⟨212943358480537490736524843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141962238987024993824349895 212943358480537490736524843)
    ·
      refine ⟨319415037720806236104787265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212943358480537490736524843 319415037720806236104787265)
      ·
        refine ⟨239561278290604677078590449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319415037720806236104787265 239561278290604677078590449)
        ·
          refine ⟨179670958717953507808942837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239561278290604677078590449 179670958717953507808942837)
          ·
            refine ⟨16844152379808141357088391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179670958717953507808942837 16844152379808141357088391)
            ·
              refine ⟨25266228569712212035632587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16844152379808141357088391 25266228569712212035632587)
              ·
                refine ⟨37899342854568318053448881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25266228569712212035632587 37899342854568318053448881)
                ·
                  refine ⟨28424507140926238540086661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37899342854568318053448881 28424507140926238540086661)
                  ·
                    refine ⟨5329595088923669726266249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28424507140926238540086661 5329595088923669726266249)
                    ·
                      refine ⟨3997196316692752294699687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5329595088923669726266249 3997196316692752294699687)
                      ·
                        rfl

theorem cell23_7784512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 2, 4, 2].length) (baseStart_7784512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784512 prefixEnd_7784512 := by exact prefixLift 7784512
  have htrace : WordTrace (prefixWord ++ tailWord_7784512) baseStart_7784512 baseEnd_7784512 := by
    simpa [prefixWord, tailWord_7784512, baseEnd_7784512] using wordTrace_append hprefix tailTrace_7784512
  have hstable : (prefixWord ++ tailWord_7784512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784512).length < 2 ^ (prefixWord ++ tailWord_7784512).sum := by decide
  have hdescent : baseEnd_7784512 < baseStart_7784512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784572 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 1, 5, 2]
def baseStart_7784572 : Nat := 118140960795 + 7784572 * 2 ^ 59
def prefixEnd_7784572 : Nat := 4983230072969 + 3 ^ 40 * 7784572 * 2
def baseEnd_7784572 : Nat := 3997227125532022059949411

theorem tailTrace_7784572 : CollatzResearch.WordTrace tailWord_7784572 prefixEnd_7784572 3997227125532022059949411 := by
  unfold tailWord_7784572
  simp only [CollatzResearch.WordTrace]
  refine ⟨141963333176916308947941985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189284444235888411930589313 141963333176916308947941985)
  ·
    refine ⟨106472499882687231710956489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141963333176916308947941985 106472499882687231710956489)
    ·
      refine ⟨79854374912015423783217367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106472499882687231710956489 79854374912015423783217367)
      ·
        refine ⟨119781562368023135674826051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79854374912015423783217367 119781562368023135674826051)
        ·
          refine ⟨179672343552034703512239077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119781562368023135674826051 179672343552034703512239077)
          ·
            refine ⟨33688564416006506908544827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179672343552034703512239077 33688564416006506908544827)
            ·
              refine ⟨50532846624009760362817241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33688564416006506908544827 50532846624009760362817241)
              ·
                refine ⟨37899634968007320272112931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50532846624009760362817241 37899634968007320272112931)
                ·
                  refine ⟨56849452452010980408169397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37899634968007320272112931 56849452452010980408169397)
                  ·
                    refine ⟨5329636167376029413265881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56849452452010980408169397 5329636167376029413265881)
                    ·
                      refine ⟨3997227125532022059949411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5329636167376029413265881 3997227125532022059949411)
                      ·
                        rfl

theorem cell23_7784572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_7784572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784572 prefixEnd_7784572 := by exact prefixLift 7784572
  have htrace : WordTrace (prefixWord ++ tailWord_7784572) baseStart_7784572 baseEnd_7784572 := by
    simpa [prefixWord, tailWord_7784572, baseEnd_7784572] using wordTrace_append hprefix tailTrace_7784572
  have hstable : (prefixWord ++ tailWord_7784572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784572).length < 2 ^ (prefixWord ++ tailWord_7784572).sum := by decide
  have hdescent : baseEnd_7784572 < baseStart_7784572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784636 : List Nat := [2, 2, 2, 3, 3, 2, 1, 2, 1, 1, 4]
def baseStart_7784636 : Nat := 118140960795 + 7784636 * 2 ^ 59
def prefixEnd_7784636 : Nat := 4983230072969 + 3 ^ 40 * 7784636 * 2
def baseEnd_7784636 : Nat := 3997259988293909809549117

theorem tailTrace_7784636 : CollatzResearch.WordTrace tailWord_7784636 prefixEnd_7784636 3997259988293909809549117 := by
  unfold tailWord_7784636
  simp only [CollatzResearch.WordTrace]
  refine ⟨141964500312800378413106881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189286000417067171217475841 141964500312800378413106881)
  ·
    refine ⟨106473375234600283809830161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141964500312800378413106881 106473375234600283809830161)
    ·
      refine ⟨79855031425950212857372621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106473375234600283809830161 79855031425950212857372621)
      ·
        refine ⟨29945636784731329821514733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79855031425950212857372621 29945636784731329821514733)
        ·
          refine ⟨11229613794274248683068025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29945636784731329821514733 11229613794274248683068025)
          ·
            refine ⟨8422210345705686512301019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11229613794274248683068025 8422210345705686512301019)
            ·
              refine ⟨12633315518558529768451529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8422210345705686512301019 12633315518558529768451529)
              ·
                refine ⟨9474986638918897326338647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12633315518558529768451529 9474986638918897326338647)
                ·
                  refine ⟨14212479958378345989507971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9474986638918897326338647 14212479958378345989507971)
                  ·
                    refine ⟨21318719937567518984261957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14212479958378345989507971 21318719937567518984261957)
                    ·
                      refine ⟨3997259988293909809549117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21318719937567518984261957 3997259988293909809549117)
                      ·
                        rfl

theorem cell23_7784636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_7784636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784636 prefixEnd_7784636 := by exact prefixLift 7784636
  have htrace : WordTrace (prefixWord ++ tailWord_7784636) baseStart_7784636 baseEnd_7784636 := by
    simpa [prefixWord, tailWord_7784636, baseEnd_7784636] using wordTrace_append hprefix tailTrace_7784636
  have hstable : (prefixWord ++ tailWord_7784636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784636).length < 2 ^ (prefixWord ++ tailWord_7784636).sum := by decide
  have hdescent : baseEnd_7784636 < baseStart_7784636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784665 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 2, 2, 5]
def baseStart_7784665 : Nat := 118140960795 + 7784665 * 2 ^ 59
def prefixEnd_7784665 : Nat := 4983230072969 + 3 ^ 40 * 7784665 * 2
def baseEnd_7784665 : Nat := 3997274879232890196086483

theorem tailTrace_7784665 : CollatzResearch.WordTrace tailWord_7784665 prefixEnd_7784665 3997274879232890196086483 := by
  unfold tailWord_7784665
  simp only [CollatzResearch.WordTrace]
  refine ⟨283930058342495694779019449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189286705561663796519346299 283930058342495694779019449)
  ·
    refine ⟨212947543756871771084264587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283930058342495694779019449 212947543756871771084264587)
    ·
      refine ⟨319421315635307656626396881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212947543756871771084264587 319421315635307656626396881)
      ·
        refine ⟨239565986726480742469797661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319421315635307656626396881 239565986726480742469797661)
        ·
          refine ⟨89837245022430278426174123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239565986726480742469797661 89837245022430278426174123)
          ·
            refine ⟨134755867533645417639261185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89837245022430278426174123 134755867533645417639261185)
            ·
              refine ⟨101066900650234063229445889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134755867533645417639261185 101066900650234063229445889)
              ·
                refine ⟨75800175487675547422084417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101066900650234063229445889 75800175487675547422084417)
                ·
                  refine ⟨56850131615756660566563313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75800175487675547422084417 56850131615756660566563313)
                  ·
                    refine ⟨42637598711817495424922485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56850131615756660566563313 42637598711817495424922485)
                    ·
                      refine ⟨3997274879232890196086483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42637598711817495424922485 3997274879232890196086483)
                      ·
                        rfl

theorem cell23_7784665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_7784665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784665 prefixEnd_7784665 := by exact prefixLift 7784665
  have htrace : WordTrace (prefixWord ++ tailWord_7784665) baseStart_7784665 baseEnd_7784665 := by
    simpa [prefixWord, tailWord_7784665, baseEnd_7784665] using wordTrace_append hprefix tailTrace_7784665
  have hstable : (prefixWord ++ tailWord_7784665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784665).length < 2 ^ (prefixWord ++ tailWord_7784665).sum := by decide
  have hdescent : baseEnd_7784665 < baseStart_7784665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784702 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_7784702 : Nat := 118140960795 + 7784702 * 2 ^ 59
def prefixEnd_7784702 : Nat := 4983230072969 + 3 ^ 40 * 7784702 * 2
def baseEnd_7784702 : Nat := 1332431292672368850441271

theorem tailTrace_7784702 : CollatzResearch.WordTrace tailWord_7784702 prefixEnd_7784702 1332431292672368850441271 := by
  unfold tailWord_7784702
  simp only [CollatzResearch.WordTrace]
  refine ⟨35491425980420206262264545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189287605228907766732077573 35491425980420206262264545)
  ·
    refine ⟨26618569485315154696698409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35491425980420206262264545 26618569485315154696698409)
    ·
      refine ⟨19963927113986366022523807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26618569485315154696698409 19963927113986366022523807)
      ·
        refine ⟨29945890670979549033785711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19963927113986366022523807 29945890670979549033785711)
        ·
          refine ⟨44918836006469323550678567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29945890670979549033785711 44918836006469323550678567)
          ·
            refine ⟨67378254009703985326017851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44918836006469323550678567 67378254009703985326017851)
            ·
              refine ⟨101067381014555977989026777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67378254009703985326017851 101067381014555977989026777)
              ·
                refine ⟨75800535760916983491770083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101067381014555977989026777 75800535760916983491770083)
                ·
                  refine ⟨113700803641375475237655125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75800535760916983491770083 113700803641375475237655125)
                  ·
                    refine ⟨1332431292672368850441271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113700803641375475237655125 1332431292672368850441271)
                    ·
                      rfl

theorem cell23_7784702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_7784702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784702 prefixEnd_7784702 := by exact prefixLift 7784702
  have htrace : WordTrace (prefixWord ++ tailWord_7784702) baseStart_7784702 baseEnd_7784702 := by
    simpa [prefixWord, tailWord_7784702, baseEnd_7784702] using wordTrace_append hprefix tailTrace_7784702
  have hstable : (prefixWord ++ tailWord_7784702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784702).length < 2 ^ (prefixWord ++ tailWord_7784702).sum := by decide
  have hdescent : baseEnd_7784702 < baseStart_7784702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784713 : List Nat := [1, 2, 1, 1, 3, 6, 2, 1, 1, 3, 2]
def baseStart_7784713 : Nat := 118140960795 + 7784713 * 2 ^ 59
def prefixEnd_7784713 : Nat := 4983230072969 + 3 ^ 40 * 7784713 * 2
def baseEnd_7784713 : Nat := 3997299526304306008286263

theorem tailTrace_7784713 : CollatzResearch.WordTrace tailWord_7784713 prefixEnd_7784713 3997299526304306008286263 := by
  unfold tailWord_7784713
  simp only [CollatzResearch.WordTrace]
  refine ⟨283931809046321798976766793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189287872697547865984511195 283931809046321798976766793)
  ·
    refine ⟨212948856784741349232575095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283931809046321798976766793 212948856784741349232575095)
    ·
      refine ⟨319423285177112023848862643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212948856784741349232575095 319423285177112023848862643)
      ·
        refine ⟨479134927765668035773293965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319423285177112023848862643 479134927765668035773293965)
        ·
          refine ⟨179675597912125513414985237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479134927765668035773293965 179675597912125513414985237)
          ·
            refine ⟨8422293652130883441327433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 179675597912125513414985237 8422293652130883441327433)
            ·
              refine ⟨6316720239098162580995575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8422293652130883441327433 6316720239098162580995575)
              ·
                refine ⟨9475080358647243871493363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6316720239098162580995575 9475080358647243871493363)
                ·
                  refine ⟨14212620537970865807240045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9475080358647243871493363 14212620537970865807240045)
                  ·
                    refine ⟨5329732701739074677715017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14212620537970865807240045 5329732701739074677715017)
                    ·
                      refine ⟨3997299526304306008286263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5329732701739074677715017 3997299526304306008286263)
                      ·
                        rfl

theorem cell23_7784713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 1, 3, 2].length) (baseStart_7784713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784713 prefixEnd_7784713 := by exact prefixLift 7784713
  have htrace : WordTrace (prefixWord ++ tailWord_7784713) baseStart_7784713 baseEnd_7784713 := by
    simpa [prefixWord, tailWord_7784713, baseEnd_7784713] using wordTrace_append hprefix tailTrace_7784713
  have hstable : (prefixWord ++ tailWord_7784713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784713).length < 2 ^ (prefixWord ++ tailWord_7784713).sum := by decide
  have hdescent : baseEnd_7784713 < baseStart_7784713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784715 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 9]
def baseStart_7784715 : Nat := 118140960795 + 7784715 * 2 ^ 59
def prefixEnd_7784715 : Nat := 4983230072969 + 3 ^ 40 * 7784715 * 2
def baseEnd_7784715 : Nat := 444144505918401666717917

theorem tailTrace_7784715 : CollatzResearch.WordTrace tailWord_7784715 prefixEnd_7784715 444144505918401666717917 := by
  unfold tailWord_7784715
  simp only [CollatzResearch.WordTrace]
  refine ⟨283931881992314553318339599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189287921328209702212226399 283931881992314553318339599)
  ·
    refine ⟨425897822988471829977509399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283931881992314553318339599 425897822988471829977509399)
    ·
      refine ⟨638846734482707744966264099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425897822988471829977509399 638846734482707744966264099)
      ·
        refine ⟨958270101724061617449396149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638846734482707744966264099 958270101724061617449396149)
        ·
          refine ⟨89837822036630776635880889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 958270101724061617449396149 89837822036630776635880889)
          ·
            refine ⟨67378366527473082476910667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89837822036630776635880889 67378366527473082476910667)
            ·
              refine ⟨101067549791209623715366001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67378366527473082476910667 101067549791209623715366001)
              ·
                refine ⟨75800662343407217786524501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101067549791209623715366001 75800662343407217786524501)
                ·
                  refine ⟨444144505918401666717917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75800662343407217786524501 444144505918401666717917)
                  ·
                    rfl

theorem cell23_7784715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 9].length) (baseStart_7784715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784715 prefixEnd_7784715 := by exact prefixLift 7784715
  have htrace : WordTrace (prefixWord ++ tailWord_7784715) baseStart_7784715 baseEnd_7784715 := by
    simpa [prefixWord, tailWord_7784715, baseEnd_7784715] using wordTrace_append hprefix tailTrace_7784715
  have hstable : (prefixWord ++ tailWord_7784715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784715).length < 2 ^ (prefixWord ++ tailWord_7784715).sum := by decide
  have hdescent : baseEnd_7784715 < baseStart_7784715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784762 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 1, 7]
def baseStart_7784762 : Nat := 118140960795 + 7784762 * 2 ^ 59
def prefixEnd_7784762 : Nat := 4983230072969 + 3 ^ 40 * 7784762 * 2
def baseEnd_7784762 : Nat := 1332441562285458772191179

theorem tailTrace_7784762 : CollatzResearch.WordTrace tailWord_7784762 prefixEnd_7784762 1332441562285458772191179 := by
  unfold tailWord_7784762
  simp only [CollatzResearch.WordTrace]
  refine ⟨70983399055786070086325135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189289064148762853563533693 70983399055786070086325135)
  ·
    refine ⟨106475098583679105129487703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70983399055786070086325135 106475098583679105129487703)
    ·
      refine ⟨159712647875518657694231555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106475098583679105129487703 159712647875518657694231555)
      ·
        refine ⟨239568971813277986541347333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159712647875518657694231555 239568971813277986541347333)
        ·
          refine ⟨44919182214989622476502625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239568971813277986541347333 44919182214989622476502625)
          ·
            refine ⟨33689386661242216857376969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44919182214989622476502625 33689386661242216857376969)
            ·
              refine ⟨25267039995931662643032727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33689386661242216857376969 25267039995931662643032727)
              ·
                refine ⟨37900559993897493964549091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25267039995931662643032727 37900559993897493964549091)
                ·
                  refine ⟨56850839990846240946823637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37900559993897493964549091 56850839990846240946823637)
                  ·
                    refine ⟨1332441562285458772191179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56850839990846240946823637 1332441562285458772191179)
                    ·
                      rfl

theorem cell23_7784762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_7784762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784762 prefixEnd_7784762 := by exact prefixLift 7784762
  have htrace : WordTrace (prefixWord ++ tailWord_7784762) baseStart_7784762 baseEnd_7784762 := by
    simpa [prefixWord, tailWord_7784762, baseEnd_7784762] using wordTrace_append hprefix tailTrace_7784762
  have hstable : (prefixWord ++ tailWord_7784762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784762).length < 2 ^ (prefixWord ++ tailWord_7784762).sum := by decide
  have hdescent : baseEnd_7784762 < baseStart_7784762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784766 : List Nat := [4, 2, 1, 2, 1, 2, 3, 3, 5]
def baseStart_7784766 : Nat := 118140960795 + 7784766 * 2 ^ 59
def prefixEnd_7784766 : Nat := 4983230072969 + 3 ^ 40 * 7784766 * 2
def baseEnd_7784766 : Nat := 444147415642110477880391

theorem tailTrace_7784766 : CollatzResearch.WordTrace tailWord_7784766 prefixEnd_7784766 444147415642110477880391 := by
  unfold tailWord_7784766
  simp only [CollatzResearch.WordTrace]
  refine ⟨35491717764391223628555769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189289161410086526018964101 35491717764391223628555769)
  ·
    refine ⟨26618788323293417721416827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35491717764391223628555769 26618788323293417721416827)
    ·
      refine ⟨39928182484940126582125241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26618788323293417721416827 39928182484940126582125241)
      ·
        refine ⟨29946136863705094936593931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39928182484940126582125241 29946136863705094936593931)
        ·
          refine ⟨44919205295557642404890897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29946136863705094936593931 44919205295557642404890897)
          ·
            refine ⟨33689403971668231803668173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44919205295557642404890897 33689403971668231803668173)
            ·
              refine ⟨12633526489375586926375565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33689403971668231803668173 12633526489375586926375565)
              ·
                refine ⟨4737572433515845097390837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12633526489375586926375565 4737572433515845097390837)
                ·
                  refine ⟨444147415642110477880391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4737572433515845097390837 444147415642110477880391)
                  ·
                    rfl

theorem cell23_7784766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_7784766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784766 prefixEnd_7784766 := by exact prefixLift 7784766
  have htrace : WordTrace (prefixWord ++ tailWord_7784766) baseStart_7784766 baseEnd_7784766 := by
    simpa [prefixWord, tailWord_7784766, baseEnd_7784766] using wordTrace_append hprefix tailTrace_7784766
  have hstable : (prefixWord ++ tailWord_7784766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784766).length < 2 ^ (prefixWord ++ tailWord_7784766).sum := by decide
  have hdescent : baseEnd_7784766 < baseStart_7784766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784782 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_7784782 : Nat := 118140960795 + 7784782 * 2 ^ 59
def prefixEnd_7784782 : Nat := 4983230072969 + 3 ^ 40 * 7784782 * 2
def baseEnd_7784782 : Nat := 3997334956469466238323445

theorem tailTrace_7784782 : CollatzResearch.WordTrace tailWord_7784782 prefixEnd_7784782 3997334956469466238323445 := by
  unfold tailWord_7784782
  simp only [CollatzResearch.WordTrace]
  refine ⟨35491790710383977970128575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189289550455381215840685733 35491790710383977970128575)
  ·
    refine ⟨53237686065575966955192863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35491790710383977970128575 53237686065575966955192863)
    ·
      refine ⟨79856529098363950432789295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53237686065575966955192863 79856529098363950432789295)
      ·
        refine ⟨119784793647545925649183943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79856529098363950432789295 119784793647545925649183943)
        ·
          refine ⟨179677190471318888473775915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119784793647545925649183943 179677190471318888473775915)
          ·
            refine ⟨269515785706978332710663873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179677190471318888473775915 269515785706978332710663873)
            ·
              refine ⟨202136839280233749532997905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269515785706978332710663873 202136839280233749532997905)
              ·
                refine ⟨151602629460175312149748429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202136839280233749532997905 151602629460175312149748429)
                ·
                  refine ⟨56850986047565742056155661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151602629460175312149748429 56850986047565742056155661)
                  ·
                    refine ⟨21319119767837153271058373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56850986047565742056155661 21319119767837153271058373)
                    ·
                      refine ⟨3997334956469466238323445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21319119767837153271058373 3997334956469466238323445)
                      ·
                        rfl

theorem cell23_7784782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_7784782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784782 prefixEnd_7784782 := by exact prefixLift 7784782
  have htrace : WordTrace (prefixWord ++ tailWord_7784782) baseStart_7784782 baseEnd_7784782 := by
    simpa [prefixWord, tailWord_7784782, baseEnd_7784782] using wordTrace_append hprefix tailTrace_7784782
  have hstable : (prefixWord ++ tailWord_7784782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784782).length < 2 ^ (prefixWord ++ tailWord_7784782).sum := by decide
  have hdescent : baseEnd_7784782 < baseStart_7784782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784789 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 1, 2, 5]
def baseStart_7784789 : Nat := 118140960795 + 7784789 * 2 ^ 59
def prefixEnd_7784789 : Nat := 4983230072969 + 3 ^ 40 * 7784789 * 2
def baseEnd_7784789 : Nat := 3997338550834047710935913

theorem tailTrace_7784789 : CollatzResearch.WordTrace tailWord_7784789 prefixEnd_7784789 3997338550834047710935913 := by
  unfold tailWord_7784789
  simp only [CollatzResearch.WordTrace]
  refine ⟨283934580994046463956533421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189289720662697642637688947 283934580994046463956533421)
  ·
    refine ⟨106475467872767423983700033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283934580994046463956533421 106475467872767423983700033)
    ·
      refine ⟨79856600904575567987775025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106475467872767423983700033 79856600904575567987775025)
      ·
        refine ⟨59892450678431675990831269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79856600904575567987775025 59892450678431675990831269)
        ·
          refine ⟨11229834502205939248280863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59892450678431675990831269 11229834502205939248280863)
          ·
            refine ⟨16844751753308908872421295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11229834502205939248280863 16844751753308908872421295)
            ·
              refine ⟨25267127629963363308631943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16844751753308908872421295 25267127629963363308631943)
              ·
                refine ⟨37900691444945044962947915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25267127629963363308631943 37900691444945044962947915)
                ·
                  refine ⟨56851037167417567444421873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37900691444945044962947915 56851037167417567444421873)
                  ·
                    refine ⟨42638277875563175583316405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56851037167417567444421873 42638277875563175583316405)
                    ·
                      refine ⟨3997338550834047710935913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42638277875563175583316405 3997338550834047710935913)
                      ·
                        rfl

theorem cell23_7784789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_7784789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784789 prefixEnd_7784789 := by exact prefixLift 7784789
  have htrace : WordTrace (prefixWord ++ tailWord_7784789) baseStart_7784789 baseEnd_7784789 := by
    simpa [prefixWord, tailWord_7784789, baseEnd_7784789] using wordTrace_append hprefix tailTrace_7784789
  have hstable : (prefixWord ++ tailWord_7784789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784789).length < 2 ^ (prefixWord ++ tailWord_7784789).sum := by decide
  have hdescent : baseEnd_7784789 < baseStart_7784789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784799 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 2, 4, 2]
def baseStart_7784799 : Nat := 118140960795 + 7784799 * 2 ^ 59
def prefixEnd_7784799 : Nat := 4983230072969 + 3 ^ 40 * 7784799 * 2
def baseEnd_7784799 : Nat := 3997343685640592671810867

theorem tailTrace_7784799 : CollatzResearch.WordTrace tailWord_7784799 prefixEnd_7784799 3997343685640592671810867 := by
  unfold tailWord_7784799
  simp only [CollatzResearch.WordTrace]
  refine ⟨283934945724010235664397451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189289963816006823776264967 283934945724010235664397451)
  ·
    refine ⟨425902418586015353496596177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283934945724010235664397451 425902418586015353496596177)
    ·
      refine ⟨319426813939511515122447133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425902418586015353496596177 319426813939511515122447133)
      ·
        refine ⟨119785055227316818170917675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319426813939511515122447133 119785055227316818170917675)
        ·
          refine ⟨179677582840975227256376513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119785055227316818170917675 179677582840975227256376513)
          ·
            refine ⟨134758187130731420442282385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179677582840975227256376513 134758187130731420442282385)
            ·
              refine ⟨101068640348048565331711789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134758187130731420442282385 101068640348048565331711789)
              ·
                refine ⟨37900740130518211999391921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101068640348048565331711789 37900740130518211999391921)
                ·
                  refine ⟨28425555097888658999543941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37900740130518211999391921 28425555097888658999543941)
                  ·
                    refine ⟨5329791580854123562414489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28425555097888658999543941 5329791580854123562414489)
                    ·
                      refine ⟨3997343685640592671810867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5329791580854123562414489 3997343685640592671810867)
                      ·
                        rfl

theorem cell23_7784799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_7784799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784799 prefixEnd_7784799 := by exact prefixLift 7784799
  have htrace : WordTrace (prefixWord ++ tailWord_7784799) baseStart_7784799 baseEnd_7784799 := by
    simpa [prefixWord, tailWord_7784799, baseEnd_7784799] using wordTrace_append hprefix tailTrace_7784799
  have hstable : (prefixWord ++ tailWord_7784799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784799).length < 2 ^ (prefixWord ++ tailWord_7784799).sum := by decide
  have hdescent : baseEnd_7784799 < baseStart_7784799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784839 : List Nat := [1, 1, 4, 2, 2, 1, 4, 2, 6]
def baseStart_7784839 : Nat := 118140960795 + 7784839 * 2 ^ 59
def prefixEnd_7784839 : Nat := 4983230072969 + 3 ^ 40 * 7784839 * 2
def baseEnd_7784839 : Nat := 444151580540752501701187

theorem tailTrace_7784839 : CollatzResearch.WordTrace tailWord_7784839 prefixEnd_7784839 444151580540752501701187 := by
  unfold tailWord_7784839
  simp only [CollatzResearch.WordTrace]
  refine ⟨283936404643865322495853571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189290936429243548330569047 283936404643865322495853571)
  ·
    refine ⟨425904606965797983743780357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283936404643865322495853571 425904606965797983743780357)
    ·
      refine ⟨79857113806087121951958817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425904606965797983743780357 79857113806087121951958817)
      ·
        refine ⟨59892835354565341463969113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79857113806087121951958817 59892835354565341463969113)
        ·
          refine ⟨44919626515924006097976835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59892835354565341463969113 44919626515924006097976835)
          ·
            refine ⟨67379439773886009146965253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44919626515924006097976835 67379439773886009146965253)
            ·
              refine ⟨12633644957603626715055985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67379439773886009146965253 12633644957603626715055985)
              ·
                refine ⟨9475233718202720036291989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12633644957603626715055985 9475233718202720036291989)
                ·
                  refine ⟨444151580540752501701187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9475233718202720036291989 444151580540752501701187)
                  ·
                    rfl

theorem cell23_7784839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 6].length) (baseStart_7784839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784839 prefixEnd_7784839 := by exact prefixLift 7784839
  have htrace : WordTrace (prefixWord ++ tailWord_7784839) baseStart_7784839 baseEnd_7784839 := by
    simpa [prefixWord, tailWord_7784839, baseEnd_7784839] using wordTrace_append hprefix tailTrace_7784839
  have hstable : (prefixWord ++ tailWord_7784839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784839).length < 2 ^ (prefixWord ++ tailWord_7784839).sum := by decide
  have hdescent : baseEnd_7784839 < baseStart_7784839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784843 : List Nat := [1, 1, 1, 1, 4, 4, 4, 2, 1, 4]
def baseStart_7784843 : Nat := 118140960795 + 7784843 * 2 ^ 59
def prefixEnd_7784843 : Nat := 4983230072969 + 3 ^ 40 * 7784843 * 2
def baseEnd_7784843 : Nat := 1332455426263130166553555

theorem tailTrace_7784843 : CollatzResearch.WordTrace tailWord_7784843 prefixEnd_7784843 1332455426263130166553555 := by
  unfold tailWord_7784843
  simp only [CollatzResearch.WordTrace]
  refine ⟨283936550535850831178999183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189291033690567220785999455 283936550535850831178999183)
  ·
    refine ⟨425904825803776246768498775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283936550535850831178999183 425904825803776246768498775)
    ·
      refine ⟨638857238705664370152748163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425904825803776246768498775 638857238705664370152748163)
      ·
        refine ⟨958285858058496555229122245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638857238705664370152748163 958285858058496555229122245)
        ·
          refine ⟨179678598385968104105460421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 958285858058496555229122245 179678598385968104105460421)
          ·
            refine ⟨33689737197369019519773829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179678598385968104105460421 33689737197369019519773829)
            ·
              refine ⟨6316825724506691159957593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33689737197369019519773829 6316825724506691159957593)
              ·
                refine ⟨4737619293380018369968195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6316825724506691159957593 4737619293380018369968195)
                ·
                  refine ⟨7106428940070027554952293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4737619293380018369968195 7106428940070027554952293)
                  ·
                    refine ⟨1332455426263130166553555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7106428940070027554952293 1332455426263130166553555)
                    ·
                      rfl

theorem cell23_7784843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 1, 4].length) (baseStart_7784843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784843 prefixEnd_7784843 := by exact prefixLift 7784843
  have htrace : WordTrace (prefixWord ++ tailWord_7784843) baseStart_7784843 baseEnd_7784843 := by
    simpa [prefixWord, tailWord_7784843, baseEnd_7784843] using wordTrace_append hprefix tailTrace_7784843
  have hstable : (prefixWord ++ tailWord_7784843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784843).length < 2 ^ (prefixWord ++ tailWord_7784843).sum := by decide
  have hdescent : baseEnd_7784843 < baseStart_7784843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784869 : List Nat := [1, 3, 1, 2, 1, 1, 4, 4, 1, 5]
def baseStart_7784869 : Nat := 118140960795 + 7784869 * 2 ^ 59
def prefixEnd_7784869 : Nat := 4983230072969 + 3 ^ 40 * 7784869 * 2
def baseEnd_7784869 : Nat := 1332459876428802465978515

theorem tailTrace_7784869 : CollatzResearch.WordTrace tailWord_7784869 prefixEnd_7784869 1332459876428802465978515 := by
  unfold tailWord_7784869
  simp only [CollatzResearch.WordTrace]
  refine ⟨283937498833756637619445661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189291665889171091746297107 283937498833756637619445661)
  ·
    refine ⟨106476562062658739107292123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283937498833756637619445661 106476562062658739107292123)
    ·
      refine ⟨159714843093988108660938185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106476562062658739107292123 159714843093988108660938185)
      ·
        refine ⟨119786132320491081495703639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159714843093988108660938185 119786132320491081495703639)
        ·
          refine ⟨179679198480736622243555459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119786132320491081495703639 179679198480736622243555459)
          ·
            refine ⟨269518797721104933365333189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179679198480736622243555459 269518797721104933365333189)
            ·
              refine ⟨50534774572707175005999973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 269518797721104933365333189 50534774572707175005999973)
              ·
                refine ⟨9475270232382595313624995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50534774572707175005999973 9475270232382595313624995)
                ·
                  refine ⟨14212905348573892970437493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9475270232382595313624995 14212905348573892970437493)
                  ·
                    refine ⟨1332459876428802465978515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14212905348573892970437493 1332459876428802465978515)
                    ·
                      rfl

theorem cell23_7784869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_7784869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784869 prefixEnd_7784869 := by exact prefixLift 7784869
  have htrace : WordTrace (prefixWord ++ tailWord_7784869) baseStart_7784869 baseEnd_7784869 := by
    simpa [prefixWord, tailWord_7784869, baseEnd_7784869] using wordTrace_append hprefix tailTrace_7784869
  have hstable : (prefixWord ++ tailWord_7784869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784869).length < 2 ^ (prefixWord ++ tailWord_7784869).sum := by decide
  have hdescent : baseEnd_7784869 < baseStart_7784869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784900 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_7784900 : Nat := 118140960795 + 7784900 * 2 ^ 59
def prefixEnd_7784900 : Nat := 4983230072969 + 3 ^ 40 * 7784900 * 2
def baseEnd_7784900 : Nat := 3997395547186696776647903

theorem tailTrace_7784900 : CollatzResearch.WordTrace tailWord_7784900 prefixEnd_7784900 3997395547186696776647903 := by
  unfold tailWord_7784900
  simp only [CollatzResearch.WordTrace]
  refine ⟨141969314748322164956912077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189292419664429553275882769 141969314748322164956912077)
  ·
    refine ⟨53238493030620811858842029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141969314748322164956912077 53238493030620811858842029)
    ·
      refine ⟨19964434886482804447065761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53238493030620811858842029 19964434886482804447065761)
      ·
        refine ⟨14973326164862103335299321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19964434886482804447065761 14973326164862103335299321)
        ·
          refine ⟨11229994623646577501474491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14973326164862103335299321 11229994623646577501474491)
          ·
            refine ⟨16844991935469866252211737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11229994623646577501474491 16844991935469866252211737)
            ·
              refine ⟨12633743951602399689158803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16844991935469866252211737 12633743951602399689158803)
              ·
                refine ⟨18950615927403599533738205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12633743951602399689158803 18950615927403599533738205)
                ·
                  refine ⟨7106480972776349825151827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18950615927403599533738205 7106480972776349825151827)
                  ·
                    refine ⟨10659721459164524737727741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7106480972776349825151827 10659721459164524737727741)
                    ·
                      refine ⟨3997395547186696776647903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10659721459164524737727741 3997395547186696776647903)
                      ·
                        rfl

theorem cell23_7784900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_7784900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784900 prefixEnd_7784900 := by exact prefixLift 7784900
  have htrace : WordTrace (prefixWord ++ tailWord_7784900) baseStart_7784900 baseEnd_7784900 := by
    simpa [prefixWord, tailWord_7784900, baseEnd_7784900] using wordTrace_append hprefix tailTrace_7784900
  have hstable : (prefixWord ++ tailWord_7784900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784900).length < 2 ^ (prefixWord ++ tailWord_7784900).sum := by decide
  have hdescent : baseEnd_7784900 < baseStart_7784900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784916 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_7784916 : Nat := 118140960795 + 7784916 * 2 ^ 59
def prefixEnd_7784916 : Nat := 4983230072969 + 3 ^ 40 * 7784916 * 2
def baseEnd_7784916 : Nat := 1332467920959056238015943

theorem tailTrace_7784916 : CollatzResearch.WordTrace tailWord_7784916 prefixEnd_7784916 1332467920959056238015943 := by
  unfold tailWord_7784916
  simp only [CollatzResearch.WordTrace]
  refine ⟨141969606532293182323203301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189292808709724243097604401 141969606532293182323203301)
  ·
    refine ⟨26619301224804971685600619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141969606532293182323203301 26619301224804971685600619)
    ·
      refine ⟨39928951837207457528400929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26619301224804971685600619 39928951837207457528400929)
      ·
        refine ⟨29946713877905593146300697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39928951837207457528400929 29946713877905593146300697)
        ·
          refine ⟨22460035408429194859725523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29946713877905593146300697 22460035408429194859725523)
          ·
            refine ⟨33690053112643792289588285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22460035408429194859725523 33690053112643792289588285)
            ·
              refine ⟨12633769917241422108595607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33690053112643792289588285 12633769917241422108595607)
              ·
                refine ⟨18950654875862133162893411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12633769917241422108595607 18950654875862133162893411)
                ·
                  refine ⟨28425982313793199744340117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18950654875862133162893411 28425982313793199744340117)
                  ·
                    refine ⟨1332467920959056238015943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28425982313793199744340117 1332467920959056238015943)
                    ·
                      rfl

theorem cell23_7784916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_7784916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784916 prefixEnd_7784916 := by exact prefixLift 7784916
  have htrace : WordTrace (prefixWord ++ tailWord_7784916) baseStart_7784916 baseEnd_7784916 := by
    simpa [prefixWord, tailWord_7784916, baseEnd_7784916] using wordTrace_append hprefix tailTrace_7784916
  have hstable : (prefixWord ++ tailWord_7784916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784916).length < 2 ^ (prefixWord ++ tailWord_7784916).sum := by decide
  have hdescent : baseEnd_7784916 < baseStart_7784916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784939 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 3]
def baseStart_7784939 : Nat := 118140960795 + 7784939 * 2 ^ 59
def prefixEnd_7784939 : Nat := 4983230072969 + 3 ^ 40 * 7784939 * 2
def baseEnd_7784939 : Nat := 3997415572932222124060223

theorem tailTrace_7784939 : CollatzResearch.WordTrace tailWord_7784939 prefixEnd_7784939 3997415572932222124060223 := by
  unfold tailWord_7784939
  simp only [CollatzResearch.WordTrace]
  refine ⟨283940051943503039574493871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189293367962335359716329247 283940051943503039574493871)
  ·
    refine ⟨425910077915254559361740807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283940051943503039574493871 425910077915254559361740807)
    ·
      refine ⟨638865116872881839042611211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425910077915254559361740807 638865116872881839042611211)
      ·
        refine ⟨958297675309322758563916817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638865116872881839042611211 958297675309322758563916817)
        ·
          refine ⟨718723256481992068922937613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 958297675309322758563916817 718723256481992068922937613)
          ·
            refine ⟨269521221180747025846101605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 718723256481992068922937613 269521221180747025846101605)
            ·
              refine ⟨50535228971390067346144051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 269521221180747025846101605 50535228971390067346144051)
              ·
                refine ⟨75802843457085101019216077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50535228971390067346144051 75802843457085101019216077)
                ·
                  refine ⟨28426066296406912882206029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75802843457085101019216077 28426066296406912882206029)
                  ·
                    refine ⟨10659774861152592330827261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28426066296406912882206029 10659774861152592330827261)
                    ·
                      refine ⟨3997415572932222124060223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10659774861152592330827261 3997415572932222124060223)
                      ·
                        rfl

theorem cell23_7784939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 3].length) (baseStart_7784939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784939 prefixEnd_7784939 := by exact prefixLift 7784939
  have htrace : WordTrace (prefixWord ++ tailWord_7784939) baseStart_7784939 baseEnd_7784939 := by
    simpa [prefixWord, tailWord_7784939, baseEnd_7784939] using wordTrace_append hprefix tailTrace_7784939
  have hstable : (prefixWord ++ tailWord_7784939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784939).length < 2 ^ (prefixWord ++ tailWord_7784939).sum := by decide
  have hdescent : baseEnd_7784939 < baseStart_7784939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784946 : List Nat := [3, 2, 1, 4, 2, 2, 9]
def baseStart_7784946 : Nat := 118140960795 + 7784946 * 2 ^ 59
def prefixEnd_7784946 : Nat := 4983230072969 + 3 ^ 40 * 7784946 * 2
def baseEnd_7784946 : Nat := 49350853917244488847811

theorem tailTrace_7784946 : CollatzResearch.WordTrace tailWord_7784946 prefixEnd_7784946 49350853917244488847811 := by
  unfold tailWord_7784946
  simp only [CollatzResearch.WordTrace]
  refine ⟨70985076813619419942499673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189293538169651786513332461 70985076813619419942499673)
  ·
    refine ⟨53238807610214564956874755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70985076813619419942499673 53238807610214564956874755)
    ·
      refine ⟨79858211415321847435312133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53238807610214564956874755 79858211415321847435312133)
      ·
        refine ⟨14973414640372846394121025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79858211415321847435312133 14973414640372846394121025)
        ·
          refine ⟨11230060980279634795590769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14973414640372846394121025 11230060980279634795590769)
          ·
            refine ⟨8422545735209726096693077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11230060980279634795590769 8422545735209726096693077)
            ·
              refine ⟨49350853917244488847811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8422545735209726096693077 49350853917244488847811)
              ·
                rfl

theorem cell23_7784946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 9].length) (baseStart_7784946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784946 prefixEnd_7784946 := by exact prefixLift 7784946
  have htrace : WordTrace (prefixWord ++ tailWord_7784946) baseStart_7784946 baseEnd_7784946 := by
    simpa [prefixWord, tailWord_7784946, baseEnd_7784946] using wordTrace_append hprefix tailTrace_7784946
  have hstable : (prefixWord ++ tailWord_7784946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784946).length < 2 ^ (prefixWord ++ tailWord_7784946).sum := by decide
  have hdescent : baseEnd_7784946 < baseStart_7784946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784957 : List Nat := [1, 4, 1, 1, 1, 3, 5, 2, 1, 2, 2]
def baseStart_7784957 : Nat := 118140960795 + 7784957 * 2 ^ 59
def prefixEnd_7784957 : Nat := 4983230072969 + 3 ^ 40 * 7784957 * 2
def baseEnd_7784957 : Nat := 3997424815584003053635141

theorem tailTrace_7784957 : CollatzResearch.WordTrace tailWord_7784957 prefixEnd_7784957 3997424815584003053635141 := by
  unfold tailWord_7784957
  simp only [CollatzResearch.WordTrace]
  refine ⟨283940708457437828648649125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189293805638291885765766083 283940708457437828648649125)
  ·
    refine ⟨53238882835769592871621711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283940708457437828648649125 53238882835769592871621711)
    ·
      refine ⟨79858324253654389307432567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53238882835769592871621711 79858324253654389307432567)
      ·
        refine ⟨119787486380481583961148851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79858324253654389307432567 119787486380481583961148851)
        ·
          refine ⟨179681229570722375941723277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119787486380481583961148851 179681229570722375941723277)
          ·
            refine ⟨67380461089020890978146229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179681229570722375941723277 67380461089020890978146229)
            ·
              refine ⟨6316918227095708529201209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67380461089020890978146229 6316918227095708529201209)
              ·
                refine ⟨4737688670321781396900907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6316918227095708529201209 4737688670321781396900907)
                ·
                  refine ⟨7106533005482672095351361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4737688670321781396900907 7106533005482672095351361)
                  ·
                    refine ⟨5329899754112004071513521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7106533005482672095351361 5329899754112004071513521)
                    ·
                      refine ⟨3997424815584003053635141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5329899754112004071513521 3997424815584003053635141)
                      ·
                        rfl

theorem cell23_7784957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_7784957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784957 prefixEnd_7784957 := by exact prefixLift 7784957
  have htrace : WordTrace (prefixWord ++ tailWord_7784957) baseStart_7784957 baseEnd_7784957 := by
    simpa [prefixWord, tailWord_7784957, baseEnd_7784957] using wordTrace_append hprefix tailTrace_7784957
  have hstable : (prefixWord ++ tailWord_7784957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784957).length < 2 ^ (prefixWord ++ tailWord_7784957).sum := by decide
  have hdescent : baseEnd_7784957 < baseStart_7784957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784967 : List Nat := [1, 1, 4, 3, 4, 1, 2, 1, 2, 4]
def baseStart_7784967 : Nat := 118140960795 + 7784967 * 2 ^ 59
def prefixEnd_7784967 : Nat := 4983230072969 + 3 ^ 40 * 7784967 * 2
def baseEnd_7784967 : Nat := 1332476650130182671503365

theorem tailTrace_7784967 : CollatzResearch.WordTrace tailWord_7784967 prefixEnd_7784967 1332476650130182671503365 := by
  unfold tailWord_7784967
  simp only [CollatzResearch.WordTrace]
  refine ⟨283941073187401600356513155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189294048791601066904342103 283941073187401600356513155)
  ·
    refine ⟨425911609781102400534769733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283941073187401600356513155 425911609781102400534769733)
    ·
      refine ⟨79858426833956700100269325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 425911609781102400534769733 79858426833956700100269325)
      ·
        refine ⟨29946910062733762537600997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79858426833956700100269325 29946910062733762537600997)
        ·
          refine ⟨5615045636762580475800187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29946910062733762537600997 5615045636762580475800187)
          ·
            refine ⟨8422568455143870713700281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5615045636762580475800187 8422568455143870713700281)
            ·
              refine ⟨6316926341357903035275211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8422568455143870713700281 6316926341357903035275211)
              ·
                refine ⟨9475389512036854552912817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6316926341357903035275211 9475389512036854552912817)
                ·
                  refine ⟨7106542134027640914684613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9475389512036854552912817 7106542134027640914684613)
                  ·
                    refine ⟨1332476650130182671503365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7106542134027640914684613 1332476650130182671503365)
                    ·
                      rfl

theorem cell23_7784967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_7784967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7784967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7784967 prefixEnd_7784967 := by exact prefixLift 7784967
  have htrace : WordTrace (prefixWord ++ tailWord_7784967) baseStart_7784967 baseEnd_7784967 := by
    simpa [prefixWord, tailWord_7784967, baseEnd_7784967] using wordTrace_append hprefix tailTrace_7784967
  have hstable : (prefixWord ++ tailWord_7784967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784967).length < 2 ^ (prefixWord ++ tailWord_7784967).sum := by decide
  have hdescent : baseEnd_7784967 < baseStart_7784967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785064 : List Nat := [2, 1, 4, 3, 2, 2, 1, 2, 2, 2, 2]
def baseStart_7785064 : Nat := 118140960795 + 7785064 * 2 ^ 59
def prefixEnd_7785064 : Nat := 4983230072969 + 3 ^ 40 * 7785064 * 2
def baseEnd_7785064 : Nat := 3997479758014034134997149

theorem tailTrace_7785064 : CollatzResearch.WordTrace tailWord_7785064 prefixEnd_7785064 3997479758014034134997149 := by
  unfold tailWord_7785064
  simp only [CollatzResearch.WordTrace]
  refine ⟨141972305534025092961397123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189296407378700123948529497 141972305534025092961397123)
  ·
    refine ⟨212958458301037639442095685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141972305534025092961397123 212958458301037639442095685)
    ·
      refine ⟨39929710931444557395392941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212958458301037639442095685 39929710931444557395392941)
      ·
        refine ⟨14973641599291709023272353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39929710931444557395392941 14973641599291709023272353)
        ·
          refine ⟨11230231199468781767454265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14973641599291709023272353 11230231199468781767454265)
          ·
            refine ⟨8422673399601586325590699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11230231199468781767454265 8422673399601586325590699)
            ·
              refine ⟨12634010099402379488386049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8422673399601586325590699 12634010099402379488386049)
              ·
                refine ⟨9475507574551784616289537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12634010099402379488386049 9475507574551784616289537)
                ·
                  refine ⟨7106630680913838462217153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9475507574551784616289537 7106630680913838462217153)
                  ·
                    refine ⟨5329973010685378846662865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7106630680913838462217153 5329973010685378846662865)
                    ·
                      refine ⟨3997479758014034134997149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5329973010685378846662865 3997479758014034134997149)
                      ·
                        rfl

theorem cell23_7785064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_7785064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785064 prefixEnd_7785064 := by exact prefixLift 7785064
  have htrace : WordTrace (prefixWord ++ tailWord_7785064) baseStart_7785064 baseEnd_7785064 := by
    simpa [prefixWord, tailWord_7785064, baseEnd_7785064] using wordTrace_append hprefix tailTrace_7785064
  have hstable : (prefixWord ++ tailWord_7785064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785064).length < 2 ^ (prefixWord ++ tailWord_7785064).sum := by decide
  have hdescent : baseEnd_7785064 < baseStart_7785064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785066 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 4, 5]
def baseStart_7785066 : Nat := 118140960795 + 7785066 * 2 ^ 59
def prefixEnd_7785066 : Nat := 4983230072969 + 3 ^ 40 * 7785066 * 2
def baseEnd_7785066 : Nat := 1332493594991781042390713

theorem tailTrace_7785066 : CollatzResearch.WordTrace tailWord_7785066 prefixEnd_7785066 1332493594991781042390713 := by
  unfold tailWord_7785066
  simp only [CollatzResearch.WordTrace]
  refine ⟨70986171003510735066091763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189296456009361960176244701 70986171003510735066091763)
  ·
    refine ⟨106479256505266102599137645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70986171003510735066091763 106479256505266102599137645)
    ·
      refine ⟨39929721189474788474676617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106479256505266102599137645 39929721189474788474676617)
      ·
        refine ⟨29947290892106091356007463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39929721189474788474676617 29947290892106091356007463)
        ·
          refine ⟨44920936338159137034011195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29947290892106091356007463 44920936338159137034011195)
          ·
            refine ⟨67381404507238705551016793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44920936338159137034011195 67381404507238705551016793)
            ·
              refine ⟨50536053380429029163262595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67381404507238705551016793 50536053380429029163262595)
              ·
                refine ⟨75804080070643543744893893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50536053380429029163262595 75804080070643543744893893)
                ·
                  refine ⟨14213265013245664452167605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75804080070643543744893893 14213265013245664452167605)
                  ·
                    refine ⟨1332493594991781042390713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14213265013245664452167605 1332493594991781042390713)
                    ·
                      rfl

theorem cell23_7785066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_7785066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785066 prefixEnd_7785066 := by exact prefixLift 7785066
  have htrace : WordTrace (prefixWord ++ tailWord_7785066) baseStart_7785066 baseEnd_7785066 := by
    simpa [prefixWord, tailWord_7785066, baseEnd_7785066] using wordTrace_append hprefix tailTrace_7785066
  have hstable : (prefixWord ++ tailWord_7785066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785066).length < 2 ^ (prefixWord ++ tailWord_7785066).sum := by decide
  have hdescent : baseEnd_7785066 < baseStart_7785066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785099 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 6]
def baseStart_7785099 : Nat := 118140960795 + 7785099 * 2 ^ 59
def prefixEnd_7785099 : Nat := 4983230072969 + 3 ^ 40 * 7785099 * 2
def baseEnd_7785099 : Nat := 3997497729836941498059487

theorem tailTrace_7785099 : CollatzResearch.WordTrace tailWord_7785099 prefixEnd_7785099 3997497729836941498059487 := by
  unfold tailWord_7785099
  simp only [CollatzResearch.WordTrace]
  refine ⟨283945887622923386900318351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189297258415282257933545567 283945887622923386900318351)
  ·
    refine ⟨425918831434385080350477527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283945887622923386900318351 425918831434385080350477527)
    ·
      refine ⟨638878247151577620525716291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425918831434385080350477527 638878247151577620525716291)
      ·
        refine ⟨958317370727366430788574437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638878247151577620525716291 958317370727366430788574437)
        ·
          refine ⟨179684507011381205772857707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 958317370727366430788574437 179684507011381205772857707)
          ·
            refine ⟨269526760517071808659286561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179684507011381205772857707 269526760517071808659286561)
            ·
              refine ⟨202145070387803856494464921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269526760517071808659286561 202145070387803856494464921)
              ·
                refine ⟨151608802790852892370848691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202145070387803856494464921 151608802790852892370848691)
                ·
                  refine ⟨227413204186279338556273037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151608802790852892370848691 227413204186279338556273037)
                  ·
                    refine ⟨85279951569854751958602389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 227413204186279338556273037 85279951569854751958602389)
                    ·
                      refine ⟨3997497729836941498059487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85279951569854751958602389 3997497729836941498059487)
                      ·
                        rfl

theorem cell23_7785099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 6].length) (baseStart_7785099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785099 prefixEnd_7785099 := by exact prefixLift 7785099
  have htrace : WordTrace (prefixWord ++ tailWord_7785099) baseStart_7785099 baseEnd_7785099 := by
    simpa [prefixWord, tailWord_7785099, baseEnd_7785099] using wordTrace_append hprefix tailTrace_7785099
  have hstable : (prefixWord ++ tailWord_7785099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785099).length < 2 ^ (prefixWord ++ tailWord_7785099).sum := by decide
  have hdescent : baseEnd_7785099 < baseStart_7785099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785143 : List Nat := [1, 1, 3, 1, 6, 1, 1, 3, 6]
def baseStart_7785143 : Nat := 118140960795 + 7785143 * 2 ^ 59
def prefixEnd_7785143 : Nat := 4983230072969 + 3 ^ 40 * 7785143 * 2
def baseEnd_7785143 : Nat := 444168924776193258434365

theorem tailTrace_7785143 : CollatzResearch.WordTrace tailWord_7785143 prefixEnd_7785143 444168924776193258434365 := by
  unfold tailWord_7785143
  simp only [CollatzResearch.WordTrace]
  refine ⟨283947492434763982414920083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189298328289842654943280055 283947492434763982414920083)
  ·
    refine ⟨425921238652145973622380125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283947492434763982414920083 425921238652145973622380125)
    ·
      refine ⟨159720464494554740108392547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425921238652145973622380125 159720464494554740108392547)
      ·
        refine ⟨239580696741832110162588821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159720464494554740108392547 239580696741832110162588821)
        ·
          refine ⟨11230345159773380163871351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 239580696741832110162588821 11230345159773380163871351)
          ·
            refine ⟨16845517739660070245807027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11230345159773380163871351 16845517739660070245807027)
            ·
              refine ⟨25268276609490105368710541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16845517739660070245807027 25268276609490105368710541)
              ·
                refine ⟨9475603728558789513266453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25268276609490105368710541 9475603728558789513266453)
                ·
                  refine ⟨444168924776193258434365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9475603728558789513266453 444168924776193258434365)
                  ·
                    rfl

theorem cell23_7785143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 6].length) (baseStart_7785143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785143 prefixEnd_7785143 := by exact prefixLift 7785143
  have htrace : WordTrace (prefixWord ++ tailWord_7785143) baseStart_7785143 baseEnd_7785143 := by
    simpa [prefixWord, tailWord_7785143, baseEnd_7785143] using wordTrace_append hprefix tailTrace_7785143
  have hstable : (prefixWord ++ tailWord_7785143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785143).length < 2 ^ (prefixWord ++ tailWord_7785143).sum := by decide
  have hdescent : baseEnd_7785143 < baseStart_7785143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785196 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 5]
def baseStart_7785196 : Nat := 118140960795 + 7785196 * 2 ^ 59
def prefixEnd_7785196 : Nat := 4983230072969 + 3 ^ 40 * 7785196 * 2
def baseEnd_7785196 : Nat := 3997547537460427618546541

theorem tailTrace_7785196 : CollatzResearch.WordTrace tailWord_7785196 prefixEnd_7785196 3997547537460427618546541 := by
  unfold tailWord_7785196
  simp only [CollatzResearch.WordTrace]
  refine ⟨141974712751785986233299721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189299617002381314977732961 141974712751785986233299721)
  ·
    refine ⟨106481034563839489674974791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141974712751785986233299721 106481034563839489674974791)
    ·
      refine ⟨159721551845759234512462187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106481034563839489674974791 159721551845759234512462187)
      ·
        refine ⟨239582327768638851768693281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159721551845759234512462187 239582327768638851768693281)
        ·
          refine ⟨179686745826479138826519961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239582327768638851768693281 179686745826479138826519961)
          ·
            refine ⟨134765059369859354119889971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179686745826479138826519961 134765059369859354119889971)
            ·
              refine ⟨202147589054789031179834957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134765059369859354119889971 202147589054789031179834957)
              ·
                refine ⟨75805345895545886692438109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202147589054789031179834957 75805345895545886692438109)
                ·
                  refine ⟨28427004710829707509664291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75805345895545886692438109 28427004710829707509664291)
                  ·
                    refine ⟨42640507066244561264496437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28427004710829707509664291 42640507066244561264496437)
                    ·
                      refine ⟨3997547537460427618546541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42640507066244561264496437 3997547537460427618546541)
                      ·
                        rfl

theorem cell23_7785196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_7785196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785196 prefixEnd_7785196 := by exact prefixLift 7785196
  have htrace : WordTrace (prefixWord ++ tailWord_7785196) baseStart_7785196 baseEnd_7785196 := by
    simpa [prefixWord, tailWord_7785196, baseEnd_7785196] using wordTrace_append hprefix tailTrace_7785196
  have hstable : (prefixWord ++ tailWord_7785196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785196).length < 2 ^ (prefixWord ++ tailWord_7785196).sum := by decide
  have hdescent : baseEnd_7785196 < baseStart_7785196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785210 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2]
def baseStart_7785210 : Nat := 118140960795 + 7785210 * 2 ^ 59
def prefixEnd_7785210 : Nat := 4983230072969 + 3 ^ 40 * 7785210 * 2
def baseEnd_7785210 : Nat := 3997554726189590563771477

theorem tailTrace_7785210 : CollatzResearch.WordTrace tailWord_7785210 prefixEnd_7785210 3997554726189590563771477 := by
  unfold tailWord_7785210
  simp only [CollatzResearch.WordTrace]
  refine ⟨70987484031380313214402271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189299957417014168571739389 70987484031380313214402271)
  ·
    refine ⟨106481226047070469821603407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70987484031380313214402271 106481226047070469821603407)
    ·
      refine ⟨159721839070605704732405111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106481226047070469821603407 159721839070605704732405111)
      ·
        refine ⟨239582758605908557098607667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159721839070605704732405111 239582758605908557098607667)
        ·
          refine ⟨359374137908862835647911501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239582758605908557098607667 359374137908862835647911501)
          ·
            refine ⟨134765301715823563367966813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359374137908862835647911501 134765301715823563367966813)
            ·
              refine ⟨50536988143433836262987555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134765301715823563367966813 50536988143433836262987555)
              ·
                refine ⟨75805482215150754394481333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50536988143433836262987555 75805482215150754394481333)
                ·
                  refine ⟨7106763957670383224482625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75805482215150754394481333 7106763957670383224482625)
                  ·
                    refine ⟨5330072968252787418361969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7106763957670383224482625 5330072968252787418361969)
                    ·
                      refine ⟨3997554726189590563771477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5330072968252787418361969 3997554726189590563771477)
                      ·
                        rfl

theorem cell23_7785210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2].length) (baseStart_7785210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785210 prefixEnd_7785210 := by exact prefixLift 7785210
  have htrace : WordTrace (prefixWord ++ tailWord_7785210) baseStart_7785210 baseEnd_7785210 := by
    simpa [prefixWord, tailWord_7785210, baseEnd_7785210] using wordTrace_append hprefix tailTrace_7785210
  have hstable : (prefixWord ++ tailWord_7785210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785210).length < 2 ^ (prefixWord ++ tailWord_7785210).sum := by decide
  have hdescent : baseEnd_7785210 < baseStart_7785210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785213 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 3, 2, 3]
def baseStart_7785213 : Nat := 118140960795 + 7785213 * 2 ^ 59
def prefixEnd_7785213 : Nat := 4983230072969 + 3 ^ 40 * 7785213 * 2
def baseEnd_7785213 : Nat := 3997556266631554052033963

theorem tailTrace_7785213 : CollatzResearch.WordTrace tailWord_7785213 prefixEnd_7785213 3997556266631554052033963 := by
  unfold tailWord_7785213
  simp only [CollatzResearch.WordTrace]
  refine ⟨283950045544510384369968293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189300030363006922913312195 283950045544510384369968293)
  ·
    refine ⟨53240633539595697069369055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283950045544510384369968293 53240633539595697069369055)
    ·
      refine ⟨79860950309393545604053583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53240633539595697069369055 79860950309393545604053583)
      ·
        refine ⟨119791425464090318406080375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79860950309393545604053583 119791425464090318406080375)
        ·
          refine ⟨179687138196135477609120563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119791425464090318406080375 179687138196135477609120563)
          ·
            refine ⟨269530707294203216413680845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179687138196135477609120563 269530707294203216413680845)
            ·
              refine ⟨101074015235326206155130317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269530707294203216413680845 101074015235326206155130317)
              ·
                refine ⟨37902755713247327308173869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101074015235326206155130317 37902755713247327308173869)
                ·
                  refine ⟨14213533392467747740565201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37902755713247327308173869 14213533392467747740565201)
                  ·
                    refine ⟨10660150044350810805423901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14213533392467747740565201 10660150044350810805423901)
                    ·
                      refine ⟨3997556266631554052033963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10660150044350810805423901 3997556266631554052033963)
                      ·
                        rfl

theorem cell23_7785213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_7785213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785213 prefixEnd_7785213 := by exact prefixLift 7785213
  have htrace : WordTrace (prefixWord ++ tailWord_7785213) baseStart_7785213 baseEnd_7785213 := by
    simpa [prefixWord, tailWord_7785213, baseEnd_7785213] using wordTrace_append hprefix tailTrace_7785213
  have hstable : (prefixWord ++ tailWord_7785213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785213).length < 2 ^ (prefixWord ++ tailWord_7785213).sum := by decide
  have hdescent : baseEnd_7785213 < baseStart_7785213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785214 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_7785214 : Nat := 118140960795 + 7785214 * 2 ^ 59
def prefixEnd_7785214 : Nat := 4983230072969 + 3 ^ 40 * 7785214 * 2
def baseEnd_7785214 : Nat := 3997556780112208548121459

theorem tailTrace_7785214 : CollatzResearch.WordTrace tailWord_7785214 prefixEnd_7785214 3997556780112208548121459 := by
  unfold tailWord_7785214
  simp only [CollatzResearch.WordTrace]
  refine ⟨35493760252188345192594337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189300054678337841027169797 35493760252188345192594337)
  ·
    refine ⟨26620320189141258894445753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35493760252188345192594337 26620320189141258894445753)
    ·
      refine ⟨19965240141855944170834315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26620320189141258894445753 19965240141855944170834315)
      ·
        refine ⟨29947860212783916256251473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19965240141855944170834315 29947860212783916256251473)
        ·
          refine ⟨22460895159587937192188605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29947860212783916256251473 22460895159587937192188605)
          ·
            refine ⟨8422835684845476447070727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22460895159587937192188605 8422835684845476447070727)
            ·
              refine ⟨12634253527268214670606091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8422835684845476447070727 12634253527268214670606091)
              ·
                refine ⟨18951380290902322005909137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12634253527268214670606091 18951380290902322005909137)
                ·
                  refine ⟨14213535218176741504431853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18951380290902322005909137 14213535218176741504431853)
                  ·
                    refine ⟨5330075706816278064161945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14213535218176741504431853 5330075706816278064161945)
                    ·
                      refine ⟨3997556780112208548121459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5330075706816278064161945 3997556780112208548121459)
                      ·
                        rfl

theorem cell23_7785214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_7785214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785214 prefixEnd_7785214 := by exact prefixLift 7785214
  have htrace : WordTrace (prefixWord ++ tailWord_7785214) baseStart_7785214 baseEnd_7785214 := by
    simpa [prefixWord, tailWord_7785214, baseEnd_7785214] using wordTrace_append hprefix tailTrace_7785214
  have hstable : (prefixWord ++ tailWord_7785214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785214).length < 2 ^ (prefixWord ++ tailWord_7785214).sum := by decide
  have hdescent : baseEnd_7785214 < baseStart_7785214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785244 : List Nat := [2, 2, 3, 1, 1, 3, 2, 4, 1, 2, 2]
def baseStart_7785244 : Nat := 118140960795 + 7785244 * 2 ^ 59
def prefixEnd_7785244 : Nat := 4983230072969 + 3 ^ 40 * 7785244 * 2
def baseEnd_7785244 : Nat := 3997572184531843430746321

theorem tailTrace_7785244 : CollatzResearch.WordTrace tailWord_7785244 prefixEnd_7785244 3997572184531843430746321 := by
  unfold tailWord_7785244
  simp only [CollatzResearch.WordTrace]
  refine ⟨141975588103699038332173393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189300784138265384442897857 141975588103699038332173393)
  ·
    refine ⟨106481691077774278749130045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141975588103699038332173393 106481691077774278749130045)
    ·
      refine ⟨39930634154165354530923767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106481691077774278749130045 39930634154165354530923767)
      ·
        refine ⟨59895951231248031796385651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39930634154165354530923767 59895951231248031796385651)
        ·
          refine ⟨89843926846872047694578477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59895951231248031796385651 89843926846872047694578477)
          ·
            refine ⟨33691472567577017885466929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89843926846872047694578477 33691472567577017885466929)
            ·
              refine ⟨25268604425682763414100197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33691472567577017885466929 25268604425682763414100197)
              ·
                refine ⟨4737863329815518140143787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25268604425682763414100197 4737863329815518140143787)
                ·
                  refine ⟨7106794994723277210215681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4737863329815518140143787 7106794994723277210215681)
                  ·
                    refine ⟨5330096246042457907661761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7106794994723277210215681 5330096246042457907661761)
                    ·
                      refine ⟨3997572184531843430746321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5330096246042457907661761 3997572184531843430746321)
                      ·
                        rfl

theorem cell23_7785244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_7785244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785244 prefixEnd_7785244 := by exact prefixLift 7785244
  have htrace : WordTrace (prefixWord ++ tailWord_7785244) baseStart_7785244 baseEnd_7785244 := by
    simpa [prefixWord, tailWord_7785244, baseEnd_7785244] using wordTrace_append hprefix tailTrace_7785244
  have hstable : (prefixWord ++ tailWord_7785244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785244).length < 2 ^ (prefixWord ++ tailWord_7785244).sum := by decide
  have hdescent : baseEnd_7785244 < baseStart_7785244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785278 : List Nat := [4, 2, 1, 2, 3, 2, 1, 3, 1, 2, 2]
def baseStart_7785278 : Nat := 118140960795 + 7785278 * 2 ^ 59
def prefixEnd_7785278 : Nat := 4983230072969 + 3 ^ 40 * 7785278 * 2
def baseEnd_7785278 : Nat := 3997589642874096297721165

theorem tailTrace_7785278 : CollatzResearch.WordTrace tailWord_7785278 prefixEnd_7785278 3997589642874096297721165 := by
  unfold tailWord_7785278
  simp only [CollatzResearch.WordTrace]
  refine ⟨35494052036159362558885561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189301610859516600314056325 35494052036159362558885561)
  ·
    refine ⟨26620539027119521919164171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35494052036159362558885561 26620539027119521919164171)
    ·
      refine ⟨39930808540679282878746257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26620539027119521919164171 39930808540679282878746257)
      ·
        refine ⟨29948106405509462159059693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39930808540679282878746257 29948106405509462159059693)
        ·
          refine ⟨11230539902066048309647385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29948106405509462159059693 11230539902066048309647385)
          ·
            refine ⟨8422904926549536232235539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11230539902066048309647385 8422904926549536232235539)
            ·
              refine ⟨12634357389824304348353309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8422904926549536232235539 12634357389824304348353309)
              ·
                refine ⟨4737884021184114130632491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12634357389824304348353309 4737884021184114130632491)
                ·
                  refine ⟨7106826031776171195948737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4737884021184114130632491 7106826031776171195948737)
                  ·
                    refine ⟨5330119523832128396961553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7106826031776171195948737 5330119523832128396961553)
                    ·
                      refine ⟨3997589642874096297721165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5330119523832128396961553 3997589642874096297721165)
                      ·
                        rfl

theorem cell23_7785278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_7785278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785278 prefixEnd_7785278 := by exact prefixLift 7785278
  have htrace : WordTrace (prefixWord ++ tailWord_7785278) baseStart_7785278 baseEnd_7785278 := by
    simpa [prefixWord, tailWord_7785278, baseEnd_7785278] using wordTrace_append hprefix tailTrace_7785278
  have hstable : (prefixWord ++ tailWord_7785278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785278).length < 2 ^ (prefixWord ++ tailWord_7785278).sum := by decide
  have hdescent : baseEnd_7785278 < baseStart_7785278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785334 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2]
def baseStart_7785334 : Nat := 118140960795 + 7785334 * 2 ^ 59
def prefixEnd_7785334 : Nat := 4983230072969 + 3 ^ 40 * 7785334 * 2
def baseEnd_7785334 : Nat := 3997618397790748078620907

theorem tailTrace_7785334 : CollatzResearch.WordTrace tailWord_7785334 prefixEnd_7785334 3997618397790748078620907 := by
  unfold tailWord_7785334
  simp only [CollatzResearch.WordTrace]
  refine ⟨17747153673567001377195191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189302972518048014690082037 17747153673567001377195191)
  ·
    refine ⟨26620730510350502065792787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17747153673567001377195191 26620730510350502065792787)
    ·
      refine ⟨39931095765525753098689181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26620730510350502065792787 39931095765525753098689181)
      ·
        refine ⟨14974160912072157412008443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39931095765525753098689181 14974160912072157412008443)
        ·
          refine ⟨22461241368108236118012665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14974160912072157412008443 22461241368108236118012665)
          ·
            refine ⟨16845931026081177088509499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22461241368108236118012665 16845931026081177088509499)
            ·
              refine ⟨25268896539121765632764249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16845931026081177088509499 25268896539121765632764249)
              ·
                refine ⟨18951672404341324224573187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25268896539121765632764249 18951672404341324224573187)
                ·
                  refine ⟨28427508606511986336859781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18951672404341324224573187 28427508606511986336859781)
                  ·
                    refine ⟨5330157863720997438161209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28427508606511986336859781 5330157863720997438161209)
                    ·
                      refine ⟨3997618397790748078620907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5330157863720997438161209 3997618397790748078620907)
                      ·
                        rfl

theorem cell23_7785334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_7785334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785334 prefixEnd_7785334 := by exact prefixLift 7785334
  have htrace : WordTrace (prefixWord ++ tailWord_7785334) baseStart_7785334 baseEnd_7785334 := by
    simpa [prefixWord, tailWord_7785334, baseEnd_7785334] using wordTrace_append hprefix tailTrace_7785334
  have hstable : (prefixWord ++ tailWord_7785334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785334).length < 2 ^ (prefixWord ++ tailWord_7785334).sum := by decide
  have hdescent : baseEnd_7785334 < baseStart_7785334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785461 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_7785461 : Nat := 118140960795 + 7785461 * 2 ^ 59
def prefixEnd_7785461 : Nat := 4983230072969 + 3 ^ 40 * 7785461 * 2
def baseEnd_7785461 : Nat := 3997683609833869081732823

theorem tailTrace_7785461 : CollatzResearch.WordTrace tailWord_7785461 prefixEnd_7785461 3997683609833869081732823 := by
  unfold tailWord_7785461
  simp only [CollatzResearch.WordTrace]
  refine ⟨283959090847611922724996237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189306060565074615149997491 283959090847611922724996237)
  ·
    refine ⟨106484659067854471021873589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283959090847611922724996237 106484659067854471021873589)
    ·
      refine ⟨9982936787611356658300649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106484659067854471021873589 9982936787611356658300649)
      ·
        refine ⟨7487202590708517493725487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9982936787611356658300649 7487202590708517493725487)
        ·
          refine ⟨11230803886062776240588231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7487202590708517493725487 11230803886062776240588231)
          ·
            refine ⟨16846205829094164360882347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11230803886062776240588231 16846205829094164360882347)
            ·
              refine ⟨25269308743641246541323521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16846205829094164360882347 25269308743641246541323521)
              ·
                refine ⟨18951981557730934905992641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25269308743641246541323521 18951981557730934905992641)
                ·
                  refine ⟨14213986168298201179494481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18951981557730934905992641 14213986168298201179494481)
                  ·
                    refine ⟨10660489626223650884620861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14213986168298201179494481 10660489626223650884620861)
                    ·
                      refine ⟨3997683609833869081732823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10660489626223650884620861 3997683609833869081732823)
                      ·
                        rfl

theorem cell23_7785461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_7785461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785461 prefixEnd_7785461 := by exact prefixLift 7785461
  have htrace : WordTrace (prefixWord ++ tailWord_7785461) baseStart_7785461 baseEnd_7785461 := by
    simpa [prefixWord, tailWord_7785461, baseEnd_7785461] using wordTrace_append hprefix tailTrace_7785461
  have hstable : (prefixWord ++ tailWord_7785461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785461).length < 2 ^ (prefixWord ++ tailWord_7785461).sum := by decide
  have hdescent : baseEnd_7785461 < baseStart_7785461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785497 : List Nat := [1, 2, 1, 2, 1, 1, 7, 2, 1, 1, 4]
def baseStart_7785497 : Nat := 118140960795 + 7785497 * 2 ^ 59
def prefixEnd_7785497 : Nat := 4983230072969 + 3 ^ 40 * 7785497 * 2
def baseEnd_7785497 : Nat := 3997702095137430940882657

theorem tailTrace_7785497 : CollatzResearch.WordTrace tailWord_7785497 prefixEnd_7785497 3997702095137430940882657 := by
  unfold tailWord_7785497
  simp only [CollatzResearch.WordTrace]
  refine ⟨283960403875481500873306745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189306935916987667248871163 283960403875481500873306745)
  ·
    refine ⟨212970302906611125654980059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283960403875481500873306745 212970302906611125654980059)
    ·
      refine ⟨319455454359916688482470089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212970302906611125654980059 319455454359916688482470089)
      ·
        refine ⟨239591590769937516361852567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319455454359916688482470089 239591590769937516361852567)
        ·
          refine ⟨359387386154906274542778851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239591590769937516361852567 359387386154906274542778851)
          ·
            refine ⟨539081079232359411814168277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359387386154906274542778851 539081079232359411814168277)
            ·
              refine ⟨12634712794508423714394569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 539081079232359411814168277 12634712794508423714394569)
              ·
                refine ⟨9476034595881317785795927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12634712794508423714394569 9476034595881317785795927)
                ·
                  refine ⟨14214051893821976678693891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9476034595881317785795927 14214051893821976678693891)
                  ·
                    refine ⟨21321077840732965018040837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14214051893821976678693891 21321077840732965018040837)
                    ·
                      refine ⟨3997702095137430940882657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21321077840732965018040837 3997702095137430940882657)
                      ·
                        rfl

theorem cell23_7785497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_7785497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785497 prefixEnd_7785497 := by exact prefixLift 7785497
  have htrace : WordTrace (prefixWord ++ tailWord_7785497) baseStart_7785497 baseEnd_7785497 := by
    simpa [prefixWord, tailWord_7785497, baseEnd_7785497] using wordTrace_append hprefix tailTrace_7785497
  have hstable : (prefixWord ++ tailWord_7785497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785497).length < 2 ^ (prefixWord ++ tailWord_7785497).sum := by decide
  have hdescent : baseEnd_7785497 < baseStart_7785497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785501 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 2, 3, 2]
def baseStart_7785501 : Nat := 118140960795 + 7785501 * 2 ^ 59
def prefixEnd_7785501 : Nat := 4983230072969 + 3 ^ 40 * 7785501 * 2
def baseEnd_7785501 : Nat := 3997704149060048925232639

theorem tailTrace_7785501 : CollatzResearch.WordTrace tailWord_7785501 prefixEnd_7785501 3997704149060048925232639 := by
  unfold tailWord_7785501
  simp only [CollatzResearch.WordTrace]
  refine ⟨283960549767467009556452357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189307033178311339704301571 283960549767467009556452357)
  ·
    refine ⟨53242603081400064291834817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283960549767467009556452357 53242603081400064291834817)
    ·
      refine ⟨39931952311050048218876113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53242603081400064291834817 39931952311050048218876113)
      ·
        refine ⟨29948964233287536164157085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39931952311050048218876113 29948964233287536164157085)
        ·
          refine ⟨11230861587482826061558907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29948964233287536164157085 11230861587482826061558907)
          ·
            refine ⟨16846292381224239092338361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11230861587482826061558907 16846292381224239092338361)
            ·
              refine ⟨12634719285918179319253771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16846292381224239092338361 12634719285918179319253771)
              ·
                refine ⟨18952078928877268978880657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12634719285918179319253771 18952078928877268978880657)
                ·
                  refine ⟨14214059196657951734160493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18952078928877268978880657 14214059196657951734160493)
                  ·
                    refine ⟨5330272198746731900310185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14214059196657951734160493 5330272198746731900310185)
                    ·
                      refine ⟨3997704149060048925232639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5330272198746731900310185 3997704149060048925232639)
                      ·
                        rfl

theorem cell23_7785501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_7785501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785501 prefixEnd_7785501 := by exact prefixLift 7785501
  have htrace : WordTrace (prefixWord ++ tailWord_7785501) baseStart_7785501 baseEnd_7785501 := by
    simpa [prefixWord, tailWord_7785501, baseEnd_7785501] using wordTrace_append hprefix tailTrace_7785501
  have hstable : (prefixWord ++ tailWord_7785501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785501).length < 2 ^ (prefixWord ++ tailWord_7785501).sum := by decide
  have hdescent : baseEnd_7785501 < baseStart_7785501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785511 : List Nat := [1, 1, 7, 1, 1, 2, 3, 1, 1, 5]
def baseStart_7785511 : Nat := 118140960795 + 7785511 * 2 ^ 59
def prefixEnd_7785511 : Nat := 4983230072969 + 3 ^ 40 * 7785511 * 2
def baseEnd_7785511 : Nat := 1332569761288864628702531

theorem tailTrace_7785511 : CollatzResearch.WordTrace tailWord_7785511 prefixEnd_7785511 1332569761288864628702531 := by
  unfold tailWord_7785511
  simp only [CollatzResearch.WordTrace]
  refine ⟨283960914497430781264316387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189307276331620520842877591 283960914497430781264316387)
  ·
    refine ⟨425941371746146171896474581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283960914497430781264316387 425941371746146171896474581)
    ·
      refine ⟨9983000900300300903823623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 425941371746146171896474581 9983000900300300903823623)
      ·
        refine ⟨14974501350450451355735435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9983000900300300903823623 14974501350450451355735435)
        ·
          refine ⟨22461752025675677033603153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14974501350450451355735435 22461752025675677033603153)
          ·
            refine ⟨16846314019256757775202365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22461752025675677033603153 16846314019256757775202365)
            ·
              refine ⟨6317367757221284165700887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16846314019256757775202365 6317367757221284165700887)
              ·
                refine ⟨9476051635831926248551331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6317367757221284165700887 9476051635831926248551331)
                ·
                  refine ⟨14214077453747889372826997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9476051635831926248551331 14214077453747889372826997)
                  ·
                    refine ⟨1332569761288864628702531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14214077453747889372826997 1332569761288864628702531)
                    ·
                      rfl

theorem cell23_7785511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_7785511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785511 prefixEnd_7785511 := by exact prefixLift 7785511
  have htrace : WordTrace (prefixWord ++ tailWord_7785511) baseStart_7785511 baseEnd_7785511 := by
    simpa [prefixWord, tailWord_7785511, baseEnd_7785511] using wordTrace_append hprefix tailTrace_7785511
  have hstable : (prefixWord ++ tailWord_7785511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785511).length < 2 ^ (prefixWord ++ tailWord_7785511).sum := by decide
  have hdescent : baseEnd_7785511 < baseStart_7785511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785534 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_7785534 : Nat := 118140960795 + 7785534 * 2 ^ 59
def prefixEnd_7785534 : Nat := 4983230072969 + 3 ^ 40 * 7785534 * 2
def baseEnd_7785534 : Nat := 3997721093921647296119987

theorem tailTrace_7785534 : CollatzResearch.WordTrace tailWord_7785534 prefixEnd_7785534 3997721093921647296119987 := by
  unfold tailWord_7785534
  simp only [CollatzResearch.WordTrace]
  refine ⟨35495219172043432024050457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189307835584231637461602437 35495219172043432024050457)
  ·
    refine ⟨26621414379032574018037843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35495219172043432024050457 26621414379032574018037843)
    ·
      refine ⟨39932121568548861027056765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26621414379032574018037843 39932121568548861027056765)
      ·
        refine ⟨14974545588205822885146287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39932121568548861027056765 14974545588205822885146287)
        ·
          refine ⟨22461818382308734327719431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14974545588205822885146287 22461818382308734327719431)
          ·
            refine ⟨33692727573463101491579147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22461818382308734327719431 33692727573463101491579147)
            ·
              refine ⟨50539091360194652237368721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33692727573463101491579147 50539091360194652237368721)
              ·
                refine ⟨37904318520145989178026541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50539091360194652237368721 37904318520145989178026541)
                ·
                  refine ⟨14214119445054745941759953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37904318520145989178026541 14214119445054745941759953)
                  ·
                    refine ⟨10660589583791059456319965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14214119445054745941759953 10660589583791059456319965)
                    ·
                      refine ⟨3997721093921647296119987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10660589583791059456319965 3997721093921647296119987)
                      ·
                        rfl

theorem cell23_7785534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_7785534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785534 prefixEnd_7785534 := by exact prefixLift 7785534
  have htrace : WordTrace (prefixWord ++ tailWord_7785534) baseStart_7785534 baseEnd_7785534 := by
    simpa [prefixWord, tailWord_7785534, baseEnd_7785534] using wordTrace_append hprefix tailTrace_7785534
  have hstable : (prefixWord ++ tailWord_7785534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785534).length < 2 ^ (prefixWord ++ tailWord_7785534).sum := by decide
  have hdescent : baseEnd_7785534 < baseStart_7785534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785550 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 2, 7]
def baseStart_7785550 : Nat := 118140960795 + 7785550 * 2 ^ 59
def prefixEnd_7785550 : Nat := 4983230072969 + 3 ^ 40 * 7785550 * 2
def baseEnd_7785550 : Nat := 1332576436537373077839971

theorem tailTrace_7785550 : CollatzResearch.WordTrace tailWord_7785550 prefixEnd_7785550 1332576436537373077839971 := by
  unfold tailWord_7785550
  simp only [CollatzResearch.WordTrace]
  refine ⟨35495292118036186365623263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189308224629526327283324069 35495292118036186365623263)
  ·
    refine ⟨53242938177054279548434895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35495292118036186365623263 53242938177054279548434895)
    ·
      refine ⟨79864407265581419322652343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53242938177054279548434895 79864407265581419322652343)
      ·
        refine ⟨119796610898372128983978515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79864407265581419322652343 119796610898372128983978515)
        ·
          refine ⟨179694916347558193475967773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119796610898372128983978515 179694916347558193475967773)
          ·
            refine ⟨67385593630334322553487915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179694916347558193475967773 67385593630334322553487915)
            ·
              refine ⟨101078390445501483830231873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67385593630334322553487915 101078390445501483830231873)
              ·
                refine ⟨75808792834126112872673905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101078390445501483830231873 75808792834126112872673905)
                ·
                  refine ⟨56856594625594584654505429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75808792834126112872673905 56856594625594584654505429)
                  ·
                    refine ⟨1332576436537373077839971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56856594625594584654505429 1332576436537373077839971)
                    ·
                      rfl

theorem cell23_7785550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_7785550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785550 prefixEnd_7785550 := by exact prefixLift 7785550
  have htrace : WordTrace (prefixWord ++ tailWord_7785550) baseStart_7785550 baseEnd_7785550 := by
    simpa [prefixWord, tailWord_7785550, baseEnd_7785550] using wordTrace_append hprefix tailTrace_7785550
  have hstable : (prefixWord ++ tailWord_7785550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785550).length < 2 ^ (prefixWord ++ tailWord_7785550).sum := by decide
  have hdescent : baseEnd_7785550 < baseStart_7785550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785560 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 2, 2, 5]
def baseStart_7785560 : Nat := 118140960795 + 7785560 * 2 ^ 59
def prefixEnd_7785560 : Nat := 4983230072969 + 3 ^ 40 * 7785560 * 2
def baseEnd_7785560 : Nat := 3997734444418664194394867

theorem tailTrace_7785560 : CollatzResearch.WordTrace tailWord_7785560 prefixEnd_7785560 3997734444418664194394867 := by
  unfold tailWord_7785560
  simp only [CollatzResearch.WordTrace]
  refine ⟨141981350837126631316425067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189308467782835508421900089 141981350837126631316425067)
  ·
    refine ⟨212972026255689946974637601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141981350837126631316425067 212972026255689946974637601)
    ·
      refine ⟨159729019691767460230978201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212972026255689946974637601 159729019691767460230978201)
      ·
        refine ⟨119796764768825595173233651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159729019691767460230978201 119796764768825595173233651)
        ·
          refine ⟨179695147153238392759850477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119796764768825595173233651 179695147153238392759850477)
          ·
            refine ⟨67385680182464397284943929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179695147153238392759850477 67385680182464397284943929)
            ·
              refine ⟨50539260136848297963707947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67385680182464397284943929 50539260136848297963707947)
              ·
                refine ⟨75808890205272446945561921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50539260136848297963707947 75808890205272446945561921)
                ·
                  refine ⟨56856667653954335209171441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75808890205272446945561921 56856667653954335209171441)
                  ·
                    refine ⟨42642500740465751406878581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56856667653954335209171441 42642500740465751406878581)
                    ·
                      refine ⟨3997734444418664194394867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42642500740465751406878581 3997734444418664194394867)
                      ·
                        rfl

theorem cell23_7785560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_7785560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785560 prefixEnd_7785560 := by exact prefixLift 7785560
  have htrace : WordTrace (prefixWord ++ tailWord_7785560) baseStart_7785560 baseEnd_7785560 := by
    simpa [prefixWord, tailWord_7785560, baseEnd_7785560] using wordTrace_append hprefix tailTrace_7785560
  have hstable : (prefixWord ++ tailWord_7785560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785560).length < 2 ^ (prefixWord ++ tailWord_7785560).sum := by decide
  have hdescent : baseEnd_7785560 < baseStart_7785560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785564 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_7785564 : Nat := 118140960795 + 7785564 * 2 ^ 59
def prefixEnd_7785564 : Nat := 4983230072969 + 3 ^ 40 * 7785564 * 2
def baseEnd_7785564 : Nat := 3997736498341282178744849

theorem tailTrace_7785564 : CollatzResearch.WordTrace tailWord_7785564 prefixEnd_7785564 3997736498341282178744849 := by
  unfold tailWord_7785564
  simp only [CollatzResearch.WordTrace]
  refine ⟨141981423783119385657997873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189308565044159180877330497 141981423783119385657997873)
  ·
    refine ⟨106486067837339539243498405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141981423783119385657997873 106486067837339539243498405)
    ·
      refine ⟨19966137719501163608155951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106486067837339539243498405 19966137719501163608155951)
      ·
        refine ⟨29949206579251745412233927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19966137719501163608155951 29949206579251745412233927)
        ·
          refine ⟨44923809868877618118350891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29949206579251745412233927 44923809868877618118350891)
          ·
            refine ⟨67385714803316427177526337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44923809868877618118350891 67385714803316427177526337)
            ·
              refine ⟨50539286102487320383144753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67385714803316427177526337 50539286102487320383144753)
              ·
                refine ⟨37904464576865490287358565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50539286102487320383144753 37904464576865490287358565)
                ·
                  refine ⟨7107087108162279428879731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37904464576865490287358565 7107087108162279428879731)
                  ·
                    refine ⟨10660630662243419143319597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7107087108162279428879731 10660630662243419143319597)
                    ·
                      refine ⟨3997736498341282178744849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10660630662243419143319597 3997736498341282178744849)
                      ·
                        rfl

theorem cell23_7785564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_7785564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785564 prefixEnd_7785564 := by exact prefixLift 7785564
  have htrace : WordTrace (prefixWord ++ tailWord_7785564) baseStart_7785564 baseEnd_7785564 := by
    simpa [prefixWord, tailWord_7785564, baseEnd_7785564] using wordTrace_append hprefix tailTrace_7785564
  have hstable : (prefixWord ++ tailWord_7785564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785564).length < 2 ^ (prefixWord ++ tailWord_7785564).sum := by decide
  have hdescent : baseEnd_7785564 < baseStart_7785564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785565 : List Nat := [1, 4, 4, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_7785565 : Nat := 118140960795 + 7785565 * 2 ^ 59
def prefixEnd_7785565 : Nat := 4983230072969 + 3 ^ 40 * 7785565 * 2
def baseEnd_7785565 : Nat := 3997737011821936674832345

theorem tailTrace_7785565 : CollatzResearch.WordTrace tailWord_7785565 prefixEnd_7785565 3997737011821936674832345 := by
  unfold tailWord_7785565
  simp only [CollatzResearch.WordTrace]
  refine ⟨283962884039235148486782149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189308589359490098991188099 283962884039235148486782149)
  ·
    refine ⟨53243040757356590341271653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283962884039235148486782149 53243040757356590341271653)
    ·
      refine ⟨9983070142004360688988435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53243040757356590341271653 9983070142004360688988435)
      ·
        refine ⟨14974605213006541033482653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9983070142004360688988435 14974605213006541033482653)
        ·
          refine ⟨5615476954877452887555995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14974605213006541033482653 5615476954877452887555995)
          ·
            refine ⟨8423215432316179331333993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5615476954877452887555995 8423215432316179331333993)
            ·
              refine ⟨6317411574237134498500495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8423215432316179331333993 6317411574237134498500495)
              ·
                refine ⟨9476117361355701747750743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6317411574237134498500495 9476117361355701747750743)
                ·
                  refine ⟨14214176042033552621626115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9476117361355701747750743 14214176042033552621626115)
                  ·
                    refine ⟨21321264063050328932439173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14214176042033552621626115 21321264063050328932439173)
                    ·
                      refine ⟨3997737011821936674832345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21321264063050328932439173 3997737011821936674832345)
                      ·
                        rfl

theorem cell23_7785565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_7785565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785565 prefixEnd_7785565 := by exact prefixLift 7785565
  have htrace : WordTrace (prefixWord ++ tailWord_7785565) baseStart_7785565 baseEnd_7785565 := by
    simpa [prefixWord, tailWord_7785565, baseEnd_7785565] using wordTrace_append hprefix tailTrace_7785565
  have hstable : (prefixWord ++ tailWord_7785565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785565).length < 2 ^ (prefixWord ++ tailWord_7785565).sum := by decide
  have hdescent : baseEnd_7785565 < baseStart_7785565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785580 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 4, 6]
def baseStart_7785580 : Nat := 118140960795 + 7785580 * 2 ^ 59
def prefixEnd_7785580 : Nat := 4983230072969 + 3 ^ 40 * 7785580 * 2
def baseEnd_7785580 : Nat := 1332581571343918038714925

theorem tailTrace_7785580 : CollatzResearch.WordTrace tailWord_7785580 prefixEnd_7785580 1332581571343918038714925 := by
  unfold tailWord_7785580
  simp only [CollatzResearch.WordTrace]
  refine ⟨141981715567090403024289097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189308954089453870699052129 141981715567090403024289097)
  ·
    refine ⟨106486286675317802268216823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141981715567090403024289097 106486286675317802268216823)
    ·
      refine ⟨159729430012976703402325235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106486286675317802268216823 159729430012976703402325235)
      ·
        refine ⟨239594145019465055103487853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159729430012976703402325235 239594145019465055103487853)
        ·
          refine ⟨89847804382299395663807945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239594145019465055103487853 89847804382299395663807945)
          ·
            refine ⟨67385853286724546747855959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89847804382299395663807945 67385853286724546747855959)
            ·
              refine ⟨101078779930086820121783939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67385853286724546747855959 101078779930086820121783939)
              ·
                refine ⟨151618169895130230182675909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101078779930086820121783939 151618169895130230182675909)
                ·
                  refine ⟨28428406855336918159251733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151618169895130230182675909 28428406855336918159251733)
                  ·
                    refine ⟨1332581571343918038714925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28428406855336918159251733 1332581571343918038714925)
                    ·
                      rfl

theorem cell23_7785580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_7785580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785580 prefixEnd_7785580 := by exact prefixLift 7785580
  have htrace : WordTrace (prefixWord ++ tailWord_7785580) baseStart_7785580 baseEnd_7785580 := by
    simpa [prefixWord, tailWord_7785580, baseEnd_7785580] using wordTrace_append hprefix tailTrace_7785580
  have hstable : (prefixWord ++ tailWord_7785580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785580).length < 2 ^ (prefixWord ++ tailWord_7785580).sum := by decide
  have hdescent : baseEnd_7785580 < baseStart_7785580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785581 : List Nat := [1, 5, 1, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_7785581 : Nat := 118140960795 + 7785581 * 2 ^ 59
def prefixEnd_7785581 : Nat := 4983230072969 + 3 ^ 40 * 7785581 * 2
def baseEnd_7785581 : Nat := 3997745227512408612232271

theorem tailTrace_7785581 : CollatzResearch.WordTrace tailWord_7785581 prefixEnd_7785581 3997745227512408612232271 := by
  unfold tailWord_7785581
  simp only [CollatzResearch.WordTrace]
  refine ⟨283963467607177183219364597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189308978404784788812909731 283963467607177183219364597)
  ·
    refine ⟨26621575088172860926815431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 283963467607177183219364597 26621575088172860926815431)
    ·
      refine ⟨39932362632259291390223147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26621575088172860926815431 39932362632259291390223147)
      ·
        refine ⟨59898543948388937085334721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39932362632259291390223147 59898543948388937085334721)
        ·
          refine ⟨44923907961291702814001041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59898543948388937085334721 44923907961291702814001041)
          ·
            refine ⟨33692930970968777110500781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44923907961291702814001041 33692930970968777110500781)
            ·
              refine ⟨12634849114113291416437793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33692930970968777110500781 12634849114113291416437793)
              ·
                refine ⟨9476136835584968562328345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12634849114113291416437793 9476136835584968562328345)
                ·
                  refine ⟨7107102626688726421746259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9476136835584968562328345 7107102626688726421746259)
                  ·
                    refine ⟨10660653940033089632619389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7107102626688726421746259 10660653940033089632619389)
                    ·
                      refine ⟨3997745227512408612232271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10660653940033089632619389 3997745227512408612232271)
                      ·
                        rfl

theorem cell23_7785581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_7785581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785581 prefixEnd_7785581 := by exact prefixLift 7785581
  have htrace : WordTrace (prefixWord ++ tailWord_7785581) baseStart_7785581 baseEnd_7785581 := by
    simpa [prefixWord, tailWord_7785581, baseEnd_7785581] using wordTrace_append hprefix tailTrace_7785581
  have hstable : (prefixWord ++ tailWord_7785581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785581).length < 2 ^ (prefixWord ++ tailWord_7785581).sum := by decide
  have hdescent : baseEnd_7785581 < baseStart_7785581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785608 : List Nat := [2, 1, 3, 4, 2, 1, 2, 2, 1, 3, 2]
def baseStart_7785608 : Nat := 118140960795 + 7785608 * 2 ^ 59
def prefixEnd_7785608 : Nat := 4983230072969 + 3 ^ 40 * 7785608 * 2
def baseEnd_7785608 : Nat := 3997759091490080006594647

theorem tailTrace_7785608 : CollatzResearch.WordTrace tailWord_7785608 prefixEnd_7785608 3997759091490080006594647 := by
  unfold tailWord_7785608
  simp only [CollatzResearch.WordTrace]
  refine ⟨141982226189039683415298739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189309634918719577887064985 141982226189039683415298739)
  ·
    refine ⟨212973339283559525122948109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141982226189039683415298739 212973339283559525122948109)
    ·
      refine ⟨79865002231334821921105541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212973339283559525122948109 79865002231334821921105541)
      ·
        refine ⟨14974687918375279110207289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79865002231334821921105541 14974687918375279110207289)
        ·
          refine ⟨11231015938781459332655467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14974687918375279110207289 11231015938781459332655467)
          ·
            refine ⟨16846523908172188998983201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11231015938781459332655467 16846523908172188998983201)
            ·
              refine ⟨12634892931129141749237401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16846523908172188998983201 12634892931129141749237401)
              ·
                refine ⟨9476169698346856311928051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12634892931129141749237401 9476169698346856311928051)
                ·
                  refine ⟨14214254547520284467892077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9476169698346856311928051 14214254547520284467892077)
                  ·
                    refine ⟨5330345455320106675459529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14214254547520284467892077 5330345455320106675459529)
                    ·
                      refine ⟨3997759091490080006594647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5330345455320106675459529 3997759091490080006594647)
                      ·
                        rfl

theorem cell23_7785608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_7785608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785608 prefixEnd_7785608 := by exact prefixLift 7785608
  have htrace : WordTrace (prefixWord ++ tailWord_7785608) baseStart_7785608 baseEnd_7785608 := by
    simpa [prefixWord, tailWord_7785608, baseEnd_7785608] using wordTrace_append hprefix tailTrace_7785608
  have hstable : (prefixWord ++ tailWord_7785608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785608).length < 2 ^ (prefixWord ++ tailWord_7785608).sum := by decide
  have hdescent : baseEnd_7785608 < baseStart_7785608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785674 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 2, 5]
def baseStart_7785674 : Nat := 118140960795 + 7785674 * 2 ^ 59
def prefixEnd_7785674 : Nat := 4983230072969 + 3 ^ 40 * 7785674 * 2
def baseEnd_7785674 : Nat := 1332597660404425582789781

theorem tailTrace_7785674 : CollatzResearch.WordTrace tailWord_7785674 prefixEnd_7785674 1332597660404425582789781 := by
  unfold tailWord_7785674
  simp only [CollatzResearch.WordTrace]
  refine ⟨70991714898960065025625019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189311239730560173401666717 70991714898960065025625019)
  ·
    refine ⟨106487572348440097538437529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70991714898960065025625019 106487572348440097538437529)
    ·
      refine ⟨79865679261330073153828147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106487572348440097538437529 79865679261330073153828147)
      ·
        refine ⟨119798518891995109730742221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79865679261330073153828147 119798518891995109730742221)
        ·
          refine ⟨44924444584498166149028333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119798518891995109730742221 44924444584498166149028333)
          ·
            refine ⟨16846666719186812305885625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44924444584498166149028333 16846666719186812305885625)
            ·
              refine ⟨12635000039390109229414219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16846666719186812305885625 12635000039390109229414219)
              ·
                refine ⟨18952500059085163844121329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12635000039390109229414219 18952500059085163844121329)
                ·
                  refine ⟨14214375044313872883090997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18952500059085163844121329 14214375044313872883090997)
                  ·
                    refine ⟨1332597660404425582789781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14214375044313872883090997 1332597660404425582789781)
                    ·
                      rfl

theorem cell23_7785674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_7785674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785674 prefixEnd_7785674 := by exact prefixLift 7785674
  have htrace : WordTrace (prefixWord ++ tailWord_7785674) baseStart_7785674 baseEnd_7785674 := by
    simpa [prefixWord, tailWord_7785674, baseEnd_7785674] using wordTrace_append hprefix tailTrace_7785674
  have hstable : (prefixWord ++ tailWord_7785674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785674).length < 2 ^ (prefixWord ++ tailWord_7785674).sum := by decide
  have hdescent : baseEnd_7785674 < baseStart_7785674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785680 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 11]
def baseStart_7785680 : Nat := 118140960795 + 7785680 * 2 ^ 59
def prefixEnd_7785680 : Nat := 4983230072969 + 3 ^ 40 * 7785680 * 2
def baseEnd_7785680 : Nat := 3997796062097203724894315

theorem tailTrace_7785680 : CollatzResearch.WordTrace tailWord_7785680 prefixEnd_7785680 3997796062097203724894315 := by
  unfold tailWord_7785680
  simp only [CollatzResearch.WordTrace]
  refine ⟨141983539216909261563609247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189311385622545682084812329 141983539216909261563609247)
  ·
    refine ⟨212975308825363892345413871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141983539216909261563609247 212975308825363892345413871)
    ·
      refine ⟨319462963238045838518120807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212975308825363892345413871 319462963238045838518120807)
      ·
        refine ⟨479194444857068757777181211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319462963238045838518120807 479194444857068757777181211)
        ·
          refine ⟨718791667285603136665771817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479194444857068757777181211 718791667285603136665771817)
          ·
            refine ⟨539093750464202352499328863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718791667285603136665771817 539093750464202352499328863)
            ·
              refine ⟨808640625696303528748993295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539093750464202352499328863 808640625696303528748993295)
              ·
                refine ⟨1212960938544455293123489943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808640625696303528748993295 1212960938544455293123489943)
                ·
                  refine ⟨1819441407816682939685234915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1212960938544455293123489943 1819441407816682939685234915)
                  ·
                    refine ⟨2729162111725024409527852373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1819441407816682939685234915 2729162111725024409527852373)
                    ·
                      refine ⟨3997796062097203724894315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2729162111725024409527852373 3997796062097203724894315)
                      ·
                        rfl

theorem cell23_7785680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_7785680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785680 prefixEnd_7785680 := by exact prefixLift 7785680
  have htrace : WordTrace (prefixWord ++ tailWord_7785680) baseStart_7785680 baseEnd_7785680 := by
    simpa [prefixWord, tailWord_7785680, baseEnd_7785680] using wordTrace_append hprefix tailTrace_7785680
  have hstable : (prefixWord ++ tailWord_7785680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785680).length < 2 ^ (prefixWord ++ tailWord_7785680).sum := by decide
  have hdescent : baseEnd_7785680 < baseStart_7785680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785704 : List Nat := [2, 1, 4, 1, 2, 1, 2, 3, 3, 4]
def baseStart_7785704 : Nat := 118140960795 + 7785704 * 2 ^ 59
def prefixEnd_7785704 : Nat := 4983230072969 + 3 ^ 40 * 7785704 * 2
def baseEnd_7785704 : Nat := 1332602795210970543664735

theorem tailTrace_7785704 : CollatzResearch.WordTrace tailWord_7785704 prefixEnd_7785704 1332602795210970543664735 := by
  unfold tailWord_7785704
  simp only [CollatzResearch.WordTrace]
  refine ⟨141983976892865787613046083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189311969190487716817394777 141983976892865787613046083)
  ·
    refine ⟨212975965339298681419569125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141983976892865787613046083 212975965339298681419569125)
    ·
      refine ⟨39932993501118502766169211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212975965339298681419569125 39932993501118502766169211)
      ·
        refine ⟨59899490251677754149253817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39932993501118502766169211 59899490251677754149253817)
        ·
          refine ⟨44924617688758315611940363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59899490251677754149253817 44924617688758315611940363)
          ·
            refine ⟨67386926533137473417910545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44924617688758315611940363 67386926533137473417910545)
            ·
              refine ⟨50540194899853105063432909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67386926533137473417910545 50540194899853105063432909)
              ·
                refine ⟨18952573087444914398787341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50540194899853105063432909 18952573087444914398787341)
                ·
                  refine ⟨7107214907791842899545253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18952573087444914398787341 7107214907791842899545253)
                  ·
                    refine ⟨1332602795210970543664735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7107214907791842899545253 1332602795210970543664735)
                    ·
                      rfl

theorem cell23_7785704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_7785704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785704 prefixEnd_7785704 := by exact prefixLift 7785704
  have htrace : WordTrace (prefixWord ++ tailWord_7785704) baseStart_7785704 baseEnd_7785704 := by
    simpa [prefixWord, tailWord_7785704, baseEnd_7785704] using wordTrace_append hprefix tailTrace_7785704
  have hstable : (prefixWord ++ tailWord_7785704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785704).length < 2 ^ (prefixWord ++ tailWord_7785704).sum := by decide
  have hdescent : baseEnd_7785704 < baseStart_7785704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785711 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 2, 4, 2]
def baseStart_7785711 : Nat := 118140960795 + 7785711 * 2 ^ 59
def prefixEnd_7785711 : Nat := 4983230072969 + 3 ^ 40 * 7785711 * 2
def baseEnd_7785711 : Nat := 3997811979997493103606673

theorem tailTrace_7785711 : CollatzResearch.WordTrace tailWord_7785711 prefixEnd_7785711 3997811979997493103606673 := by
  unfold tailWord_7785711
  simp only [CollatzResearch.WordTrace]
  refine ⟨283968209096706215421596987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189312139397804143614397991 283968209096706215421596987)
  ·
    refine ⟨425952313645059323132395481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283968209096706215421596987 425952313645059323132395481)
    ·
      refine ⟨319464235233794492349296611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425952313645059323132395481 319464235233794492349296611)
      ·
        refine ⟨479196352850691738523944917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319464235233794492349296611 479196352850691738523944917)
        ·
          refine ⟨11231164519938087621654959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 479196352850691738523944917 11231164519938087621654959)
          ·
            refine ⟨16846746779907131432482439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11231164519938087621654959 16846746779907131432482439)
            ·
              refine ⟨25270120169860697148723659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16846746779907131432482439 25270120169860697148723659)
              ·
                refine ⟨37905180254791045723085489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25270120169860697148723659 37905180254791045723085489)
                ·
                  refine ⟨28428885191093284292314117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37905180254791045723085489 28428885191093284292314117)
                  ·
                    refine ⟨5330415973329990804808897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28428885191093284292314117 5330415973329990804808897)
                    ·
                      refine ⟨3997811979997493103606673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5330415973329990804808897 3997811979997493103606673)
                      ·
                        rfl

theorem cell23_7785711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 4, 2].length) (baseStart_7785711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785711 prefixEnd_7785711 := by exact prefixLift 7785711
  have htrace : WordTrace (prefixWord ++ tailWord_7785711) baseStart_7785711 baseEnd_7785711 := by
    simpa [prefixWord, tailWord_7785711, baseEnd_7785711] using wordTrace_append hprefix tailTrace_7785711
  have hstable : (prefixWord ++ tailWord_7785711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785711).length < 2 ^ (prefixWord ++ tailWord_7785711).sum := by decide
  have hdescent : baseEnd_7785711 < baseStart_7785711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785731 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 2, 2, 3]
def baseStart_7785731 : Nat := 118140960795 + 7785731 * 2 ^ 59
def prefixEnd_7785731 : Nat := 4983230072969 + 3 ^ 40 * 7785731 * 2
def baseEnd_7785731 : Nat := 3997822249610583025356581

theorem tailTrace_7785731 : CollatzResearch.WordTrace tailWord_7785731 prefixEnd_7785731 3997822249610583025356581 := by
  unfold tailWord_7785731
  simp only [CollatzResearch.WordTrace]
  refine ⟨283968938556633758837325047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189312625704422505891550031 283968938556633758837325047)
  ·
    refine ⟨425953407834950638255987571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283968938556633758837325047 425953407834950638255987571)
    ·
      refine ⟨638930111752425957383981357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425953407834950638255987571 638930111752425957383981357)
      ·
        refine ⟨239598791907159734018993009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 638930111752425957383981357 239598791907159734018993009)
        ·
          refine ⟨179699093930369800514244757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239598791907159734018993009 179699093930369800514244757)
          ·
            refine ⟨8423395027986084399105223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 179699093930369800514244757 8423395027986084399105223)
            ·
              refine ⟨12635092541979126598657835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8423395027986084399105223 12635092541979126598657835)
              ·
                refine ⟨18952638812968689897986753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12635092541979126598657835 18952638812968689897986753)
                ·
                  refine ⟨14214479109726517423490065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18952638812968689897986753 14214479109726517423490065)
                  ·
                    refine ⟨10660859332294888067617549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14214479109726517423490065 10660859332294888067617549)
                    ·
                      refine ⟨3997822249610583025356581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10660859332294888067617549 3997822249610583025356581)
                      ·
                        rfl

theorem cell23_7785731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_7785731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785731 prefixEnd_7785731 := by exact prefixLift 7785731
  have htrace : WordTrace (prefixWord ++ tailWord_7785731) baseStart_7785731 baseEnd_7785731 := by
    simpa [prefixWord, tailWord_7785731, baseEnd_7785731] using wordTrace_append hprefix tailTrace_7785731
  have hstable : (prefixWord ++ tailWord_7785731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785731).length < 2 ^ (prefixWord ++ tailWord_7785731).sum := by decide
  have hdescent : baseEnd_7785731 < baseStart_7785731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785781 : List Nat := [1, 3, 3, 1, 2, 3, 2, 2, 1, 5]
def baseStart_7785781 : Nat := 118140960795 + 7785781 * 2 ^ 59
def prefixEnd_7785781 : Nat := 4983230072969 + 3 ^ 40 * 7785781 * 2
def baseEnd_7785781 : Nat := 1332615974547769276577117

theorem tailTrace_7785781 : CollatzResearch.WordTrace tailWord_7785781 prefixEnd_7785781 1332615974547769276577117 := by
  unfold tailWord_7785781
  simp only [CollatzResearch.WordTrace]
  refine ⟨283970762206452617376645197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189313841470968411584430131 283970762206452617376645197)
  ·
    refine ⟨106489035827419731516241949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283970762206452617376645197 106489035827419731516241949)
    ·
      refine ⟨39933388435282399318590731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106489035827419731516241949 39933388435282399318590731)
      ·
        refine ⟨59900082652923598977886097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39933388435282399318590731 59900082652923598977886097)
        ·
          refine ⟨44925061989692699233414573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59900082652923598977886097 44925061989692699233414573)
          ·
            refine ⟨16846898246134762212530465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44925061989692699233414573 16846898246134762212530465)
            ·
              refine ⟨12635173684601071659397849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16846898246134762212530465 12635173684601071659397849)
              ·
                refine ⟨9476380263450803744548387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12635173684601071659397849 9476380263450803744548387)
                ·
                  refine ⟨14214570395176205616822581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9476380263450803744548387 14214570395176205616822581)
                  ·
                    refine ⟨1332615974547769276577117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14214570395176205616822581 1332615974547769276577117)
                    ·
                      rfl

theorem cell23_7785781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_7785781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785781 prefixEnd_7785781 := by exact prefixLift 7785781
  have htrace : WordTrace (prefixWord ++ tailWord_7785781) baseStart_7785781 baseEnd_7785781 := by
    simpa [prefixWord, tailWord_7785781, baseEnd_7785781] using wordTrace_append hprefix tailTrace_7785781
  have hstable : (prefixWord ++ tailWord_7785781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785781).length < 2 ^ (prefixWord ++ tailWord_7785781).sum := by decide
  have hdescent : baseEnd_7785781 < baseStart_7785781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785784 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 1, 8, 2]
def baseStart_7785784 : Nat := 118140960795 + 7785784 * 2 ^ 59
def prefixEnd_7785784 : Nat := 4983230072969 + 3 ^ 40 * 7785784 * 2
def baseEnd_7785784 : Nat := 3997849464085271317993837

theorem tailTrace_7785784 : CollatzResearch.WordTrace tailWord_7785784 prefixEnd_7785784 3997849464085271317993837 := by
  unfold tailWord_7785784
  simp only [CollatzResearch.WordTrace]
  refine ⟨141985435812720874444502203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189313914416961165926002937 141985435812720874444502203)
  ·
    refine ⟨212978153719081311666753305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141985435812720874444502203 212978153719081311666753305)
    ·
      refine ⟨159733615289310983750064979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212978153719081311666753305 159733615289310983750064979)
      ·
        refine ⟨239600422933966475625097469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159733615289310983750064979 239600422933966475625097469)
        ·
          refine ⟨89850158600237428359411551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239600422933966475625097469 89850158600237428359411551)
          ·
            refine ⟨134775237900356142539117327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89850158600237428359411551 134775237900356142539117327)
            ·
              refine ⟨202162856850534213808675991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134775237900356142539117327 202162856850534213808675991)
              ·
                refine ⟨303244285275801320713013987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202162856850534213808675991 303244285275801320713013987)
                ·
                  refine ⟨454866427913701981069520981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303244285275801320713013987 454866427913701981069520981)
                  ·
                    refine ⟨5330465952113695090658449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 454866427913701981069520981 5330465952113695090658449)
                    ·
                      refine ⟨3997849464085271317993837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5330465952113695090658449 3997849464085271317993837)
                      ·
                        rfl

theorem cell23_7785784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 8, 2].length) (baseStart_7785784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785784 prefixEnd_7785784 := by exact prefixLift 7785784
  have htrace : WordTrace (prefixWord ++ tailWord_7785784) baseStart_7785784 baseEnd_7785784 := by
    simpa [prefixWord, tailWord_7785784, baseEnd_7785784] using wordTrace_append hprefix tailTrace_7785784
  have hstable : (prefixWord ++ tailWord_7785784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785784).length < 2 ^ (prefixWord ++ tailWord_7785784).sum := by decide
  have hdescent : baseEnd_7785784 < baseStart_7785784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785801 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 5, 2, 2]
def baseStart_7785801 : Nat := 118140960795 + 7785801 * 2 ^ 59
def prefixEnd_7785801 : Nat := 4983230072969 + 3 ^ 40 * 7785801 * 2
def baseEnd_7785801 : Nat := 3997858193256397751481259

theorem tailTrace_7785801 : CollatzResearch.WordTrace tailWord_7785801 prefixEnd_7785801 3997858193256397751481259 := by
  unfold tailWord_7785801
  simp only [CollatzResearch.WordTrace]
  refine ⟨283971491666380160792373257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189314327777586773861582171 283971491666380160792373257)
  ·
    refine ⟨212978618749785120594279943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283971491666380160792373257 212978618749785120594279943)
    ·
      refine ⟨319467928124677680891419915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212978618749785120594279943 319467928124677680891419915)
      ·
        refine ⟨479201892187016521337129873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319467928124677680891419915 479201892187016521337129873)
        ·
          refine ⟨359401419140262391002847405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479201892187016521337129873 359401419140262391002847405)
          ·
            refine ⟨134775532177598396626067777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359401419140262391002847405 134775532177598396626067777)
            ·
              refine ⟨101081649133198797469550833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134775532177598396626067777 101081649133198797469550833)
              ·
                refine ⟨75811236849899098102163125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101081649133198797469550833 75811236849899098102163125)
                ·
                  refine ⟨7107303454678040447077793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75811236849899098102163125 7107303454678040447077793)
                  ·
                    refine ⟨5330477591008530335308345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7107303454678040447077793 5330477591008530335308345)
                    ·
                      refine ⟨3997858193256397751481259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5330477591008530335308345 3997858193256397751481259)
                      ·
                        rfl

theorem cell23_7785801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 2, 2].length) (baseStart_7785801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785801 prefixEnd_7785801 := by exact prefixLift 7785801
  have htrace : WordTrace (prefixWord ++ tailWord_7785801) baseStart_7785801 baseEnd_7785801 := by
    simpa [prefixWord, tailWord_7785801, baseEnd_7785801] using wordTrace_append hprefix tailTrace_7785801
  have hstable : (prefixWord ++ tailWord_7785801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785801).length < 2 ^ (prefixWord ++ tailWord_7785801).sum := by decide
  have hdescent : baseEnd_7785801 < baseStart_7785801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785804 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 1, 1, 5]
def baseStart_7785804 : Nat := 118140960795 + 7785804 * 2 ^ 59
def prefixEnd_7785804 : Nat := 4983230072969 + 3 ^ 40 * 7785804 * 2
def baseEnd_7785804 : Nat := 3997859733698361239743745

theorem tailTrace_7785804 : CollatzResearch.WordTrace tailWord_7785804 prefixEnd_7785804 3997859733698361239743745 := by
  unfold tailWord_7785804
  simp only [CollatzResearch.WordTrace]
  refine ⟨141985800542684646152366233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189314400723579528203154977 141985800542684646152366233)
  ·
    refine ⟨106489350407013484614274675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141985800542684646152366233 106489350407013484614274675)
    ·
      refine ⟨159734025610520226921412013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106489350407013484614274675 159734025610520226921412013)
      ·
        refine ⟨59900259603945085095529505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159734025610520226921412013 59900259603945085095529505)
        ·
          refine ⟨44925194702958813821647129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59900259603945085095529505 44925194702958813821647129)
          ·
            refine ⟨33693896027219110366235347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44925194702958813821647129 33693896027219110366235347)
            ·
              refine ⟨50540844040828665549353021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33693896027219110366235347 50540844040828665549353021)
              ·
                refine ⟨18952816515310749581007383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50540844040828665549353021 18952816515310749581007383)
                ·
                  refine ⟨28429224772966124371511075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18952816515310749581007383 28429224772966124371511075)
                  ·
                    refine ⟨42643837159449186557266613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28429224772966124371511075 42643837159449186557266613)
                    ·
                      refine ⟨3997859733698361239743745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42643837159449186557266613 3997859733698361239743745)
                      ·
                        rfl

theorem cell23_7785804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_7785804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785804 prefixEnd_7785804 := by exact prefixLift 7785804
  have htrace : WordTrace (prefixWord ++ tailWord_7785804) baseStart_7785804 baseEnd_7785804 := by
    simpa [prefixWord, tailWord_7785804, baseEnd_7785804] using wordTrace_append hprefix tailTrace_7785804
  have hstable : (prefixWord ++ tailWord_7785804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785804).length < 2 ^ (prefixWord ++ tailWord_7785804).sum := by decide
  have hdescent : baseEnd_7785804 < baseStart_7785804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785818 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2]
def baseStart_7785818 : Nat := 118140960795 + 7785818 * 2 ^ 59
def prefixEnd_7785818 : Nat := 4983230072969 + 3 ^ 40 * 7785818 * 2
def baseEnd_7785818 : Nat := 3997866922427524184968681

theorem tailTrace_7785818 : CollatzResearch.WordTrace tailWord_7785818 prefixEnd_7785818 3997866922427524184968681 := by
  unfold tailWord_7785818
  simp only [CollatzResearch.WordTrace]
  refine ⟨70993027926829643173935527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189314741138212381797161405 70993027926829643173935527)
  ·
    refine ⟨106489541890244464760903291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70993027926829643173935527 106489541890244464760903291)
    ·
      refine ⟨159734312835366697141354937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106489541890244464760903291 159734312835366697141354937)
      ·
        refine ⟨119800734626525022856016203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159734312835366697141354937 119800734626525022856016203)
        ·
          refine ⟨179701101939787534284024305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119800734626525022856016203 179701101939787534284024305)
          ·
            refine ⟨134775826454840650713018229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179701101939787534284024305 134775826454840650713018229)
            ·
              refine ⟨12635233730141311004345459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134775826454840650713018229 12635233730141311004345459)
              ·
                refine ⟨18952850595211966506518189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12635233730141311004345459 18952850595211966506518189)
                ·
                  refine ⟨7107318973204487439944321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18952850595211966506518189 7107318973204487439944321)
                  ·
                    refine ⟨5330489229903365579958241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7107318973204487439944321 5330489229903365579958241)
                    ·
                      refine ⟨3997866922427524184968681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5330489229903365579958241 3997866922427524184968681)
                      ·
                        rfl

theorem cell23_7785818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_7785818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785818 prefixEnd_7785818 := by exact prefixLift 7785818
  have htrace : WordTrace (prefixWord ++ tailWord_7785818) baseStart_7785818 baseEnd_7785818 := by
    simpa [prefixWord, tailWord_7785818, baseEnd_7785818] using wordTrace_append hprefix tailTrace_7785818
  have hstable : (prefixWord ++ tailWord_7785818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785818).length < 2 ^ (prefixWord ++ tailWord_7785818).sum := by decide
  have hdescent : baseEnd_7785818 < baseStart_7785818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785824 : List Nat := [2, 1, 1, 3, 4, 2, 2, 8]
def baseStart_7785824 : Nat := 118140960795 + 7785824 * 2 ^ 59
def prefixEnd_7785824 : Nat := 4983230072969 + 3 ^ 40 * 7785824 * 2
def baseEnd_7785824 : Nat := 148069259381905598573839

theorem tailTrace_7785824 : CollatzResearch.WordTrace tailWord_7785824 prefixEnd_7785824 148069259381905598573839 := by
  unfold tailWord_7785824
  simp only [CollatzResearch.WordTrace]
  refine ⟨141986165272648417860230263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189314887030197890480307017 141986165272648417860230263)
  ·
    refine ⟨212979247908972626790345395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141986165272648417860230263 212979247908972626790345395)
    ·
      refine ⟨319468871863458940185518093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212979247908972626790345395 319468871863458940185518093)
      ·
        refine ⟨119800826948797102569569285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319468871863458940185518093 119800826948797102569569285)
        ·
          refine ⟨22462655052899456731794241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119800826948797102569569285 22462655052899456731794241)
          ·
            refine ⟨16846991289674592548845681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22462655052899456731794241 16846991289674592548845681)
            ·
              refine ⟨12635243467255944411634261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16846991289674592548845681 12635243467255944411634261)
              ·
                refine ⟨148069259381905598573839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12635243467255944411634261 148069259381905598573839)
                ·
                  rfl

theorem cell23_7785824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 8].length) (baseStart_7785824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785824 prefixEnd_7785824 := by exact prefixLift 7785824
  have htrace : WordTrace (prefixWord ++ tailWord_7785824) baseStart_7785824 baseEnd_7785824 := by
    simpa [prefixWord, tailWord_7785824, baseEnd_7785824] using wordTrace_append hprefix tailTrace_7785824
  have hstable : (prefixWord ++ tailWord_7785824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785824).length < 2 ^ (prefixWord ++ tailWord_7785824).sum := by decide
  have hdescent : baseEnd_7785824 < baseStart_7785824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785828 : List Nat := [2, 3, 1, 1, 3, 2, 4, 1, 2, 4]
def baseStart_7785828 : Nat := 118140960795 + 7785828 * 2 ^ 59
def prefixEnd_7785828 : Nat := 4983230072969 + 3 ^ 40 * 7785828 * 2
def baseEnd_7785828 : Nat := 1332624019078023048614545

theorem tailTrace_7785828 : CollatzResearch.WordTrace tailWord_7785828 prefixEnd_7785828 1332624019078023048614545 := by
  unfold tailWord_7785828
  simp only [CollatzResearch.WordTrace]
  refine ⟨141986238218641172201803069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189314984291521562935737425 141986238218641172201803069)
  ·
    refine ⟨53244839331990439575676151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141986238218641172201803069 53244839331990439575676151)
    ·
      refine ⟨79867258997985659363514227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53244839331990439575676151 79867258997985659363514227)
      ·
        refine ⟨119800888496978489045271341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79867258997985659363514227 119800888496978489045271341)
        ·
          refine ⟨44925333186366933391976753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119800888496978489045271341 44925333186366933391976753)
          ·
            refine ⟨33693999889775200043982565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44925333186366933391976753 33693999889775200043982565)
            ·
              refine ⟨6317624979332850008246731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33693999889775200043982565 6317624979332850008246731)
              ·
                refine ⟨9476437468999275012370097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6317624979332850008246731 9476437468999275012370097)
                ·
                  refine ⟨7107328101749456259277573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9476437468999275012370097 7107328101749456259277573)
                  ·
                    refine ⟨1332624019078023048614545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7107328101749456259277573 1332624019078023048614545)
                    ·
                      rfl

theorem cell23_7785828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_7785828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785828 prefixEnd_7785828 := by exact prefixLift 7785828
  have htrace : WordTrace (prefixWord ++ tailWord_7785828) baseStart_7785828 baseEnd_7785828 := by
    simpa [prefixWord, tailWord_7785828, baseEnd_7785828] using wordTrace_append hprefix tailTrace_7785828
  have hstable : (prefixWord ++ tailWord_7785828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785828).length < 2 ^ (prefixWord ++ tailWord_7785828).sum := by decide
  have hdescent : baseEnd_7785828 < baseStart_7785828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785868 : List Nat := [2, 2, 1, 2, 1, 3, 4, 2, 2, 1, 3]
def baseStart_7785868 : Nat := 118140960795 + 7785868 * 2 ^ 59
def prefixEnd_7785868 : Nat := 4983230072969 + 3 ^ 40 * 7785868 * 2
def baseEnd_7785868 : Nat := 3997892596460248989343451

theorem tailTrace_7785868 : CollatzResearch.WordTrace tailWord_7785868 prefixEnd_7785868 3997892596460248989343451 := by
  unfold tailWord_7785868
  simp only [CollatzResearch.WordTrace]
  refine ⟨141986967678568715617531129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189315956904758287490041505 141986967678568715617531129)
  ·
    refine ⟨106490225758926536713148347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141986967678568715617531129 106490225758926536713148347)
    ·
      refine ⟨159735338638389805069722521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106490225758926536713148347 159735338638389805069722521)
      ·
        refine ⟨119801503978792353802291891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159735338638389805069722521 119801503978792353802291891)
        ·
          refine ⟨179702255968188530703437837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119801503978792353802291891 179702255968188530703437837)
          ·
            refine ⟨67388345988070699013789189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179702255968188530703437837 67388345988070699013789189)
            ·
              refine ⟨12635314872763256065085473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67388345988070699013789189 12635314872763256065085473)
              ·
                refine ⟨9476486154572442048814105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12635314872763256065085473 9476486154572442048814105)
                ·
                  refine ⟨7107364615929331536610579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9476486154572442048814105 7107364615929331536610579)
                  ·
                    refine ⟨10661046923893997304915869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7107364615929331536610579 10661046923893997304915869)
                    ·
                      refine ⟨3997892596460248989343451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10661046923893997304915869 3997892596460248989343451)
                      ·
                        rfl

theorem cell23_7785868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_7785868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785868 prefixEnd_7785868 := by exact prefixLift 7785868
  have htrace : WordTrace (prefixWord ++ tailWord_7785868) baseStart_7785868 baseEnd_7785868 := by
    simpa [prefixWord, tailWord_7785868, baseEnd_7785868] using wordTrace_append hprefix tailTrace_7785868
  have hstable : (prefixWord ++ tailWord_7785868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785868).length < 2 ^ (prefixWord ++ tailWord_7785868).sum := by decide
  have hdescent : baseEnd_7785868 < baseStart_7785868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785931 : List Nat := [1, 1, 1, 1, 3, 3, 4, 4, 5]
def baseStart_7785931 : Nat := 118140960795 + 7785931 * 2 ^ 59
def prefixEnd_7785931 : Nat := 4983230072969 + 3 ^ 40 * 7785931 * 2
def baseEnd_7785931 : Nat := 444213882860164693650629

theorem tailTrace_7785931 : CollatzResearch.WordTrace tailWord_7785931 prefixEnd_7785931 444213882860164693650629 := by
  unfold tailWord_7785931
  simp only [CollatzResearch.WordTrace]
  refine ⟨283976233155909192994605647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189317488770606128663070431 283976233155909192994605647)
  ·
    refine ⟨425964349733863789491908471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283976233155909192994605647 425964349733863789491908471)
    ·
      refine ⟨638946524600795684237862707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425964349733863789491908471 638946524600795684237862707)
      ·
        refine ⟨958419786901193526356794061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638946524600795684237862707 958419786901193526356794061)
        ·
          refine ⟨359407420087947572383797773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 958419786901193526356794061 359407420087947572383797773)
          ·
            refine ⟨134777782532980339643924165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359407420087947572383797773 134777782532980339643924165)
            ·
              refine ⟨25270834224933813683235781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134777782532980339643924165 25270834224933813683235781)
              ·
                refine ⟨4738281417175090065606709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25270834224933813683235781 4738281417175090065606709)
                ·
                  refine ⟨444213882860164693650629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4738281417175090065606709 444213882860164693650629)
                  ·
                    rfl

theorem cell23_7785931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 5].length) (baseStart_7785931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785931 prefixEnd_7785931 := by exact prefixLift 7785931
  have htrace : WordTrace (prefixWord ++ tailWord_7785931) baseStart_7785931 baseEnd_7785931 := by
    simpa [prefixWord, tailWord_7785931, baseEnd_7785931] using wordTrace_append hprefix tailTrace_7785931
  have hstable : (prefixWord ++ tailWord_7785931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785931).length < 2 ^ (prefixWord ++ tailWord_7785931).sum := by decide
  have hdescent : baseEnd_7785931 < baseStart_7785931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785941 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 2, 3, 3]
def baseStart_7785941 : Nat := 118140960795 + 7785941 * 2 ^ 59
def prefixEnd_7785941 : Nat := 4983230072969 + 3 ^ 40 * 7785941 * 2
def baseEnd_7785941 : Nat := 3997930080548027203730615

theorem tailTrace_7785941 : CollatzResearch.WordTrace tailWord_7785941 prefixEnd_7785941 3997930080548027203730615 := by
  unfold tailWord_7785941
  simp only [CollatzResearch.WordTrace]
  refine ⟨283976597885872964702469677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189317731923915309801646451 283976597885872964702469677)
  ·
    refine ⟨106491224207202361763426129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283976597885872964702469677 106491224207202361763426129)
    ·
      refine ⟨79868418155401771322569597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106491224207202361763426129 79868418155401771322569597)
      ·
        refine ⟨29950656808275664245963599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79868418155401771322569597 29950656808275664245963599)
        ·
          refine ⟨44925985212413496368945399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29950656808275664245963599 44925985212413496368945399)
          ·
            refine ⟨67388977818620244553418099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44925985212413496368945399 67388977818620244553418099)
            ·
              refine ⟨101083466727930366830127149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67388977818620244553418099 101083466727930366830127149)
              ·
                refine ⟨37906300022973887561297681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101083466727930366830127149 37906300022973887561297681)
                ·
                  refine ⟨28429725017230415670973261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37906300022973887561297681 28429725017230415670973261)
                  ·
                    refine ⟨10661146881461405876614973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28429725017230415670973261 10661146881461405876614973)
                    ·
                      refine ⟨3997930080548027203730615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10661146881461405876614973 3997930080548027203730615)
                      ·
                        rfl

theorem cell23_7785941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_7785941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785941 prefixEnd_7785941 := by exact prefixLift 7785941
  have htrace : WordTrace (prefixWord ++ tailWord_7785941) baseStart_7785941 baseEnd_7785941 := by
    simpa [prefixWord, tailWord_7785941, baseEnd_7785941] using wordTrace_append hprefix tailTrace_7785941
  have hstable : (prefixWord ++ tailWord_7785941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785941).length < 2 ^ (prefixWord ++ tailWord_7785941).sum := by decide
  have hdescent : baseEnd_7785941 < baseStart_7785941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785942 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_7785942 : Nat := 118140960795 + 7785942 * 2 ^ 59
def prefixEnd_7785942 : Nat := 4983230072969 + 3 ^ 40 * 7785942 * 2
def baseEnd_7785942 : Nat := 3997930594028681699818111

theorem tailTrace_7785942 : CollatzResearch.WordTrace tailWord_7785942 prefixEnd_7785942 3997930594028681699818111 := by
  unfold tailWord_7785942
  simp only [CollatzResearch.WordTrace]
  refine ⟨17748539647429333867078505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189317756239246227915504053 17748539647429333867078505)
  ·
    refine ⟨13311404735572000400308879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17748539647429333867078505 13311404735572000400308879)
    ·
      refine ⟨19967107103358000600463319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13311404735572000400308879 19967107103358000600463319)
      ·
        refine ⟨29950660655037000900694979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19967107103358000600463319 29950660655037000900694979)
        ·
          refine ⟨44925990982555501351042469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29950660655037000900694979 44925990982555501351042469)
          ·
            refine ⟨8423623309229156503320463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44925990982555501351042469 8423623309229156503320463)
            ·
              refine ⟨12635434963843734754980695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8423623309229156503320463 12635434963843734754980695)
              ·
                refine ⟨18953152445765602132471043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12635434963843734754980695 18953152445765602132471043)
                ·
                  refine ⟨28429728668648403198706565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18953152445765602132471043 28429728668648403198706565)
                  ·
                    refine ⟨5330574125371575599757481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28429728668648403198706565 5330574125371575599757481)
                    ·
                      refine ⟨3997930594028681699818111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5330574125371575599757481 3997930594028681699818111)
                      ·
                        rfl

theorem cell23_7785942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_7785942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785942 prefixEnd_7785942 := by exact prefixLift 7785942
  have htrace : WordTrace (prefixWord ++ tailWord_7785942) baseStart_7785942 baseEnd_7785942 := by
    simpa [prefixWord, tailWord_7785942, baseEnd_7785942] using wordTrace_append hprefix tailTrace_7785942
  have hstable : (prefixWord ++ tailWord_7785942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785942).length < 2 ^ (prefixWord ++ tailWord_7785942).sum := by decide
  have hdescent : baseEnd_7785942 < baseStart_7785942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785944 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 1, 7]
def baseStart_7785944 : Nat := 118140960795 + 7785944 * 2 ^ 59
def prefixEnd_7785944 : Nat := 4983230072969 + 3 ^ 40 * 7785944 * 2
def baseEnd_7785944 : Nat := 1332643873663330230664367

theorem tailTrace_7785944 : CollatzResearch.WordTrace tailWord_7785944 prefixEnd_7785944 1332643873663330230664367 := by
  unfold tailWord_7785944
  simp only [CollatzResearch.WordTrace]
  refine ⟨141988353652431048107414443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189317804869908064143219257 141988353652431048107414443)
  ·
    refine ⟨212982530478646572161121665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141988353652431048107414443 212982530478646572161121665)
    ·
      refine ⟨159736897858984929120841249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212982530478646572161121665 159736897858984929120841249)
      ·
        refine ⟨119802673394238696840630937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159736897858984929120841249 119802673394238696840630937)
        ·
          refine ⟨89852005045679022630473203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119802673394238696840630937 89852005045679022630473203)
          ·
            refine ⟨134778007568518533945709805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89852005045679022630473203 134778007568518533945709805)
            ·
              refine ⟨50541752838194450229641177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134778007568518533945709805 50541752838194450229641177)
              ·
                refine ⟨37906314628645837672230883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50541752838194450229641177 37906314628645837672230883)
                ·
                  refine ⟨56859471942968756508346325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37906314628645837672230883 56859471942968756508346325)
                  ·
                    refine ⟨1332643873663330230664367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56859471942968756508346325 1332643873663330230664367)
                    ·
                      rfl

theorem cell23_7785944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_7785944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785944 prefixEnd_7785944 := by exact prefixLift 7785944
  have htrace : WordTrace (prefixWord ++ tailWord_7785944) baseStart_7785944 baseEnd_7785944 := by
    simpa [prefixWord, tailWord_7785944, baseEnd_7785944] using wordTrace_append hprefix tailTrace_7785944
  have hstable : (prefixWord ++ tailWord_7785944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785944).length < 2 ^ (prefixWord ++ tailWord_7785944).sum := by decide
  have hdescent : baseEnd_7785944 < baseStart_7785944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785981 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_7785981 : Nat := 118140960795 + 7785981 * 2 ^ 59
def prefixEnd_7785981 : Nat := 4983230072969 + 3 ^ 40 * 7785981 * 2
def baseEnd_7785981 : Nat := 3997950619774207047230431

theorem tailTrace_7785981 : CollatzResearch.WordTrace tailWord_7785981 prefixEnd_7785981 3997950619774207047230431 := by
  unfold tailWord_7785981
  simp only [CollatzResearch.WordTrace]
  refine ⟨283978056805728051533925797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189318704537152034355950531 283978056805728051533925797)
  ·
    refine ⟨53245885651074009662611087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283978056805728051533925797 53245885651074009662611087)
    ·
      refine ⟨79868828476611014493916631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53245885651074009662611087 79868828476611014493916631)
      ·
        refine ⟨119803242714916521740874947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79868828476611014493916631 119803242714916521740874947)
        ·
          refine ⟨179704864072374782611312421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119803242714916521740874947 179704864072374782611312421)
          ·
            refine ⟨33694662013570271739621079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179704864072374782611312421 33694662013570271739621079)
            ·
              refine ⟨50541993020355407609431619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33694662013570271739621079 50541993020355407609431619)
              ·
                refine ⟨75812989530533111414147429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50541993020355407609431619 75812989530533111414147429)
                ·
                  refine ⟨14214935536974958390152643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75812989530533111414147429 14214935536974958390152643)
                  ·
                    refine ⟨21322403305462437585228965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14214935536974958390152643 21322403305462437585228965)
                    ·
                      refine ⟨3997950619774207047230431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21322403305462437585228965 3997950619774207047230431)
                      ·
                        rfl

theorem cell23_7785981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_7785981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785981 prefixEnd_7785981 := by exact prefixLift 7785981
  have htrace : WordTrace (prefixWord ++ tailWord_7785981) baseStart_7785981 baseEnd_7785981 := by
    simpa [prefixWord, tailWord_7785981, baseEnd_7785981] using wordTrace_append hprefix tailTrace_7785981
  have hstable : (prefixWord ++ tailWord_7785981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785981).length < 2 ^ (prefixWord ++ tailWord_7785981).sum := by decide
  have hdescent : baseEnd_7785981 < baseStart_7785981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785982 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 7]
def baseStart_7785982 : Nat := 118140960795 + 7785982 * 2 ^ 59
def prefixEnd_7785982 : Nat := 4983230072969 + 3 ^ 40 * 7785982 * 2
def baseEnd_7785982 : Nat := 444216792583873504813103

theorem tailTrace_7785982 : CollatzResearch.WordTrace tailWord_7785982 prefixEnd_7785982 444216792583873504813103 := by
  unfold tailWord_7785982
  simp only [CollatzResearch.WordTrace]
  refine ⟨35497261659840553588089025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189318728852482952469808133 35497261659840553588089025)
  ·
    refine ⟨26622946244880415191066769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35497261659840553588089025 26622946244880415191066769)
    ·
      refine ⟨19967209683660311393300077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26622946244880415191066769 19967209683660311393300077)
      ·
        refine ⟨7487703631372616772487529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19967209683660311393300077 7487703631372616772487529)
        ·
          refine ⟨5615777723529462579365647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7487703631372616772487529 5615777723529462579365647)
          ·
            refine ⟨8423666585294193869048471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5615777723529462579365647 8423666585294193869048471)
            ·
              refine ⟨12635499877941290803572707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8423666585294193869048471 12635499877941290803572707)
              ·
                refine ⟨18953249816911936205359061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12635499877941290803572707 18953249816911936205359061)
                ·
                  refine ⟨444216792583873504813103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18953249816911936205359061 444216792583873504813103)
                  ·
                    rfl

theorem cell23_7785982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_7785982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785982 prefixEnd_7785982 := by exact prefixLift 7785982
  have htrace : WordTrace (prefixWord ++ tailWord_7785982) baseStart_7785982 baseEnd_7785982 := by
    simpa [prefixWord, tailWord_7785982, baseEnd_7785982] using wordTrace_append hprefix tailTrace_7785982
  have hstable : (prefixWord ++ tailWord_7785982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785982).length < 2 ^ (prefixWord ++ tailWord_7785982).sum := by decide
  have hdescent : baseEnd_7785982 < baseStart_7785982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7785988 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_7785988 : Nat := 118140960795 + 7785988 * 2 ^ 59
def prefixEnd_7785988 : Nat := 4983230072969 + 3 ^ 40 * 7785988 * 2
def baseEnd_7785988 : Nat := 3997954214138788519842899

theorem tailTrace_7785988 : CollatzResearch.WordTrace tailWord_7785988 prefixEnd_7785988 3997954214138788519842899 := by
  unfold tailWord_7785988
  simp only [CollatzResearch.WordTrace]
  refine ⟨141989156058351345864715309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189318874744468461152953745 141989156058351345864715309)
  ·
    refine ⟨53245933521881754699268241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141989156058351345864715309 53245933521881754699268241)
    ·
      refine ⟨39934450141411316024451181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53245933521881754699268241 39934450141411316024451181)
      ·
        refine ⟨14975418803029243509169193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39934450141411316024451181 14975418803029243509169193)
        ·
          refine ⟨11231564102271932631876895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14975418803029243509169193 11231564102271932631876895)
          ·
            refine ⟨16847346153407898947815343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11231564102271932631876895 16847346153407898947815343)
            ·
              refine ⟨25271019230111848421723015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16847346153407898947815343 25271019230111848421723015)
              ·
                refine ⟨37906528845167772632584523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25271019230111848421723015 37906528845167772632584523)
                ·
                  refine ⟨56859793267751658948876785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37906528845167772632584523 56859793267751658948876785)
                  ·
                    refine ⟨42644844950813744211657589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56859793267751658948876785 42644844950813744211657589)
                    ·
                      refine ⟨3997954214138788519842899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42644844950813744211657589 3997954214138788519842899)
                      ·
                        rfl

theorem cell23_7785988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_7785988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7785988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7785988 prefixEnd_7785988 := by exact prefixLift 7785988
  have htrace : WordTrace (prefixWord ++ tailWord_7785988) baseStart_7785988 baseEnd_7785988 := by
    simpa [prefixWord, tailWord_7785988, baseEnd_7785988] using wordTrace_append hprefix tailTrace_7785988
  have hstable : (prefixWord ++ tailWord_7785988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7785988).length < 2 ^ (prefixWord ++ tailWord_7785988).sum := by decide
  have hdescent : baseEnd_7785988 < baseStart_7785988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7785988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786001 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 3]
def baseStart_7786001 : Nat := 118140960795 + 7786001 * 2 ^ 59
def prefixEnd_7786001 : Nat := 4983230072969 + 3 ^ 40 * 7786001 * 2
def baseEnd_7786001 : Nat := 3997960889387296968980339

theorem tailTrace_7786001 : CollatzResearch.WordTrace tailWord_7786001 prefixEnd_7786001 3997960889387296968980339 := by
  unfold tailWord_7786001
  simp only [CollatzResearch.WordTrace]
  refine ⟨283978786265655594949653857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189319190843770396633102571 283978786265655594949653857)
  ·
    refine ⟨212984089699241696212240393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283978786265655594949653857 212984089699241696212240393)
    ·
      refine ⟨159738067274431272159180295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212984089699241696212240393 159738067274431272159180295)
      ·
        refine ⟨239607100911646908238770443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159738067274431272159180295 239607100911646908238770443)
        ·
          refine ⟨359410651367470362358155665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239607100911646908238770443 359410651367470362358155665)
          ·
            refine ⟨269557988525602771768616749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359410651367470362358155665 269557988525602771768616749)
            ·
              refine ⟨101084245697101039413231281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269557988525602771768616749 101084245697101039413231281)
              ·
                refine ⟨75813184272825779559923461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101084245697101039413231281 75813184272825779559923461)
                ·
                  refine ⟨14214972051154833667485649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75813184272825779559923461 14214972051154833667485649)
                  ·
                    refine ⟨10661229038366125250614237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14214972051154833667485649 10661229038366125250614237)
                    ·
                      refine ⟨3997960889387296968980339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10661229038366125250614237 3997960889387296968980339)
                      ·
                        rfl

theorem cell23_7786001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_7786001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786001 prefixEnd_7786001 := by exact prefixLift 7786001
  have htrace : WordTrace (prefixWord ++ tailWord_7786001) baseStart_7786001 baseEnd_7786001 := by
    simpa [prefixWord, tailWord_7786001, baseEnd_7786001] using wordTrace_append hprefix tailTrace_7786001
  have hstable : (prefixWord ++ tailWord_7786001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786001).length < 2 ^ (prefixWord ++ tailWord_7786001).sum := by decide
  have hdescent : baseEnd_7786001 < baseStart_7786001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786018 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_7786018 : Nat := 118140960795 + 7786018 * 2 ^ 59
def prefixEnd_7786018 : Nat := 4983230072969 + 3 ^ 40 * 7786018 * 2
def baseEnd_7786018 : Nat := 3997969618558423402467761

theorem tailTrace_7786018 : CollatzResearch.WordTrace tailWord_7786018 prefixEnd_7786018 3997969618558423402467761 := by
  unfold tailWord_7786018
  simp only [CollatzResearch.WordTrace]
  refine ⟨70994851576648501713255677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189319604204396004568681805 70994851576648501713255677)
  ·
    refine ⟨26623069341243188142470879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70994851576648501713255677 26623069341243188142470879)
    ·
      refine ⟨39934604011864782213706319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26623069341243188142470879 39934604011864782213706319)
      ·
        refine ⟨59901906017797173320559479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39934604011864782213706319 59901906017797173320559479)
        ·
          refine ⟨89852859026695759980839219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59901906017797173320559479 89852859026695759980839219)
          ·
            refine ⟨134779288540043639971258829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89852859026695759980839219 134779288540043639971258829)
            ·
              refine ⟨50542233202516364989222061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134779288540043639971258829 50542233202516364989222061)
              ·
                refine ⟨18953337450943636870958273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50542233202516364989222061 18953337450943636870958273)
                ·
                  refine ⟨14215003088207727653218705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18953337450943636870958273 14215003088207727653218705)
                  ·
                    refine ⟨10661252316155795739914029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14215003088207727653218705 10661252316155795739914029)
                    ·
                      refine ⟨3997969618558423402467761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10661252316155795739914029 3997969618558423402467761)
                      ·
                        rfl

theorem cell23_7786018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_7786018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786018 prefixEnd_7786018 := by exact prefixLift 7786018
  have htrace : WordTrace (prefixWord ++ tailWord_7786018) baseStart_7786018 baseEnd_7786018 := by
    simpa [prefixWord, tailWord_7786018, baseEnd_7786018] using wordTrace_append hprefix tailTrace_7786018
  have hstable : (prefixWord ++ tailWord_7786018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786018).length < 2 ^ (prefixWord ++ tailWord_7786018).sum := by decide
  have hdescent : baseEnd_7786018 < baseStart_7786018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786048 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 3, 1, 3]
def baseStart_7786048 : Nat := 118140960795 + 7786048 * 2 ^ 59
def prefixEnd_7786048 : Nat := 4983230072969 + 3 ^ 40 * 7786048 * 2
def baseEnd_7786048 : Nat := 3997985022978058285092623

theorem tailTrace_7786048 : CollatzResearch.WordTrace tailWord_7786048 prefixEnd_7786048 3997985022978058285092623 := by
  unfold tailWord_7786048
  simp only [CollatzResearch.WordTrace]
  refine ⟨141990250248242660988307399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189320333664323547984409865 141990250248242660988307399)
  ·
    refine ⟨212985375372363991482461099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141990250248242660988307399 212985375372363991482461099)
    ·
      refine ⟨319478063058545987223691649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212985375372363991482461099 319478063058545987223691649)
      ·
        refine ⟨239608547293909490417768737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319478063058545987223691649 239608547293909490417768737)
        ·
          refine ⟨179706410470432117813326553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239608547293909490417768737 179706410470432117813326553)
          ·
            refine ⟨134779807852824088359994915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179706410470432117813326553 134779807852824088359994915)
            ·
              refine ⟨202169711779236132539992373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134779807852824088359994915 202169711779236132539992373)
              ·
                refine ⟨18953410479303387425624285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202169711779236132539992373 18953410479303387425624285)
                ·
                  refine ⟨7107528929738770284609107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18953410479303387425624285 7107528929738770284609107)
                  ·
                    refine ⟨10661293394608155426913661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7107528929738770284609107 10661293394608155426913661)
                    ·
                      refine ⟨3997985022978058285092623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10661293394608155426913661 3997985022978058285092623)
                      ·
                        rfl

theorem cell23_7786048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 3, 1, 3].length) (baseStart_7786048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786048 prefixEnd_7786048 := by exact prefixLift 7786048
  have htrace : WordTrace (prefixWord ++ tailWord_7786048) baseStart_7786048 baseEnd_7786048 := by
    simpa [prefixWord, tailWord_7786048, baseEnd_7786048] using wordTrace_append hprefix tailTrace_7786048
  have hstable : (prefixWord ++ tailWord_7786048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786048).length < 2 ^ (prefixWord ++ tailWord_7786048).sum := by decide
  have hdescent : baseEnd_7786048 < baseStart_7786048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786058 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 1, 5, 2]
def baseStart_7786058 : Nat := 118140960795 + 7786058 * 2 ^ 59
def prefixEnd_7786058 : Nat := 4983230072969 + 3 ^ 40 * 7786058 * 2
def baseEnd_7786058 : Nat := 3997990157784603245967577

theorem tailTrace_7786058 : CollatzResearch.WordTrace tailWord_7786058 prefixEnd_7786058 3997990157784603245967577 := by
  unfold tailWord_7786058
  simp only [CollatzResearch.WordTrace]
  refine ⟨70995216306612273421119707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189320576817632729122985885 70995216306612273421119707)
  ·
    refine ⟨106492824459918410131679561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70995216306612273421119707 106492824459918410131679561)
    ·
      refine ⟨79869618344938807598759671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106492824459918410131679561 79869618344938807598759671)
      ·
        refine ⟨119804427517408211398139507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79869618344938807598759671 119804427517408211398139507)
        ·
          refine ⟨179706641276112317097209261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119804427517408211398139507 179706641276112317097209261)
          ·
            refine ⟨67389990478542118911453473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179706641276112317097209261 67389990478542118911453473)
            ·
              refine ⟨50542492858906589183590105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67389990478542118911453473 50542492858906589183590105)
              ·
                refine ⟨37906869644179941887692579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50542492858906589183590105 37906869644179941887692579)
                ·
                  refine ⟨56860304466269912831538869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37906869644179941887692579 56860304466269912831538869)
                  ·
                    refine ⟨5330653543712804327956769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56860304466269912831538869 5330653543712804327956769)
                    ·
                      refine ⟨3997990157784603245967577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5330653543712804327956769 3997990157784603245967577)
                      ·
                        rfl

theorem cell23_7786058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_7786058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786058 prefixEnd_7786058 := by exact prefixLift 7786058
  have htrace : WordTrace (prefixWord ++ tailWord_7786058) baseStart_7786058 baseEnd_7786058 := by
    simpa [prefixWord, tailWord_7786058, baseEnd_7786058] using wordTrace_append hprefix tailTrace_7786058
  have hstable : (prefixWord ++ tailWord_7786058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786058).length < 2 ^ (prefixWord ++ tailWord_7786058).sum := by decide
  have hdescent : baseEnd_7786058 < baseStart_7786058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786068 : List Nat := [2, 4, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_7786068 : Nat := 118140960795 + 7786068 * 2 ^ 59
def prefixEnd_7786068 : Nat := 4983230072969 + 3 ^ 40 * 7786068 * 2
def baseEnd_7786068 : Nat := 1332665097530382735614177

theorem tailTrace_7786068 : CollatzResearch.WordTrace tailWord_7786068 prefixEnd_7786068 1332665097530382735614177 := by
  unfold tailWord_7786068
  simp only [CollatzResearch.WordTrace]
  refine ⟨141990614978206432696171429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189320819970941910261561905 141990614978206432696171429)
  ·
    refine ⟨26623240308413706130532143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141990614978206432696171429 26623240308413706130532143)
    ·
      refine ⟨39934860462620559195798215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26623240308413706130532143 39934860462620559195798215)
      ·
        refine ⟨59902290693930838793697323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39934860462620559195798215 59902290693930838793697323)
        ·
          refine ⟨89853436040896258190545985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59902290693930838793697323 89853436040896258190545985)
          ·
            refine ⟨67390077030672193642909489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89853436040896258190545985 67390077030672193642909489)
            ·
              refine ⟨50542557773004145232182117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67390077030672193642909489 50542557773004145232182117)
              ·
                refine ⟨9476729582438277231034147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50542557773004145232182117 9476729582438277231034147)
                ·
                  refine ⟨14215094373657415846551221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9476729582438277231034147 14215094373657415846551221)
                  ·
                    refine ⟨1332665097530382735614177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14215094373657415846551221 1332665097530382735614177)
                    ·
                      rfl

theorem cell23_7786068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_7786068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786068 prefixEnd_7786068 := by exact prefixLift 7786068
  have htrace : WordTrace (prefixWord ++ tailWord_7786068) baseStart_7786068 baseEnd_7786068 := by
    simpa [prefixWord, tailWord_7786068, baseEnd_7786068] using wordTrace_append hprefix tailTrace_7786068
  have hstable : (prefixWord ++ tailWord_7786068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786068).length < 2 ^ (prefixWord ++ tailWord_7786068).sum := by decide
  have hdescent : baseEnd_7786068 < baseStart_7786068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786081 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 1, 6]
def baseStart_7786081 : Nat := 118140960795 + 7786081 * 2 ^ 59
def prefixEnd_7786081 : Nat := 4983230072969 + 3 ^ 40 * 7786081 * 2
def baseEnd_7786081 : Nat := 1332667322613218885326657

theorem tailTrace_7786081 : CollatzResearch.WordTrace tailWord_7786081 prefixEnd_7786081 1332667322613218885326657 := by
  unfold tailWord_7786081
  simp only [CollatzResearch.WordTrace]
  refine ⟨283981704105365768612566097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189321136070243845741710731 283981704105365768612566097)
  ·
    refine ⟨212986278079024326459424573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283981704105365768612566097 212986278079024326459424573)
    ·
      refine ⟨79869854279634122422284215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212986278079024326459424573 79869854279634122422284215)
      ·
        refine ⟨119804781419451183633426323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79869854279634122422284215 119804781419451183633426323)
        ·
          refine ⟨179707172129176775450139485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119804781419451183633426323 179707172129176775450139485)
          ·
            refine ⟨67390189548441290793802307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179707172129176775450139485 67390189548441290793802307)
            ·
              refine ⟨101085284322661936190703461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67390189548441290793802307 101085284322661936190703461)
              ·
                refine ⟨18953490810499113035756899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101085284322661936190703461 18953490810499113035756899)
                ·
                  refine ⟨28430236215748669553635349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18953490810499113035756899 28430236215748669553635349)
                  ·
                    refine ⟨1332667322613218885326657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28430236215748669553635349 1332667322613218885326657)
                    ·
                      rfl

theorem cell23_7786081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_7786081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786081 prefixEnd_7786081 := by exact prefixLift 7786081
  have htrace : WordTrace (prefixWord ++ tailWord_7786081) baseStart_7786081 baseEnd_7786081 := by
    simpa [prefixWord, tailWord_7786081, baseEnd_7786081] using wordTrace_append hprefix tailTrace_7786081
  have hstable : (prefixWord ++ tailWord_7786081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786081).length < 2 ^ (prefixWord ++ tailWord_7786081).sum := by decide
  have hdescent : baseEnd_7786081 < baseStart_7786081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786085 : List Nat := [1, 3, 1, 3, 3, 1, 4, 1, 1, 5]
def baseStart_7786085 : Nat := 118140960795 + 7786085 * 2 ^ 59
def prefixEnd_7786085 : Nat := 4983230072969 + 3 ^ 40 * 7786085 * 2
def baseEnd_7786085 : Nat := 1332668007254091546776651

theorem tailTrace_7786085 : CollatzResearch.WordTrace tailWord_7786085 prefixEnd_7786085 1332668007254091546776651 := by
  unfold tailWord_7786085
  simp only [CollatzResearch.WordTrace]
  refine ⟨283981849997351277295711709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189321233331567518197141139 283981849997351277295711709)
  ·
    refine ⟨106493193749006728985891891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283981849997351277295711709 106493193749006728985891891)
    ·
      refine ⟨159739790623510093478837837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106493193749006728985891891 159739790623510093478837837)
      ·
        refine ⟨59902421483816285054564189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159739790623510093478837837 59902421483816285054564189)
        ·
          refine ⟨22463408056431106895461571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59902421483816285054564189 22463408056431106895461571)
          ·
            refine ⟨33695112084646660343192357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22463408056431106895461571 33695112084646660343192357)
            ·
              refine ⟨6317833515871248814348567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33695112084646660343192357 6317833515871248814348567)
              ·
                refine ⟨9476750273806873221522851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6317833515871248814348567 9476750273806873221522851)
                ·
                  refine ⟨14215125410710309832284277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9476750273806873221522851 14215125410710309832284277)
                  ·
                    refine ⟨1332668007254091546776651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14215125410710309832284277 1332668007254091546776651)
                    ·
                      rfl

theorem cell23_7786085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 1, 5].length) (baseStart_7786085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786085 prefixEnd_7786085 := by exact prefixLift 7786085
  have htrace : WordTrace (prefixWord ++ tailWord_7786085) baseStart_7786085 baseEnd_7786085 := by
    simpa [prefixWord, tailWord_7786085, baseEnd_7786085] using wordTrace_append hprefix tailTrace_7786085
  have hstable : (prefixWord ++ tailWord_7786085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786085).length < 2 ^ (prefixWord ++ tailWord_7786085).sum := by decide
  have hdescent : baseEnd_7786085 < baseStart_7786085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786122 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 3, 2, 2]
def baseStart_7786122 : Nat := 118140960795 + 7786122 * 2 ^ 59
def prefixEnd_7786122 : Nat := 4983230072969 + 3 ^ 40 * 7786122 * 2
def baseEnd_7786122 : Nat := 3998023020546490995567283

theorem tailTrace_7786122 : CollatzResearch.WordTrace tailWord_7786122 prefixEnd_7786122 3998023020546490995567283 := by
  unfold tailWord_7786122
  simp only [CollatzResearch.WordTrace]
  refine ⟨70995799874554308153702155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189322132998811488409872413 70995799874554308153702155)
  ·
    refine ⟨106493699811831462230553233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70995799874554308153702155 106493699811831462230553233)
    ·
      refine ⟨79870274858873596672914925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106493699811831462230553233 79870274858873596672914925)
      ·
        refine ⟨29951353072077598752343097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79870274858873596672914925 29951353072077598752343097)
        ·
          refine ⟨22463514804058199064257323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29951353072077598752343097 22463514804058199064257323)
          ·
            refine ⟨33695272206087298596385985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22463514804058199064257323 33695272206087298596385985)
            ·
              refine ⟨25271454154565473947289489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33695272206087298596385985 25271454154565473947289489)
              ·
                refine ⟨18953590615924105460467117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25271454154565473947289489 18953590615924105460467117)
                ·
                  refine ⟨7107596480971539547675169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18953590615924105460467117 7107596480971539547675169)
                  ·
                    refine ⟨5330697360728654660756377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7107596480971539547675169 5330697360728654660756377)
                    ·
                      refine ⟨3998023020546490995567283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5330697360728654660756377 3998023020546490995567283)
                      ·
                        rfl

theorem cell23_7786122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_7786122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786122 prefixEnd_7786122 := by exact prefixLift 7786122
  have htrace : WordTrace (prefixWord ++ tailWord_7786122) baseStart_7786122 baseEnd_7786122 := by
    simpa [prefixWord, tailWord_7786122, baseEnd_7786122] using wordTrace_append hprefix tailTrace_7786122
  have hstable : (prefixWord ++ tailWord_7786122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786122).length < 2 ^ (prefixWord ++ tailWord_7786122).sum := by decide
  have hdescent : baseEnd_7786122 < baseStart_7786122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786141 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 1, 9]
def baseStart_7786141 : Nat := 118140960795 + 7786141 * 2 ^ 59
def prefixEnd_7786141 : Nat := 4983230072969 + 3 ^ 40 * 7786141 * 2
def baseEnd_7786141 : Nat := 1332677592226308807076565

theorem tailTrace_7786141 : CollatzResearch.WordTrace tailWord_7786141 prefixEnd_7786141 1332677592226308807076565 := by
  unfold tailWord_7786141
  simp only [CollatzResearch.WordTrace]
  refine ⟨283983892485148398859750277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189322594990098932573166851 283983892485148398859750277)
  ·
    refine ⟨53246979840965324786203177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283983892485148398859750277 53246979840965324786203177)
    ·
      refine ⟨39935234880723993589652383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53246979840965324786203177 39935234880723993589652383)
      ·
        refine ⟨59902852321085990384478575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39935234880723993589652383 59902852321085990384478575)
        ·
          refine ⟨89854278481628985576717863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59902852321085990384478575 89854278481628985576717863)
          ·
            refine ⟨134781417722443478365076795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89854278481628985576717863 134781417722443478365076795)
            ·
              refine ⟨202172126583665217547615193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134781417722443478365076795 202172126583665217547615193)
              ·
                refine ⟨151629094937748913160711395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202172126583665217547615193 151629094937748913160711395)
                ·
                  refine ⟨227443642406623369741067093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151629094937748913160711395 227443642406623369741067093)
                  ·
                    refine ⟨1332677592226308807076565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 227443642406623369741067093 1332677592226308807076565)
                    ·
                      rfl

theorem cell23_7786141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_7786141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786141 prefixEnd_7786141 := by exact prefixLift 7786141
  have htrace : WordTrace (prefixWord ++ tailWord_7786141) baseStart_7786141 baseEnd_7786141 := by
    simpa [prefixWord, tailWord_7786141, baseEnd_7786141] using wordTrace_append hprefix tailTrace_7786141
  have hstable : (prefixWord ++ tailWord_7786141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786141).length < 2 ^ (prefixWord ++ tailWord_7786141).sum := by decide
  have hdescent : baseEnd_7786141 < baseStart_7786141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786142 : List Nat := [4, 3, 1, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_7786142 : Nat := 118140960795 + 7786142 * 2 ^ 59
def prefixEnd_7786142 : Nat := 4983230072969 + 3 ^ 40 * 7786142 * 2
def baseEnd_7786142 : Nat := 3998033290159580917317191

theorem tailTrace_7786142 : CollatzResearch.WordTrace tailWord_7786142 prefixEnd_7786142 3998033290159580917317191 := by
  unfold tailWord_7786142
  simp only [CollatzResearch.WordTrace]
  refine ⟨35497991119768097003817085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189322619305429850687024453 35497991119768097003817085)
  ·
    refine ⟨13311746669913036376431407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35497991119768097003817085 13311746669913036376431407)
    ·
      refine ⟨19967620004869554564647111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13311746669913036376431407 19967620004869554564647111)
      ·
        refine ⟨29951430007304331846970667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19967620004869554564647111 29951430007304331846970667)
        ·
          refine ⟨44927145010956497770456001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29951430007304331846970667 44927145010956497770456001)
          ·
            refine ⟨33695358758217373327842001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44927145010956497770456001 33695358758217373327842001)
            ·
              refine ⟨25271519068663029995881501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33695358758217373327842001 25271519068663029995881501)
              ·
                refine ⟨9476819650748636248455563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25271519068663029995881501 9476819650748636248455563)
                ·
                  refine ⟨14215229476122954372683345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9476819650748636248455563 14215229476122954372683345)
                  ·
                    refine ⟨10661422107092215779512509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14215229476122954372683345 10661422107092215779512509)
                    ·
                      refine ⟨3998033290159580917317191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10661422107092215779512509 3998033290159580917317191)
                      ·
                        rfl

theorem cell23_7786142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_7786142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786142 prefixEnd_7786142 := by exact prefixLift 7786142
  have htrace : WordTrace (prefixWord ++ tailWord_7786142) baseStart_7786142 baseEnd_7786142 := by
    simpa [prefixWord, tailWord_7786142, baseEnd_7786142] using wordTrace_append hprefix tailTrace_7786142
  have hstable : (prefixWord ++ tailWord_7786142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786142).length < 2 ^ (prefixWord ++ tailWord_7786142).sum := by decide
  have hdescent : baseEnd_7786142 < baseStart_7786142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786166 : List Nat := [5, 1, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_7786166 : Nat := 118140960795 + 7786166 * 2 ^ 59
def prefixEnd_7786166 : Nat := 4983230072969 + 3 ^ 40 * 7786166 * 2
def baseEnd_7786166 : Nat := 1332681871231762941139027

theorem tailTrace_7786166 : CollatzResearch.WordTrace tailWord_7786166 prefixEnd_7786166 1332681871231762941139027 := by
  unfold tailWord_7786166
  simp only [CollatzResearch.WordTrace]
  refine ⟨17749050269378614258088147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189323202873371885419606901 17749050269378614258088147)
  ·
    refine ⟨26623575404067921387132221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17749050269378614258088147 26623575404067921387132221)
    ·
      refine ⟨9983840776525470520174583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26623575404067921387132221 9983840776525470520174583)
      ·
        refine ⟨14975761164788205780261875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9983840776525470520174583 14975761164788205780261875)
        ·
          refine ⟨22463641747182308670392813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14975761164788205780261875 22463641747182308670392813)
          ·
            refine ⟨8423865655193365751397305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22463641747182308670392813 8423865655193365751397305)
            ·
              refine ⟨6317899241395024313547979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8423865655193365751397305 6317899241395024313547979)
              ·
                refine ⟨9476848862092536470321969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6317899241395024313547979 9476848862092536470321969)
                ·
                  refine ⟨7107636646569402352741477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9476848862092536470321969 7107636646569402352741477)
                  ·
                    refine ⟨1332681871231762941139027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7107636646569402352741477 1332681871231762941139027)
                    ·
                      rfl

theorem cell23_7786166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_7786166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786166 prefixEnd_7786166 := by exact prefixLift 7786166
  have htrace : WordTrace (prefixWord ++ tailWord_7786166) baseStart_7786166 baseEnd_7786166 := by
    simpa [prefixWord, tailWord_7786166, baseEnd_7786166] using wordTrace_append hprefix tailTrace_7786166
  have hstable : (prefixWord ++ tailWord_7786166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786166).length < 2 ^ (prefixWord ++ tailWord_7786166).sum := by decide
  have hdescent : baseEnd_7786166 < baseStart_7786166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786171 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 2, 6]
def baseStart_7786171 : Nat := 118140960795 + 7786171 * 2 ^ 59
def prefixEnd_7786171 : Nat := 4983230072969 + 3 ^ 40 * 7786171 * 2
def baseEnd_7786171 : Nat := 1332682727032853767951519

theorem tailTrace_7786171 : CollatzResearch.WordTrace tailWord_7786171 prefixEnd_7786171 1332682727032853767951519 := by
  unfold tailWord_7786171
  simp only [CollatzResearch.WordTrace]
  refine ⟨283984986675039713983342367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189323324450026475988894911 283984986675039713983342367)
  ·
    refine ⟨425977480012559570975013551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283984986675039713983342367 425977480012559570975013551)
    ·
      refine ⟨638966220018839356462520327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425977480012559570975013551 638966220018839356462520327)
      ·
        refine ⟨958449330028259034693780491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638966220018839356462520327 958449330028259034693780491)
        ·
          refine ⟨1437673995042388552040670737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958449330028259034693780491 1437673995042388552040670737)
          ·
            refine ⟨1078255496281791414030503053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1437673995042388552040670737 1078255496281791414030503053)
            ·
              refine ⟨404345811105671780261438645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1078255496281791414030503053 404345811105671780261438645)
              ·
                refine ⟨37907419791156729399509873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 404345811105671780261438645 37907419791156729399509873)
                ·
                  refine ⟨28430564843367547049632405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37907419791156729399509873 28430564843367547049632405)
                  ·
                    refine ⟨1332682727032853767951519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28430564843367547049632405 1332682727032853767951519)
                    ·
                      rfl

theorem cell23_7786171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 6].length) (baseStart_7786171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786171 prefixEnd_7786171 := by exact prefixLift 7786171
  have htrace : WordTrace (prefixWord ++ tailWord_7786171) baseStart_7786171 baseEnd_7786171 := by
    simpa [prefixWord, tailWord_7786171, baseEnd_7786171] using wordTrace_append hprefix tailTrace_7786171
  have hstable : (prefixWord ++ tailWord_7786171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786171).length < 2 ^ (prefixWord ++ tailWord_7786171).sum := by decide
  have hdescent : baseEnd_7786171 < baseStart_7786171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786172 : List Nat := [2, 2, 2, 3, 1, 3, 1, 3, 2, 1, 3]
def baseStart_7786172 : Nat := 118140960795 + 7786172 * 2 ^ 59
def prefixEnd_7786172 : Nat := 4983230072969 + 3 ^ 40 * 7786172 * 2
def baseEnd_7786172 : Nat := 3998048694579215799942053

theorem tailTrace_7786172 : CollatzResearch.WordTrace tailWord_7786172 prefixEnd_7786172 3998048694579215799942053 := by
  unfold tailWord_7786172
  simp only [CollatzResearch.WordTrace]
  refine ⟨141992511574018045577064385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189323348765357394102752513 141992511574018045577064385)
  ·
    refine ⟨106494383680513534182798289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141992511574018045577064385 106494383680513534182798289)
    ·
      refine ⟨79870787760385150637098717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106494383680513534182798289 79870787760385150637098717)
      ·
        refine ⟨29951545410144431488912019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79870787760385150637098717 29951545410144431488912019)
        ·
          refine ⟨44927318115216647233368029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29951545410144431488912019 44927318115216647233368029)
          ·
            refine ⟨16847744293206242712513011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44927318115216647233368029 16847744293206242712513011)
            ·
              refine ⟨25271616439809364068769517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16847744293206242712513011 25271616439809364068769517)
              ·
                refine ⟨9476856164928511525788569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25271616439809364068769517 9476856164928511525788569)
                ·
                  refine ⟨7107642123696383644341427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9476856164928511525788569 7107642123696383644341427)
                  ·
                    refine ⟨10661463185544575466512141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7107642123696383644341427 10661463185544575466512141)
                    ·
                      refine ⟨3998048694579215799942053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10661463185544575466512141 3998048694579215799942053)
                      ·
                        rfl

theorem cell23_7786172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_7786172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786172 prefixEnd_7786172 := by exact prefixLift 7786172
  have htrace : WordTrace (prefixWord ++ tailWord_7786172) baseStart_7786172 baseEnd_7786172 := by
    simpa [prefixWord, tailWord_7786172, baseEnd_7786172] using wordTrace_append hprefix tailTrace_7786172
  have hstable : (prefixWord ++ tailWord_7786172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786172).length < 2 ^ (prefixWord ++ tailWord_7786172).sum := by decide
  have hdescent : baseEnd_7786172 < baseStart_7786172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786181 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 3, 3, 5]
def baseStart_7786181 : Nat := 118140960795 + 7786181 * 2 ^ 59
def prefixEnd_7786181 : Nat := 4983230072969 + 3 ^ 40 * 7786181 * 2
def baseEnd_7786181 : Nat := 3998053315905106264729511

theorem tailTrace_7786181 : CollatzResearch.WordTrace tailWord_7786181 prefixEnd_7786181 3998053315905106264729511 := by
  unfold tailWord_7786181
  simp only [CollatzResearch.WordTrace]
  refine ⟨283985351405003485691206397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189323567603335657127470931 283985351405003485691206397)
  ·
    refine ⟨106494506776876307134202399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283985351405003485691206397 106494506776876307134202399)
    ·
      refine ⟨159741760165314460701303599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106494506776876307134202399 159741760165314460701303599)
      ·
        refine ⟨239612640247971691051955399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159741760165314460701303599 239612640247971691051955399)
        ·
          refine ⟨359418960371957536577933099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239612640247971691051955399 359418960371957536577933099)
          ·
            refine ⟨539128440557936304866899649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359418960371957536577933099 539128440557936304866899649)
            ·
              refine ⟨404346330418452228650174737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539128440557936304866899649 404346330418452228650174737)
              ·
                refine ⟨303259747813839171487631053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404346330418452228650174737 303259747813839171487631053)
                ·
                  refine ⟨113722405430189689307861645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303259747813839171487631053 113722405430189689307861645)
                  ·
                    refine ⟨42645902036321133490448117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113722405430189689307861645 42645902036321133490448117)
                    ·
                      refine ⟨3998053315905106264729511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42645902036321133490448117 3998053315905106264729511)
                      ·
                        rfl

theorem cell23_7786181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_7786181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786181 prefixEnd_7786181 := by exact prefixLift 7786181
  have htrace : WordTrace (prefixWord ++ tailWord_7786181) baseStart_7786181 baseEnd_7786181 := by
    simpa [prefixWord, tailWord_7786181, baseEnd_7786181] using wordTrace_append hprefix tailTrace_7786181
  have hstable : (prefixWord ++ tailWord_7786181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786181).length < 2 ^ (prefixWord ++ tailWord_7786181).sum := by decide
  have hdescent : baseEnd_7786181 < baseStart_7786181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786248 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 1, 7]
def baseStart_7786248 : Nat := 118140960795 + 7786248 * 2 ^ 59
def prefixEnd_7786248 : Nat := 4983230072969 + 3 ^ 40 * 7786248 * 2
def baseEnd_7786248 : Nat := 1332695906369652500863901

theorem tailTrace_7786248 : CollatzResearch.WordTrace tailWord_7786248 prefixEnd_7786248 1332695906369652500863901 := by
  unfold tailWord_7786248
  simp only [CollatzResearch.WordTrace]
  refine ⟨141993897547880378066947699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189325196730507170755930265 141993897547880378066947699)
  ·
    refine ⟨212990846321820567100421549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141993897547880378066947699 212990846321820567100421549)
    ·
      refine ⟨79871567370682712662658081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212990846321820567100421549 79871567370682712662658081)
      ·
        refine ⟨59903675528012034496993561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79871567370682712662658081 59903675528012034496993561)
        ·
          refine ⟨44927756646009025872745171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59903675528012034496993561 44927756646009025872745171)
          ·
            refine ⟨67391634969013538809117757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44927756646009025872745171 67391634969013538809117757)
            ·
              refine ⟨25271863113380077053419159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67391634969013538809117757 25271863113380077053419159)
              ·
                refine ⟨37907794670070115580128739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25271863113380077053419159 37907794670070115580128739)
                ·
                  refine ⟨56861692005105173370193109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37907794670070115580128739 56861692005105173370193109)
                  ·
                    refine ⟨1332695906369652500863901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56861692005105173370193109 1332695906369652500863901)
                    ·
                      rfl

theorem cell23_7786248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_7786248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786248 prefixEnd_7786248 := by exact prefixLift 7786248
  have htrace : WordTrace (prefixWord ++ tailWord_7786248) baseStart_7786248 baseEnd_7786248 := by
    simpa [prefixWord, tailWord_7786248, baseEnd_7786248] using wordTrace_append hprefix tailTrace_7786248
  have hstable : (prefixWord ++ tailWord_7786248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786248).length < 2 ^ (prefixWord ++ tailWord_7786248).sum := by decide
  have hdescent : baseEnd_7786248 < baseStart_7786248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786322 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_7786322 : Nat := 118140960795 + 7786322 * 2 ^ 59
def prefixEnd_7786322 : Nat := 4983230072969 + 3 ^ 40 * 7786322 * 2
def baseEnd_7786322 : Nat := 3998125716677390213066363

theorem tailTrace_7786322 : CollatzResearch.WordTrace tailWord_7786322 prefixEnd_7786322 3998125716677390213066363 := by
  unfold tailWord_7786322
  simp only [CollatzResearch.WordTrace]
  refine ⟨70997623524373166693022305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189326996064995111181392813 70997623524373166693022305)
  ·
    refine ⟨53248217643279875019766729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70997623524373166693022305 53248217643279875019766729)
    ·
      refine ⟨39936163232459906264825047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53248217643279875019766729 39936163232459906264825047)
      ·
        refine ⟨59904244848689859397237571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39936163232459906264825047 59904244848689859397237571)
        ·
          refine ⟨89856367273034789095856357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59904244848689859397237571 89856367273034789095856357)
          ·
            refine ⟨16848068863694022955473067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89856367273034789095856357 16848068863694022955473067)
            ·
              refine ⟨25272103295541034433209601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16848068863694022955473067 25272103295541034433209601)
              ·
                refine ⟨18954077471655775824907201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25272103295541034433209601 18954077471655775824907201)
                ·
                  refine ⟨14215558103741831868680401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18954077471655775824907201 14215558103741831868680401)
                  ·
                    refine ⟨10661668577806373901510301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14215558103741831868680401 10661668577806373901510301)
                    ·
                      refine ⟨3998125716677390213066363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10661668577806373901510301 3998125716677390213066363)
                      ·
                        rfl

theorem cell23_7786322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_7786322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786322 prefixEnd_7786322 := by exact prefixLift 7786322
  have htrace : WordTrace (prefixWord ++ tailWord_7786322) baseStart_7786322 baseEnd_7786322 := by
    simpa [prefixWord, tailWord_7786322, baseEnd_7786322] using wordTrace_append hprefix tailTrace_7786322
  have hstable : (prefixWord ++ tailWord_7786322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786322).length < 2 ^ (prefixWord ++ tailWord_7786322).sum := by decide
  have hdescent : baseEnd_7786322 < baseStart_7786322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786329 : List Nat := [1, 2, 1, 2, 2, 3, 5, 2, 1, 4]
def baseStart_7786329 : Nat := 118140960795 + 7786329 * 2 ^ 59
def prefixEnd_7786329 : Nat := 4983230072969 + 3 ^ 40 * 7786329 * 2
def baseEnd_7786329 : Nat := 1332709770347323895226277

theorem tailTrace_7786329 : CollatzResearch.WordTrace tailWord_7786329 prefixEnd_7786329 1332709770347323895226277 := by
  unfold tailWord_7786329
  simp only [CollatzResearch.WordTrace]
  refine ⟨283990749408467306967594041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189327166272311537978396027 283990749408467306967594041)
  ·
    refine ⟨212993062056350480225695531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283990749408467306967594041 212993062056350480225695531)
    ·
      refine ⟨319489593084525720338543297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212993062056350480225695531 319489593084525720338543297)
      ·
        refine ⟨239617194813394290253907473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319489593084525720338543297 239617194813394290253907473)
        ·
          refine ⟨179712896110045717690430605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239617194813394290253907473 179712896110045717690430605)
          ·
            refine ⟨67392336041267144133911477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179712896110045717690430605 67392336041267144133911477)
            ·
              refine ⟨6318031503868794762554201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67392336041267144133911477 6318031503868794762554201)
              ·
                refine ⟨4738523627901596071915651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6318031503868794762554201 4738523627901596071915651)
                ·
                  refine ⟨7107785441852394107873477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4738523627901596071915651 7107785441852394107873477)
                  ·
                    refine ⟨1332709770347323895226277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7107785441852394107873477 1332709770347323895226277)
                    ·
                      rfl

theorem cell23_7786329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 1, 4].length) (baseStart_7786329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786329 prefixEnd_7786329 := by exact prefixLift 7786329
  have htrace : WordTrace (prefixWord ++ tailWord_7786329) baseStart_7786329 baseEnd_7786329 := by
    simpa [prefixWord, tailWord_7786329, baseEnd_7786329] using wordTrace_append hprefix tailTrace_7786329
  have hstable : (prefixWord ++ tailWord_7786329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786329).length < 2 ^ (prefixWord ++ tailWord_7786329).sum := by decide
  have hdescent : baseEnd_7786329 < baseStart_7786329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786345 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 3, 5, 2]
def baseStart_7786345 : Nat := 118140960795 + 7786345 * 2 ^ 59
def prefixEnd_7786345 : Nat := 4983230072969 + 3 ^ 40 * 7786345 * 2
def baseEnd_7786345 : Nat := 3998137526732443623078757

theorem tailTrace_7786345 : CollatzResearch.WordTrace tailWord_7786345 prefixEnd_7786345 3998137526732443623078757 := by
  unfold tailWord_7786345
  simp only [CollatzResearch.WordTrace]
  refine ⟨283991332976409341700176489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189327555317606227800117659 283991332976409341700176489)
  ·
    refine ⟨212993499732307006275132367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283991332976409341700176489 212993499732307006275132367)
    ·
      refine ⟨319490249598460509412698551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212993499732307006275132367 319490249598460509412698551)
      ·
        refine ⟨479235374397690764119047827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319490249598460509412698551 479235374397690764119047827)
        ·
          refine ⟨718853061596536146178571741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479235374397690764119047827 718853061596536146178571741)
          ·
            refine ⟨269569898098701054816964403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 718853061596536146178571741 269569898098701054816964403)
            ·
              refine ⟨404354847148051582225446605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269569898098701054816964403 404354847148051582225446605)
              ·
                refine ⟨151633067680519343334542477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404354847148051582225446605 151633067680519343334542477)
                ·
                  refine ⟨56862400380194753750453429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151633067680519343334542477 56862400380194753750453429)
                  ·
                    refine ⟨5330850035643258164105009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56862400380194753750453429 5330850035643258164105009)
                    ·
                      refine ⟨3998137526732443623078757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5330850035643258164105009 3998137526732443623078757)
                      ·
                        rfl

theorem cell23_7786345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 5, 2].length) (baseStart_7786345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786345 prefixEnd_7786345 := by exact prefixLift 7786345
  have htrace : WordTrace (prefixWord ++ tailWord_7786345) baseStart_7786345 baseEnd_7786345 := by
    simpa [prefixWord, tailWord_7786345, baseEnd_7786345] using wordTrace_append hprefix tailTrace_7786345
  have hstable : (prefixWord ++ tailWord_7786345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786345).length < 2 ^ (prefixWord ++ tailWord_7786345).sum := by decide
  have hdescent : baseEnd_7786345 < baseStart_7786345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786362 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2]
def baseStart_7786362 : Nat := 118140960795 + 7786362 * 2 ^ 59
def prefixEnd_7786362 : Nat := 4983230072969 + 3 ^ 40 * 7786362 * 2
def baseEnd_7786362 : Nat := 3998146255903570056566179

theorem tailTrace_7786362 : CollatzResearch.WordTrace tailWord_7786362 prefixEnd_7786362 3998146255903570056566179 := by
  unfold tailWord_7786362
  simp only [CollatzResearch.WordTrace]
  refine ⟨70997988254336938400886335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189327968678231835735696893 70997988254336938400886335)
  ·
    refine ⟨106496982381505407601329503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70997988254336938400886335 106496982381505407601329503)
    ·
      refine ⟨159745473572258111401994255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106496982381505407601329503 159745473572258111401994255)
      ·
        refine ⟨239618210358387167102991383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159745473572258111401994255 239618210358387167102991383)
        ·
          refine ⟨359427315537580750654487075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239618210358387167102991383 359427315537580750654487075)
          ·
            refine ⟨539140973306371125981730613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359427315537580750654487075 539140973306371125981730613)
            ·
              refine ⟨50544466247472293060787245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 539140973306371125981730613 50544466247472293060787245)
              ·
                refine ⟨18954174842802109897795217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50544466247472293060787245 18954174842802109897795217)
                ·
                  refine ⟨14215631132101582423346413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18954174842802109897795217 14215631132101582423346413)
                  ·
                    refine ⟨5330861674538093408754905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14215631132101582423346413 5330861674538093408754905)
                    ·
                      refine ⟨3998146255903570056566179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5330861674538093408754905 3998146255903570056566179)
                      ·
                        rfl

theorem cell23_7786362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2].length) (baseStart_7786362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786362 prefixEnd_7786362 := by exact prefixLift 7786362
  have htrace : WordTrace (prefixWord ++ tailWord_7786362) baseStart_7786362 baseEnd_7786362 := by
    simpa [prefixWord, tailWord_7786362, baseEnd_7786362] using wordTrace_append hprefix tailTrace_7786362
  have hstable : (prefixWord ++ tailWord_7786362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786362).length < 2 ^ (prefixWord ++ tailWord_7786362).sum := by decide
  have hdescent : baseEnd_7786362 < baseStart_7786362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786385 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 4, 4]
def baseStart_7786385 : Nat := 118140960795 + 7786385 * 2 ^ 59
def prefixEnd_7786385 : Nat := 4983230072969 + 3 ^ 40 * 7786385 * 2
def baseEnd_7786385 : Nat := 1332719355319541155526191

theorem tailTrace_7786385 : CollatzResearch.WordTrace tailWord_7786385 prefixEnd_7786385 1332719355319541155526191 := by
  unfold tailWord_7786385
  simp only [CollatzResearch.WordTrace]
  refine ⟨283992791896264428531632609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189328527930842952354421739 283992791896264428531632609)
  ·
    refine ⟨212994593922198321398724457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283992791896264428531632609 212994593922198321398724457)
    ·
      refine ⟨159745945441648741049043343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212994593922198321398724457 159745945441648741049043343)
      ·
        refine ⟨239618918162473111573565015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159745945441648741049043343 239618918162473111573565015)
        ·
          refine ⟨359428377243709667360347523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239618918162473111573565015 359428377243709667360347523)
          ·
            refine ⟨539142565865564501040521285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359428377243709667360347523 539142565865564501040521285)
            ·
              refine ⟨101089231099793343945097741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 539142565865564501040521285 101089231099793343945097741)
              ·
                refine ⟨37908461662422503979411653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101089231099793343945097741 37908461662422503979411653)
                ·
                  refine ⟨7107836561704219496139685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37908461662422503979411653 7107836561704219496139685)
                  ·
                    refine ⟨1332719355319541155526191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7107836561704219496139685 1332719355319541155526191)
                    ·
                      rfl

theorem cell23_7786385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_7786385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786385 prefixEnd_7786385 := by exact prefixLift 7786385
  have htrace : WordTrace (prefixWord ++ tailWord_7786385) baseStart_7786385 baseEnd_7786385 := by
    simpa [prefixWord, tailWord_7786385, baseEnd_7786385] using wordTrace_append hprefix tailTrace_7786385
  have hstable : (prefixWord ++ tailWord_7786385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786385).length < 2 ^ (prefixWord ++ tailWord_7786385).sum := by decide
  have hdescent : baseEnd_7786385 < baseStart_7786385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786415 : List Nat := [1, 1, 2, 1, 2, 2, 7, 7]
def baseStart_7786415 : Nat := 118140960795 + 7786415 * 2 ^ 59
def prefixEnd_7786415 : Nat := 4983230072969 + 3 ^ 40 * 7786415 * 2
def baseEnd_7786415 : Nat := 148080498902898457377905

theorem tailTrace_7786415 : CollatzResearch.WordTrace tailWord_7786415 prefixEnd_7786415 148080498902898457377905 := by
  unfold tailWord_7786415
  simp only [CollatzResearch.WordTrace]
  refine ⟨283993886086155743655224699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189329257390770495770149799 283993886086155743655224699)
  ·
    refine ⟨425990829129233615482837049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283993886086155743655224699 425990829129233615482837049)
    ·
      refine ⟨319493121846925211612127787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425990829129233615482837049 319493121846925211612127787)
      ·
        refine ⟨479239682770387817418191681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319493121846925211612127787 479239682770387817418191681)
        ·
          refine ⟨359429762077790863063643761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479239682770387817418191681 359429762077790863063643761)
          ·
            refine ⟨269572321558343147297732821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359429762077790863063643761 269572321558343147297732821)
            ·
              refine ⟨6318101286523667514790613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 269572321558343147297732821 6318101286523667514790613)
              ·
                refine ⟨148080498902898457377905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6318101286523667514790613 148080498902898457377905)
                ·
                  rfl

theorem cell23_7786415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 7].length) (baseStart_7786415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786415 prefixEnd_7786415 := by exact prefixLift 7786415
  have htrace : WordTrace (prefixWord ++ tailWord_7786415) baseStart_7786415 baseEnd_7786415 := by
    simpa [prefixWord, tailWord_7786415, baseEnd_7786415] using wordTrace_append hprefix tailTrace_7786415
  have hstable : (prefixWord ++ tailWord_7786415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786415).length < 2 ^ (prefixWord ++ tailWord_7786415).sum := by decide
  have hdescent : baseEnd_7786415 < baseStart_7786415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786420 : List Nat := [2, 5, 2, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_7786420 : Nat := 118140960795 + 7786420 * 2 ^ 59
def prefixEnd_7786420 : Nat := 4983230072969 + 3 ^ 40 * 7786420 * 2
def baseEnd_7786420 : Nat := 3998176037781530829640913

theorem tailTrace_7786420 : CollatzResearch.WordTrace tailWord_7786420 prefixEnd_7786420 3998176037781530829640913 := by
  unfold tailWord_7786420
  simp only [CollatzResearch.WordTrace]
  refine ⟨141997034225568814754578357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189329378967425086339437809 141997034225568814754578357)
  ·
    refine ⟨13312221958647076383241721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141997034225568814754578357 13312221958647076383241721)
    ·
      refine ⟨9984166468985307287431291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13312221958647076383241721 9984166468985307287431291)
      ·
        refine ⟨14976249703477960931146937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9984166468985307287431291 14976249703477960931146937)
        ·
          refine ⟨11232187277608470698360203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14976249703477960931146937 11232187277608470698360203)
          ·
            refine ⟨16848280916412706047540305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11232187277608470698360203 16848280916412706047540305)
            ·
              refine ⟨12636210687309529535655229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16848280916412706047540305 12636210687309529535655229)
              ·
                refine ⟨4738579007741073575870711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12636210687309529535655229 4738579007741073575870711)
                ·
                  refine ⟨7107868511611610363806067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4738579007741073575870711 7107868511611610363806067)
                  ·
                    refine ⟨10661802767417415545709101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7107868511611610363806067 10661802767417415545709101)
                    ·
                      refine ⟨3998176037781530829640913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10661802767417415545709101 3998176037781530829640913)
                      ·
                        rfl

theorem cell23_7786420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_7786420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786420 prefixEnd_7786420 := by exact prefixLift 7786420
  have htrace : WordTrace (prefixWord ++ tailWord_7786420) baseStart_7786420 baseEnd_7786420 := by
    simpa [prefixWord, tailWord_7786420, baseEnd_7786420] using wordTrace_append hprefix tailTrace_7786420
  have hstable : (prefixWord ++ tailWord_7786420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786420).length < 2 ^ (prefixWord ++ tailWord_7786420).sum := by decide
  have hdescent : baseEnd_7786420 < baseStart_7786420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786429 : List Nat := [1, 4, 1, 2, 3, 2, 1, 3, 1, 2, 3]
def baseStart_7786429 : Nat := 118140960795 + 7786429 * 2 ^ 59
def prefixEnd_7786429 : Nat := 4983230072969 + 3 ^ 40 * 7786429 * 2
def baseEnd_7786429 : Nat := 3998180659107421294428371

theorem tailTrace_7786429 : CollatzResearch.WordTrace tailWord_7786429 prefixEnd_7786429 3998180659107421294428371 := by
  unfold tailWord_7786429
  simp only [CollatzResearch.WordTrace]
  refine ⟨283994396708105024046234341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189329597805403349364156227 283994396708105024046234341)
  ·
    refine ⟨53248949382769692008668939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 283994396708105024046234341 53248949382769692008668939)
    ·
      refine ⟨79873424074154538013003409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53248949382769692008668939 79873424074154538013003409)
      ·
        refine ⟨59905068055615903509752557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79873424074154538013003409 59905068055615903509752557)
        ·
          refine ⟨22464400520855963816157209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59905068055615903509752557 22464400520855963816157209)
          ·
            refine ⟨16848300390641972862117907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22464400520855963816157209 16848300390641972862117907)
            ·
              refine ⟨25272450585962959293176861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16848300390641972862117907 25272450585962959293176861)
              ·
                refine ⟨9477168969736109734941323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25272450585962959293176861 9477168969736109734941323)
                ·
                  refine ⟨14215753454604164602411985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9477168969736109734941323 14215753454604164602411985)
                  ·
                    refine ⟨10661815090953123451808989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14215753454604164602411985 10661815090953123451808989)
                    ·
                      refine ⟨3998180659107421294428371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10661815090953123451808989 3998180659107421294428371)
                      ·
                        rfl

theorem cell23_7786429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_7786429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786429 prefixEnd_7786429 := by exact prefixLift 7786429
  have htrace : WordTrace (prefixWord ++ tailWord_7786429) baseStart_7786429 baseEnd_7786429 := by
    simpa [prefixWord, tailWord_7786429, baseEnd_7786429] using wordTrace_append hprefix tailTrace_7786429
  have hstable : (prefixWord ++ tailWord_7786429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786429).length < 2 ^ (prefixWord ++ tailWord_7786429).sum := by decide
  have hdescent : baseEnd_7786429 < baseStart_7786429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786465 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_7786465 : Nat := 118140960795 + 7786465 * 2 ^ 59
def prefixEnd_7786465 : Nat := 4983230072969 + 3 ^ 40 * 7786465 * 2
def baseEnd_7786465 : Nat := 3998199144410983153578205

theorem tailTrace_7786465 : CollatzResearch.WordTrace tailWord_7786465 prefixEnd_7786465 3998199144410983153578205 := by
  unfold tailWord_7786465
  simp only [CollatzResearch.WordTrace]
  refine ⟨283995709735974602194544849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189330473157316401463029899 283995709735974602194544849)
  ·
    refine ⟨212996782301980951645908637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283995709735974602194544849 212996782301980951645908637)
    ·
      refine ⟨79873793363242856867215739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212996782301980951645908637 79873793363242856867215739)
      ·
        refine ⟨119810690044864285300823609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79873793363242856867215739 119810690044864285300823609)
        ·
          refine ⟨89858017533648213975617707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119810690044864285300823609 89858017533648213975617707)
          ·
            refine ⟨134787026300472320963426561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89858017533648213975617707 134787026300472320963426561)
            ·
              refine ⟨101090269725354240722569921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134787026300472320963426561 101090269725354240722569921)
              ·
                refine ⟨75817702294015680541927441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101090269725354240722569921 75817702294015680541927441)
                ·
                  refine ⟨56863276720511760406445581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75817702294015680541927441 56863276720511760406445581)
                  ·
                    refine ⟨21323728770191910152417093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56863276720511760406445581 21323728770191910152417093)
                    ·
                      refine ⟨3998199144410983153578205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21323728770191910152417093 3998199144410983153578205)
                      ·
                        rfl

theorem cell23_7786465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_7786465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786465 prefixEnd_7786465 := by exact prefixLift 7786465
  have htrace : WordTrace (prefixWord ++ tailWord_7786465) baseStart_7786465 baseEnd_7786465 := by
    simpa [prefixWord, tailWord_7786465, baseEnd_7786465] using wordTrace_append hprefix tailTrace_7786465
  have hstable : (prefixWord ++ tailWord_7786465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786465).length < 2 ^ (prefixWord ++ tailWord_7786465).sum := by decide
  have hdescent : baseEnd_7786465 < baseStart_7786465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786466 : List Nat := [3, 3, 3, 1, 2, 2, 2, 7]
def baseStart_7786466 : Nat := 118140960795 + 7786466 * 2 ^ 59
def prefixEnd_7786466 : Nat := 4983230072969 + 3 ^ 40 * 7786466 * 2
def baseEnd_7786466 : Nat := 148081468810801394432063

theorem tailTrace_7786466 : CollatzResearch.WordTrace tailWord_7786466 prefixEnd_7786466 148081468810801394432063 := by
  unfold tailWord_7786466
  simp only [CollatzResearch.WordTrace]
  refine ⟨70998936552242744841332813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189330497472647319576887501 70998936552242744841332813)
  ·
    refine ⟨26624601207091029315499805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70998936552242744841332813 26624601207091029315499805)
    ·
      refine ⟨9984225452659135993312427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26624601207091029315499805 9984225452659135993312427)
      ·
        refine ⟨14976338178988703989968641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9984225452659135993312427 14976338178988703989968641)
        ·
          refine ⟨11232253634241527992476481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14976338178988703989968641 11232253634241527992476481)
          ·
            refine ⟨8424190225681145994357361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11232253634241527992476481 8424190225681145994357361)
            ·
              refine ⟨6318142669260859495768021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8424190225681145994357361 6318142669260859495768021)
              ·
                refine ⟨148081468810801394432063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6318142669260859495768021 148081468810801394432063)
                ·
                  rfl

theorem cell23_7786466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 7].length) (baseStart_7786466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786466 prefixEnd_7786466 := by exact prefixLift 7786466
  have htrace : WordTrace (prefixWord ++ tailWord_7786466) baseStart_7786466 baseEnd_7786466 := by
    simpa [prefixWord, tailWord_7786466, baseEnd_7786466] using wordTrace_append hprefix tailTrace_7786466
  have hstable : (prefixWord ++ tailWord_7786466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786466).length < 2 ^ (prefixWord ++ tailWord_7786466).sum := by decide
  have hdescent : baseEnd_7786466 < baseStart_7786466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786477 : List Nat := [1, 5, 1, 4, 1, 2, 1, 3, 1, 2, 2]
def baseStart_7786477 : Nat := 118140960795 + 7786477 * 2 ^ 59
def prefixEnd_7786477 : Nat := 4983230072969 + 3 ^ 40 * 7786477 * 2
def baseEnd_7786477 : Nat := 3998205306178837106628151

theorem tailTrace_7786477 : CollatzResearch.WordTrace tailWord_7786477 prefixEnd_7786477 3998205306178837106628151 := by
  unfold tailWord_7786477
  simp only [CollatzResearch.WordTrace]
  refine ⟨283996147411931128243981685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189330764941287418829321123 283996147411931128243981685)
  ·
    refine ⟨26624638819868543272873283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 283996147411931128243981685 26624638819868543272873283)
    ·
      refine ⟨39936958229802814909309925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26624638819868543272873283 39936958229802814909309925)
      ·
        refine ⟨7488179668088027795495611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39936958229802814909309925 7488179668088027795495611)
        ·
          refine ⟨11232269502132041693243417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7488179668088027795495611 11232269502132041693243417)
          ·
            refine ⟨8424202126599031269932563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11232269502132041693243417 8424202126599031269932563)
            ·
              refine ⟨12636303189898546904898845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8424202126599031269932563 12636303189898546904898845)
              ·
                refine ⟨4738613696211955089337067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12636303189898546904898845 4738613696211955089337067)
                ·
                  refine ⟨7107920544317932634005601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4738613696211955089337067 7107920544317932634005601)
                  ·
                    refine ⟨5330940408238449475504201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7107920544317932634005601 5330940408238449475504201)
                    ·
                      refine ⟨3998205306178837106628151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5330940408238449475504201 3998205306178837106628151)
                      ·
                        rfl

theorem cell23_7786477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_7786477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786477 prefixEnd_7786477 := by exact prefixLift 7786477
  have htrace : WordTrace (prefixWord ++ tailWord_7786477) baseStart_7786477 baseEnd_7786477 := by
    simpa [prefixWord, tailWord_7786477, baseEnd_7786477] using wordTrace_append hprefix tailTrace_7786477
  have hstable : (prefixWord ++ tailWord_7786477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786477).length < 2 ^ (prefixWord ++ tailWord_7786477).sum := by decide
  have hdescent : baseEnd_7786477 < baseStart_7786477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786495 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 4]
def baseStart_7786495 : Nat := 118140960795 + 7786495 * 2 ^ 59
def prefixEnd_7786495 : Nat := 4983230072969 + 3 ^ 40 * 7786495 * 2
def baseEnd_7786495 : Nat := 3998214548830618036203067

theorem tailTrace_7786495 : CollatzResearch.WordTrace tailWord_7786495 prefixEnd_7786495 3998214548830618036203067 := by
  unfold tailWord_7786495
  simp only [CollatzResearch.WordTrace]
  refine ⟨283996803925865917318136939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189331202617243944878757959 283996803925865917318136939)
  ·
    refine ⟨425995205888798875977205409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283996803925865917318136939 425995205888798875977205409)
    ·
      refine ⟨319496404416599156982904057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425995205888798875977205409 319496404416599156982904057)
      ·
        refine ⟨239622303312449367737178043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319496404416599156982904057 239622303312449367737178043)
        ·
          refine ⟨359433454968674051605767065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239622303312449367737178043 359433454968674051605767065)
          ·
            refine ⟨269575091226505538704325299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359433454968674051605767065 269575091226505538704325299)
            ·
              refine ⟨404362636839758308056487949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269575091226505538704325299 404362636839758308056487949)
              ·
                refine ⟨151635988814909365521182981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404362636839758308056487949 151635988814909365521182981)
                ·
                  refine ⟨28431747902795506035221809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151635988814909365521182981 28431747902795506035221809)
                  ·
                    refine ⟨21323810927096629526416357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28431747902795506035221809 21323810927096629526416357)
                    ·
                      refine ⟨3998214548830618036203067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21323810927096629526416357 3998214548830618036203067)
                      ·
                        rfl

theorem cell23_7786495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_7786495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786495 prefixEnd_7786495 := by exact prefixLift 7786495
  have htrace : WordTrace (prefixWord ++ tailWord_7786495) baseStart_7786495 baseEnd_7786495 := by
    simpa [prefixWord, tailWord_7786495, baseEnd_7786495] using wordTrace_append hprefix tailTrace_7786495
  have hstable : (prefixWord ++ tailWord_7786495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786495).length < 2 ^ (prefixWord ++ tailWord_7786495).sum := by decide
  have hdescent : baseEnd_7786495 < baseStart_7786495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786565 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 2, 8]
def baseStart_7786565 : Nat := 118140960795 + 7786565 * 2 ^ 59
def prefixEnd_7786565 : Nat := 4983230072969 + 3 ^ 40 * 7786565 * 2
def baseEnd_7786565 : Nat := 1332750164158810920775915

theorem tailTrace_7786565 : CollatzResearch.WordTrace tailWord_7786565 prefixEnd_7786565 1332750164158810920775915 := by
  unfold tailWord_7786565
  simp only [CollatzResearch.WordTrace]
  refine ⟨283999357035612319273185149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189332904690408212848790099 283999357035612319273185149)
  ·
    refine ⟨106499758888354619727444431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283999357035612319273185149 106499758888354619727444431)
    ·
      refine ⟨159749638332531929591166647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106499758888354619727444431 159749638332531929591166647)
      ·
        refine ⟨239624457498797894386749971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159749638332531929591166647 239624457498797894386749971)
        ·
          refine ⟨359436686248196841580124957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239624457498797894386749971 359436686248196841580124957)
          ·
            refine ⟨134788757343073815592546859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359436686248196841580124957 134788757343073815592546859)
            ·
              refine ⟨202183136014610723388820289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134788757343073815592546859 202183136014610723388820289)
              ·
                refine ⟨151637352010958042541615217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202183136014610723388820289 151637352010958042541615217)
                ·
                  refine ⟨113728014008218531906211413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151637352010958042541615217 113728014008218531906211413)
                  ·
                    refine ⟨1332750164158810920775915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113728014008218531906211413 1332750164158810920775915)
                    ·
                      rfl

theorem cell23_7786565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_7786565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786565 prefixEnd_7786565 := by exact prefixLift 7786565
  have htrace : WordTrace (prefixWord ++ tailWord_7786565) baseStart_7786565 baseEnd_7786565 := by
    simpa [prefixWord, tailWord_7786565, baseEnd_7786565] using wordTrace_append hprefix tailTrace_7786565
  have hstable : (prefixWord ++ tailWord_7786565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786565).length < 2 ^ (prefixWord ++ tailWord_7786565).sum := by decide
  have hdescent : baseEnd_7786565 < baseStart_7786565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786566 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_7786566 : Nat := 118140960795 + 7786566 * 2 ^ 59
def prefixEnd_7786566 : Nat := 4983230072969 + 3 ^ 40 * 7786566 * 2
def baseEnd_7786566 : Nat := 3998251005957087258415241

theorem tailTrace_7786566 : CollatzResearch.WordTrace tailWord_7786566 prefixEnd_7786566 3998251005957087258415241 := by
  unfold tailWord_7786566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8874981047144021763874111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 189332929005739130962647701 8874981047144021763874111)
  ·
    refine ⟨13312471570716032645811167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8874981047144021763874111 13312471570716032645811167)
    ·
      refine ⟨19968707356074048968716751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13312471570716032645811167 19968707356074048968716751)
      ·
        refine ⟨29953061034111073453075127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19968707356074048968716751 29953061034111073453075127)
        ·
          refine ⟨44929591551166610179612691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29953061034111073453075127 44929591551166610179612691)
          ·
            refine ⟨67394387326749915269419037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44929591551166610179612691 67394387326749915269419037)
            ·
              refine ⟨25272895247531218226032139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67394387326749915269419037 25272895247531218226032139)
              ·
                refine ⟨37909342871296827339048209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25272895247531218226032139 37909342871296827339048209)
                ·
                  refine ⟨28432007153472620504286157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37909342871296827339048209 28432007153472620504286157)
                  ·
                    refine ⟨10662002682552232689107309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28432007153472620504286157 10662002682552232689107309)
                    ·
                      refine ⟨3998251005957087258415241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10662002682552232689107309 3998251005957087258415241)
                      ·
                        rfl

theorem cell23_7786566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_7786566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786566 prefixEnd_7786566 := by exact prefixLift 7786566
  have htrace : WordTrace (prefixWord ++ tailWord_7786566) baseStart_7786566 baseEnd_7786566 := by
    simpa [prefixWord, tailWord_7786566, baseEnd_7786566] using wordTrace_append hprefix tailTrace_7786566
  have hstable : (prefixWord ++ tailWord_7786566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786566).length < 2 ^ (prefixWord ++ tailWord_7786566).sum := by decide
  have hdescent : baseEnd_7786566 < baseStart_7786566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786572 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 4, 1, 4]
def baseStart_7786572 : Nat := 118140960795 + 7786572 * 2 ^ 59
def prefixEnd_7786572 : Nat := 4983230072969 + 3 ^ 40 * 7786572 * 2
def baseEnd_7786572 : Nat := 3998254086841014234940213

theorem tailTrace_7786572 : CollatzResearch.WordTrace tailWord_7786572 prefixEnd_7786572 3998254086841014234940213 := by
  unfold tailWord_7786572
  simp only [CollatzResearch.WordTrace]
  refine ⟨141999806173293479734344985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189333074897724639645793313 141999806173293479734344985)
  ·
    refine ⟨106499854629970109800758739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141999806173293479734344985 106499854629970109800758739)
    ·
      refine ⟨159749781944955164701138109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106499854629970109800758739 159749781944955164701138109)
      ·
        refine ⟨59906168229358186762926791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159749781944955164701138109 59906168229358186762926791)
        ·
          refine ⟨89859252344037280144390187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59906168229358186762926791 89859252344037280144390187)
          ·
            refine ⟨134788878516055920216585281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89859252344037280144390187 134788878516055920216585281)
            ·
              refine ⟨101091658887041940162438961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134788878516055920216585281 101091658887041940162438961)
              ·
                refine ⟨75818744165281455121829221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101091658887041940162438961 75818744165281455121829221)
                ·
                  refine ⟨14216014530990272835342979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75818744165281455121829221 14216014530990272835342979)
                  ·
                    refine ⟨21324021796485409253014469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14216014530990272835342979 21324021796485409253014469)
                    ·
                      refine ⟨3998254086841014234940213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21324021796485409253014469 3998254086841014234940213)
                      ·
                        rfl

theorem cell23_7786572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_7786572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786572 prefixEnd_7786572 := by exact prefixLift 7786572
  have htrace : WordTrace (prefixWord ++ tailWord_7786572) baseStart_7786572 baseEnd_7786572 := by
    simpa [prefixWord, tailWord_7786572, baseEnd_7786572] using wordTrace_append hprefix tailTrace_7786572
  have hstable : (prefixWord ++ tailWord_7786572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786572).length < 2 ^ (prefixWord ++ tailWord_7786572).sum := by decide
  have hdescent : baseEnd_7786572 < baseStart_7786572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786575 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 5]
def baseStart_7786575 : Nat := 118140960795 + 7786575 * 2 ^ 59
def prefixEnd_7786575 : Nat := 4983230072969 + 3 ^ 40 * 7786575 * 2
def baseEnd_7786575 : Nat := 3998255627282977723202699

theorem tailTrace_7786575 : CollatzResearch.WordTrace tailWord_7786575 prefixEnd_7786575 3998255627282977723202699 := by
  unfold tailWord_7786575
  simp only [CollatzResearch.WordTrace]
  refine ⟨283999721765576090981049179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189333147843717393987366119 283999721765576090981049179)
  ·
    refine ⟨425999582648364136471573769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 283999721765576090981049179 425999582648364136471573769)
    ·
      refine ⟨319499686986273102353680327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425999582648364136471573769 319499686986273102353680327)
      ·
        refine ⟨479249530479409653530520491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319499686986273102353680327 479249530479409653530520491)
        ·
          refine ⟨718874295719114480295780737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479249530479409653530520491 718874295719114480295780737)
          ·
            refine ⟨539155721789335860221835553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718874295719114480295780737 539155721789335860221835553)
            ·
              refine ⟨404366791342001895166376665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539155721789335860221835553 404366791342001895166376665)
              ·
                refine ⟨303275093506501421374782499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404366791342001895166376665 303275093506501421374782499)
                ·
                  refine ⟨454912640259752132062173749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303275093506501421374782499 454912640259752132062173749)
                  ·
                    refine ⟨42648060024351762380828789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 454912640259752132062173749 42648060024351762380828789)
                    ·
                      refine ⟨3998255627282977723202699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42648060024351762380828789 3998255627282977723202699)
                      ·
                        rfl

theorem cell23_7786575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_7786575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786575 prefixEnd_7786575 := by exact prefixLift 7786575
  have htrace : WordTrace (prefixWord ++ tailWord_7786575) baseStart_7786575 baseEnd_7786575 := by
    simpa [prefixWord, tailWord_7786575, baseEnd_7786575] using wordTrace_append hprefix tailTrace_7786575
  have hstable : (prefixWord ++ tailWord_7786575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786575).length < 2 ^ (prefixWord ++ tailWord_7786575).sum := by decide
  have hdescent : baseEnd_7786575 < baseStart_7786575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786590 : List Nat := [4, 4, 1, 1, 2, 1, 2, 3, 5]
def baseStart_7786590 : Nat := 118140960795 + 7786590 * 2 ^ 59
def prefixEnd_7786590 : Nat := 4983230072969 + 3 ^ 40 * 7786590 * 2
def baseEnd_7786590 : Nat := 444251481054755018279459

theorem tailTrace_7786590 : CollatzResearch.WordTrace tailWord_7786590 prefixEnd_7786590 444251481054755018279459 := by
  unfold tailWord_7786590
  simp only [CollatzResearch.WordTrace]
  refine ⟨35500033607565218567855653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189333512573681165695230149 35500033607565218567855653)
  ·
    refine ⟨6656256301418478481472935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35500033607565218567855653 6656256301418478481472935)
    ·
      refine ⟨9984384452127717722209403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6656256301418478481472935 9984384452127717722209403)
      ·
        refine ⟨14976576678191576583314105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9984384452127717722209403 14976576678191576583314105)
        ·
          refine ⟨11232432508643682437485579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14976576678191576583314105 11232432508643682437485579)
          ·
            refine ⟨16848648762965523656228369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11232432508643682437485579 16848648762965523656228369)
            ·
              refine ⟨12636486572224142742171277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16848648762965523656228369 12636486572224142742171277)
              ·
                refine ⟨4738682464584053528314229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12636486572224142742171277 4738682464584053528314229)
                ·
                  refine ⟨444251481054755018279459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4738682464584053528314229 444251481054755018279459)
                  ·
                    rfl

theorem cell23_7786590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_7786590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786590 prefixEnd_7786590 := by exact prefixLift 7786590
  have htrace : WordTrace (prefixWord ++ tailWord_7786590) baseStart_7786590 baseEnd_7786590 := by
    simpa [prefixWord, tailWord_7786590, baseEnd_7786590] using wordTrace_append hprefix tailTrace_7786590
  have hstable : (prefixWord ++ tailWord_7786590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786590).length < 2 ^ (prefixWord ++ tailWord_7786590).sum := by decide
  have hdescent : baseEnd_7786590 < baseStart_7786590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786649 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 6, 3, 2]
def baseStart_7786649 : Nat := 118140960795 + 7786649 * 2 ^ 59
def prefixEnd_7786649 : Nat := 4983230072969 + 3 ^ 40 * 7786649 * 2
def baseEnd_7786649 : Nat := 3998293624851410433677359

theorem tailTrace_7786649 : CollatzResearch.WordTrace tailWord_7786649 prefixEnd_7786649 3998293624851410433677359 := by
  unfold tailWord_7786649
  simp only [CollatzResearch.WordTrace]
  refine ⟨284002420767308001619243001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189334947178205334412828667 284002420767308001619243001)
  ·
    refine ⟨213001815575481001214432251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284002420767308001619243001 213001815575481001214432251)
    ·
      refine ⟨319502723363221501821648377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213001815575481001214432251 319502723363221501821648377)
      ·
        refine ⟨239627042522416126366236283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319502723363221501821648377 239627042522416126366236283)
        ·
          refine ⟨359440563783624189549354425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239627042522416126366236283 359440563783624189549354425)
          ·
            refine ⟨269580422837718142162015819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359440563783624189549354425 269580422837718142162015819)
            ·
              refine ⟨404370634256577213243023729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269580422837718142162015819 404370634256577213243023729)
              ·
                refine ⟨303277975692432909932267797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404370634256577213243023729 303277975692432909932267797)
                ·
                  refine ⟨14216155110582792653075053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 303277975692432909932267797 14216155110582792653075053)
                  ·
                    refine ⟨5331058166468547244903145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14216155110582792653075053 5331058166468547244903145)
                    ·
                      refine ⟨3998293624851410433677359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5331058166468547244903145 3998293624851410433677359)
                      ·
                        rfl

theorem cell23_7786649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 3, 2].length) (baseStart_7786649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786649 prefixEnd_7786649 := by exact prefixLift 7786649
  have htrace : WordTrace (prefixWord ++ tailWord_7786649) baseStart_7786649 baseEnd_7786649 := by
    simpa [prefixWord, tailWord_7786649, baseEnd_7786649] using wordTrace_append hprefix tailTrace_7786649
  have hstable : (prefixWord ++ tailWord_7786649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786649).length < 2 ^ (prefixWord ++ tailWord_7786649).sum := by decide
  have hdescent : baseEnd_7786649 < baseStart_7786649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786650 : List Nat := [3, 1, 1, 5, 2, 2, 1, 3, 1, 4]
def baseStart_7786650 : Nat := 118140960795 + 7786650 * 2 ^ 59
def prefixEnd_7786650 : Nat := 4983230072969 + 3 ^ 40 * 7786650 * 2
def baseEnd_7786650 : Nat := 1332764712777354976588285

theorem tailTrace_7786650 : CollatzResearch.WordTrace tailWord_7786650 prefixEnd_7786650 1332764712777354976588285 := by
  unfold tailWord_7786650
  simp only [CollatzResearch.WordTrace]
  refine ⟨71000614310076094697507351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189334971493536252526686269 71000614310076094697507351)
  ·
    refine ⟨106500921465114142046261027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71000614310076094697507351 106500921465114142046261027)
    ·
      refine ⟨159751382197671213069391541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106500921465114142046261027 159751382197671213069391541)
      ·
        refine ⟨14976692081031676225255457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159751382197671213069391541 14976692081031676225255457)
        ·
          refine ⟨11232519060773757168941593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14976692081031676225255457 11232519060773757168941593)
          ·
            refine ⟨8424389295580317876706195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11232519060773757168941593 8424389295580317876706195)
            ·
              refine ⟨12636583943370476815059293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8424389295580317876706195 12636583943370476815059293)
              ·
                refine ⟨4738718978763928805647235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12636583943370476815059293 4738718978763928805647235)
                ·
                  refine ⟨7108078468145893208470853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4738718978763928805647235 7108078468145893208470853)
                  ·
                    refine ⟨1332764712777354976588285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7108078468145893208470853 1332764712777354976588285)
                    ·
                      rfl

theorem cell23_7786650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 1, 4].length) (baseStart_7786650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786650 prefixEnd_7786650 := by exact prefixLift 7786650
  have htrace : WordTrace (prefixWord ++ tailWord_7786650) baseStart_7786650 baseEnd_7786650 := by
    simpa [prefixWord, tailWord_7786650, baseEnd_7786650] using wordTrace_append hprefix tailTrace_7786650
  have hstable : (prefixWord ++ tailWord_7786650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786650).length < 2 ^ (prefixWord ++ tailWord_7786650).sum := by decide
  have hdescent : baseEnd_7786650 < baseStart_7786650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786696 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 5, 2, 2]
def baseStart_7786696 : Nat := 118140960795 + 7786696 * 2 ^ 59
def prefixEnd_7786696 : Nat := 4983230072969 + 3 ^ 40 * 7786696 * 2
def baseEnd_7786696 : Nat := 3998317758442171749789643

theorem tailTrace_7786696 : CollatzResearch.WordTrace tailWord_7786696 prefixEnd_7786696 3998317758442171749789643 := by
  unfold tailWord_7786696
  simp only [CollatzResearch.WordTrace]
  refine ⟨142002067499068864323101971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189336089998758485764135961 142002067499068864323101971)
  ·
    refine ⟨213003101248603296484652957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142002067499068864323101971 213003101248603296484652957)
    ·
      refine ⟨79876162968226236181744859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213003101248603296484652957 79876162968226236181744859)
      ·
        refine ⟨119814244452339354272617289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79876162968226236181744859 119814244452339354272617289)
        ·
          refine ⟨89860683339254515704462967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119814244452339354272617289 89860683339254515704462967)
          ·
            refine ⟨134791025008881773556694451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89860683339254515704462967 134791025008881773556694451)
            ·
              refine ⟨202186537513322660335041677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134791025008881773556694451 202186537513322660335041677)
              ·
                refine ⟨75819951567495997625640629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202186537513322660335041677 75819951567495997625640629)
                ·
                  refine ⟨7108120459452749777403809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75819951567495997625640629 7108120459452749777403809)
                  ·
                    refine ⟨5331090344589562333052857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7108120459452749777403809 5331090344589562333052857)
                    ·
                      refine ⟨3998317758442171749789643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5331090344589562333052857 3998317758442171749789643)
                      ·
                        rfl

theorem cell23_7786696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_7786696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786696 prefixEnd_7786696 := by exact prefixLift 7786696
  have htrace : WordTrace (prefixWord ++ tailWord_7786696) baseStart_7786696 baseEnd_7786696 := by
    simpa [prefixWord, tailWord_7786696, baseEnd_7786696] using wordTrace_append hprefix tailTrace_7786696
  have hstable : (prefixWord ++ tailWord_7786696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786696).length < 2 ^ (prefixWord ++ tailWord_7786696).sum := by decide
  have hdescent : baseEnd_7786696 < baseStart_7786696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786699 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 3]
def baseStart_7786699 : Nat := 118140960795 + 7786699 * 2 ^ 59
def prefixEnd_7786699 : Nat := 4983230072969 + 3 ^ 40 * 7786699 * 2
def baseEnd_7786699 : Nat := 3998319298884135238052129

theorem tailTrace_7786699 : CollatzResearch.WordTrace tailWord_7786699 prefixEnd_7786699 3998319298884135238052129 := by
  unfold tailWord_7786699
  simp only [CollatzResearch.WordTrace]
  refine ⟨284004244417126860158563151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189336162944751240105708767 284004244417126860158563151)
  ·
    refine ⟨426006366625690290237844727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284004244417126860158563151 426006366625690290237844727)
    ·
      refine ⟨639009549938535435356767091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426006366625690290237844727 639009549938535435356767091)
      ·
        refine ⟨958514324907803153035150637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639009549938535435356767091 958514324907803153035150637)
        ·
          refine ⟨359442871840426182388181489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 958514324907803153035150637 359442871840426182388181489)
          ·
            refine ⟨269582153880319636791136117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359442871840426182388181489 269582153880319636791136117)
            ·
              refine ⟨25273326926279965949169011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269582153880319636791136117 25273326926279965949169011)
              ·
                refine ⟨37909990389419948923753517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25273326926279965949169011 37909990389419948923753517)
                ·
                  refine ⟨14216246396032480846407569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37909990389419948923753517 14216246396032480846407569)
                  ·
                    refine ⟨10662184797024360634805677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14216246396032480846407569 10662184797024360634805677)
                    ·
                      refine ⟨3998319298884135238052129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10662184797024360634805677 3998319298884135238052129)
                      ·
                        rfl

theorem cell23_7786699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 3].length) (baseStart_7786699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786699 prefixEnd_7786699 := by exact prefixLift 7786699
  have htrace : WordTrace (prefixWord ++ tailWord_7786699) baseStart_7786699 baseEnd_7786699 := by
    simpa [prefixWord, tailWord_7786699, baseEnd_7786699] using wordTrace_append hprefix tailTrace_7786699
  have hstable : (prefixWord ++ tailWord_7786699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786699).length < 2 ^ (prefixWord ++ tailWord_7786699).sum := by decide
  have hdescent : baseEnd_7786699 < baseStart_7786699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786700 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 2, 3, 2]
def baseStart_7786700 : Nat := 118140960795 + 7786700 * 2 ^ 59
def prefixEnd_7786700 : Nat := 4983230072969 + 3 ^ 40 * 7786700 * 2
def baseEnd_7786700 : Nat := 3998319812364789734139625

theorem tailTrace_7786700 : CollatzResearch.WordTrace tailWord_7786700 prefixEnd_7786700 3998319812364789734139625 := by
  unfold tailWord_7786700
  simp only [CollatzResearch.WordTrace]
  refine ⟨142002140445061618664674777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189336187260082158219566369 142002140445061618664674777)
  ·
    refine ⟨106501605333796213998506083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142002140445061618664674777 106501605333796213998506083)
    ·
      refine ⟨159752408000694320997759125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106501605333796213998506083 159752408000694320997759125)
      ·
        refine ⟨7488394125032546296769959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 159752408000694320997759125 7488394125032546296769959)
        ·
          refine ⟨11232591187548819445154939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7488394125032546296769959 11232591187548819445154939)
          ·
            refine ⟨16848886781323229167732409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11232591187548819445154939 16848886781323229167732409)
            ·
              refine ⟨12636665085992421875799307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16848886781323229167732409 12636665085992421875799307)
              ·
                refine ⟨18954997628988632813698961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12636665085992421875799307 18954997628988632813698961)
                ·
                  refine ⟨14216248221741474610274221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18954997628988632813698961 14216248221741474610274221)
                  ·
                    refine ⟨5331093083153052978852833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14216248221741474610274221 5331093083153052978852833)
                    ·
                      refine ⟨3998319812364789734139625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5331093083153052978852833 3998319812364789734139625)
                      ·
                        rfl

theorem cell23_7786700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_7786700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786700 prefixEnd_7786700 := by exact prefixLift 7786700
  have htrace : WordTrace (prefixWord ++ tailWord_7786700) baseStart_7786700 baseEnd_7786700 := by
    simpa [prefixWord, tailWord_7786700, baseEnd_7786700] using wordTrace_append hprefix tailTrace_7786700
  have hstable : (prefixWord ++ tailWord_7786700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786700).length < 2 ^ (prefixWord ++ tailWord_7786700).sum := by decide
  have hdescent : baseEnd_7786700 < baseStart_7786700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786710 : List Nat := [5, 2, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_7786710 : Nat := 118140960795 + 7786710 * 2 ^ 59
def prefixEnd_7786710 : Nat := 4983230072969 + 3 ^ 40 * 7786710 * 2
def baseEnd_7786710 : Nat := 1332774982390444898338193

theorem tailTrace_7786710 : CollatzResearch.WordTrace tailWord_7786710 prefixEnd_7786710 1332774982390444898338193 := by
  unfold tailWord_7786710
  simp only [CollatzResearch.WordTrace]
  refine ⟨17750290351255438064825849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189336430413391339358142389 17750290351255438064825849)
  ·
    refine ⟨13312717763441578548619387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17750290351255438064825849 13312717763441578548619387)
    ·
      refine ⟨19969076645162367822929081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13312717763441578548619387 19969076645162367822929081)
      ·
        refine ⟨14976807483871775867196811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19969076645162367822929081 14976807483871775867196811)
        ·
          refine ⟨22465211225807663800795217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14976807483871775867196811 22465211225807663800795217)
          ·
            refine ⟨16848908419355747850596413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22465211225807663800795217 16848908419355747850596413)
            ·
              refine ⟨6318340657258405443973655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16848908419355747850596413 6318340657258405443973655)
              ·
                refine ⟨9477510985887608165960483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6318340657258405443973655 9477510985887608165960483)
                ·
                  refine ⟨14216266478831412248940725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9477510985887608165960483 14216266478831412248940725)
                  ·
                    refine ⟨1332774982390444898338193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14216266478831412248940725 1332774982390444898338193)
                    ·
                      rfl

theorem cell23_7786710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_7786710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786710 prefixEnd_7786710 := by exact prefixLift 7786710
  have htrace : WordTrace (prefixWord ++ tailWord_7786710) baseStart_7786710 baseEnd_7786710 := by
    simpa [prefixWord, tailWord_7786710, baseEnd_7786710] using wordTrace_append hprefix tailTrace_7786710
  have hstable : (prefixWord ++ tailWord_7786710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786710).length < 2 ^ (prefixWord ++ tailWord_7786710).sum := by decide
  have hdescent : baseEnd_7786710 < baseStart_7786710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786730 : List Nat := [3, 1, 3, 1, 1, 2, 3, 4, 1, 2, 2]
def baseStart_7786730 : Nat := 118140960795 + 7786730 * 2 ^ 59
def prefixEnd_7786730 : Nat := 4983230072969 + 3 ^ 40 * 7786730 * 2
def baseEnd_7786730 : Nat := 3998335216784424616764487

theorem tailTrace_7786730 : CollatzResearch.WordTrace tailWord_7786730 prefixEnd_7786730 3998335216784424616764487 := by
  unfold tailWord_7786730
  simp only [CollatzResearch.WordTrace]
  refine ⟨71001343770003638113235411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189336916720009701635294429 71001343770003638113235411)
  ·
    refine ⟨106502015655005457169853117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71001343770003638113235411 106502015655005457169853117)
    ·
      refine ⟨39938255870627046438694919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106502015655005457169853117 39938255870627046438694919)
      ·
        refine ⟨59907383805940569658042379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39938255870627046438694919 59907383805940569658042379)
        ·
          refine ⟨89861075708910854487063569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59907383805940569658042379 89861075708910854487063569)
          ·
            refine ⟨67395806781683140865297677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89861075708910854487063569 67395806781683140865297677)
            ·
              refine ⟨25273427543131177824486629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67395806781683140865297677 25273427543131177824486629)
              ·
                refine ⟨4738767664337095842091243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25273427543131177824486629 4738767664337095842091243)
                ·
                  refine ⟨7108151496505643763136865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4738767664337095842091243 7108151496505643763136865)
                  ·
                    refine ⟨5331113622379232822352649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7108151496505643763136865 5331113622379232822352649)
                    ·
                      refine ⟨3998335216784424616764487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5331113622379232822352649 3998335216784424616764487)
                      ·
                        rfl

theorem cell23_7786730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_7786730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786730 prefixEnd_7786730 := by exact prefixLift 7786730
  have htrace : WordTrace (prefixWord ++ tailWord_7786730) baseStart_7786730 baseEnd_7786730 := by
    simpa [prefixWord, tailWord_7786730, baseEnd_7786730] using wordTrace_append hprefix tailTrace_7786730
  have hstable : (prefixWord ++ tailWord_7786730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786730).length < 2 ^ (prefixWord ++ tailWord_7786730).sum := by decide
  have hdescent : baseEnd_7786730 < baseStart_7786730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786732 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 1, 9]
def baseStart_7786732 : Nat := 118140960795 + 7786732 * 2 ^ 59
def prefixEnd_7786732 : Nat := 4983230072969 + 3 ^ 40 * 7786732 * 2
def baseEnd_7786732 : Nat := 1332778747915244536313159

theorem tailTrace_7786732 : CollatzResearch.WordTrace tailWord_7786732 prefixEnd_7786732 1332778747915244536313159 := by
  unfold tailWord_7786732
  simp only [CollatzResearch.WordTrace]
  refine ⟨142002724013003653397257225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189336965350671537863009633 142002724013003653397257225)
  ·
    refine ⟨106502043009752740047942919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142002724013003653397257225 106502043009752740047942919)
    ·
      refine ⟨159753064514629110071914379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106502043009752740047942919 159753064514629110071914379)
      ·
        refine ⟨239629596771943665107871569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159753064514629110071914379 239629596771943665107871569)
        ·
          refine ⟨179722197578957748830903677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239629596771943665107871569 179722197578957748830903677)
          ·
            refine ⟨67395824092109155811588879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179722197578957748830903677 67395824092109155811588879)
            ·
              refine ⟨101093736138163733717383319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67395824092109155811588879 101093736138163733717383319)
              ·
                refine ⟨151640604207245600576074979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101093736138163733717383319 151640604207245600576074979)
                ·
                  refine ⟨227460906310868400864112469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151640604207245600576074979 227460906310868400864112469)
                  ·
                    refine ⟨1332778747915244536313159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 227460906310868400864112469 1332778747915244536313159)
                    ·
                      rfl

theorem cell23_7786732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_7786732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786732 prefixEnd_7786732 := by exact prefixLift 7786732
  have htrace : WordTrace (prefixWord ++ tailWord_7786732) baseStart_7786732 baseEnd_7786732 := by
    simpa [prefixWord, tailWord_7786732, baseEnd_7786732] using wordTrace_append hprefix tailTrace_7786732
  have hstable : (prefixWord ++ tailWord_7786732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786732).length < 2 ^ (prefixWord ++ tailWord_7786732).sum := by decide
  have hdescent : baseEnd_7786732 < baseStart_7786732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786746 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3]
def baseStart_7786746 : Nat := 118140960795 + 7786746 * 2 ^ 59
def prefixEnd_7786746 : Nat := 4983230072969 + 3 ^ 40 * 7786746 * 2
def baseEnd_7786746 : Nat := 3998343432474896554164413

theorem tailTrace_7786746 : CollatzResearch.WordTrace tailWord_7786746 prefixEnd_7786746 3998343432474896554164413 := by
  unfold tailWord_7786746
  simp only [CollatzResearch.WordTrace]
  refine ⟨71001489661989146796381023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189337305765304391457016061 71001489661989146796381023)
  ·
    refine ⟨106502234492983720194571535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71001489661989146796381023 106502234492983720194571535)
    ·
      refine ⟨159753351739475580291857303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106502234492983720194571535 159753351739475580291857303)
      ·
        refine ⟨239630027609213370437785955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159753351739475580291857303 239630027609213370437785955)
        ·
          refine ⟨359445041413820055656678933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239630027609213370437785955 359445041413820055656678933)
          ·
            refine ⟨16848986316272815108906825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 359445041413820055656678933 16848986316272815108906825)
            ·
              refine ⟨12636739737204611331680119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16848986316272815108906825 12636739737204611331680119)
              ·
                refine ⟨18955109605806916997520179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12636739737204611331680119 18955109605806916997520179)
                ·
                  refine ⟨28432664408710375496280269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18955109605806916997520179 28432664408710375496280269)
                  ·
                    refine ⟨10662249153266390811105101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28432664408710375496280269 10662249153266390811105101)
                    ·
                      refine ⟨3998343432474896554164413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10662249153266390811105101 3998343432474896554164413)
                      ·
                        rfl

theorem cell23_7786746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_7786746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786746 prefixEnd_7786746 := by exact prefixLift 7786746
  have htrace : WordTrace (prefixWord ++ tailWord_7786746) baseStart_7786746 baseEnd_7786746 := by
    simpa [prefixWord, tailWord_7786746, baseEnd_7786746] using wordTrace_append hprefix tailTrace_7786746
  have hstable : (prefixWord ++ tailWord_7786746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786746).length < 2 ^ (prefixWord ++ tailWord_7786746).sum := by decide
  have hdescent : baseEnd_7786746 < baseStart_7786746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786797 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_7786797 : Nat := 118140960795 + 7786797 * 2 ^ 59
def prefixEnd_7786797 : Nat := 4983230072969 + 3 ^ 40 * 7786797 * 2
def baseEnd_7786797 : Nat := 3998369619988275854626679

theorem tailTrace_7786797 : CollatzResearch.WordTrace tailWord_7786797 prefixEnd_7786797 3998369619988275854626679 := by
  unfold tailWord_7786797
  simp only [CollatzResearch.WordTrace]
  refine ⟨284007818770771822895630645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189338545847181215263753763 284007818770771822895630645)
  ·
    refine ⟨26625733009759858396465373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 284007818770771822895630645 26625733009759858396465373)
    ·
      refine ⟨9984649878659946898674515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26625733009759858396465373 9984649878659946898674515)
      ·
        refine ⟨14976974817989920348011773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9984649878659946898674515 14976974817989920348011773)
        ·
          refine ⟨5616365556746220130504415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14976974817989920348011773 5616365556746220130504415)
          ·
            refine ⟨8424548335119330195756623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5616365556746220130504415 8424548335119330195756623)
            ·
              refine ⟨12636822502678995293634935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8424548335119330195756623 12636822502678995293634935)
              ·
                refine ⟨18955233754018492940452403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12636822502678995293634935 18955233754018492940452403)
                ·
                  refine ⟨28432850631027739410678605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18955233754018492940452403 28432850631027739410678605)
                  ·
                    refine ⟨10662318986635402279004477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28432850631027739410678605 10662318986635402279004477)
                    ·
                      refine ⟨3998369619988275854626679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10662318986635402279004477 3998369619988275854626679)
                      ·
                        rfl

theorem cell23_7786797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_7786797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786797 prefixEnd_7786797 := by exact prefixLift 7786797
  have htrace : WordTrace (prefixWord ++ tailWord_7786797) baseStart_7786797 baseEnd_7786797 := by
    simpa [prefixWord, tailWord_7786797, baseEnd_7786797] using wordTrace_append hprefix tailTrace_7786797
  have hstable : (prefixWord ++ tailWord_7786797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786797).length < 2 ^ (prefixWord ++ tailWord_7786797).sum := by decide
  have hdescent : baseEnd_7786797 < baseStart_7786797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786799 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 4]
def baseStart_7786799 : Nat := 118140960795 + 7786799 * 2 ^ 59
def prefixEnd_7786799 : Nat := 4983230072969 + 3 ^ 40 * 7786799 * 2
def baseEnd_7786799 : Nat := 3998370646949584846801669

theorem tailTrace_7786799 : CollatzResearch.WordTrace tailWord_7786799 prefixEnd_7786799 3998370646949584846801669 := by
  unfold tailWord_7786799
  simp only [CollatzResearch.WordTrace]
  refine ⟨284007891716764577237203451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189338594477843051491468967 284007891716764577237203451)
  ·
    refine ⟨426011837575146865855805177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284007891716764577237203451 426011837575146865855805177)
    ·
      refine ⟨319508878181360149391853883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426011837575146865855805177 319508878181360149391853883)
      ·
        refine ⟨479263317272040224087780825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319508878181360149391853883 479263317272040224087780825)
        ·
          refine ⟨359447487954030168065835619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479263317272040224087780825 359447487954030168065835619)
          ·
            refine ⟨539171231931045252098753429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359447487954030168065835619 539171231931045252098753429)
            ·
              refine ⟨25273651496767746192129067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 539171231931045252098753429 25273651496767746192129067)
              ·
                refine ⟨37910477245151619288193601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25273651496767746192129067 37910477245151619288193601)
                ·
                  refine ⟨28432857933863714466145201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37910477245151619288193601 28432857933863714466145201)
                  ·
                    refine ⟨21324643450397785849608901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28432857933863714466145201 21324643450397785849608901)
                    ·
                      refine ⟨3998370646949584846801669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21324643450397785849608901 3998370646949584846801669)
                      ·
                        rfl

theorem cell23_7786799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_7786799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786799 prefixEnd_7786799 := by exact prefixLift 7786799
  have htrace : WordTrace (prefixWord ++ tailWord_7786799) baseStart_7786799 baseEnd_7786799 := by
    simpa [prefixWord, tailWord_7786799, baseEnd_7786799] using wordTrace_append hprefix tailTrace_7786799
  have hstable : (prefixWord ++ tailWord_7786799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786799).length < 2 ^ (prefixWord ++ tailWord_7786799).sum := by decide
  have hdescent : baseEnd_7786799 < baseStart_7786799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786819 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 3]
def baseStart_7786819 : Nat := 118140960795 + 7786819 * 2 ^ 59
def prefixEnd_7786819 : Nat := 4983230072969 + 3 ^ 40 * 7786819 * 2
def baseEnd_7786819 : Nat := 3998380916562674768551577

theorem tailTrace_7786819 : CollatzResearch.WordTrace tailWord_7786819 prefixEnd_7786819 3998380916562674768551577 := by
  unfold tailWord_7786819
  simp only [CollatzResearch.WordTrace]
  refine ⟨284008621176692120652931511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189339080784461413768621007 284008621176692120652931511)
  ·
    refine ⟨426012931765038180979397267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284008621176692120652931511 426012931765038180979397267)
    ·
      refine ⟨639019397647557271469095901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426012931765038180979397267 639019397647557271469095901)
      ·
        refine ⟨239632274117833976800910963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 639019397647557271469095901 239632274117833976800910963)
        ·
          refine ⟨359448411176750965201366445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239632274117833976800910963 359448411176750965201366445)
          ·
            refine ⟨134793154191281611950512417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359448411176750965201366445 134793154191281611950512417)
            ·
              refine ⟨101094865643461208962884313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134793154191281611950512417 101094865643461208962884313)
              ·
                refine ⟨75821149232595906722163235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101094865643461208962884313 75821149232595906722163235)
                ·
                  refine ⟨113731723848893860083244853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75821149232595906722163235 113731723848893860083244853)
                  ·
                    refine ⟨10662349110833799382804205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113731723848893860083244853 10662349110833799382804205)
                    ·
                      refine ⟨3998380916562674768551577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10662349110833799382804205 3998380916562674768551577)
                      ·
                        rfl

theorem cell23_7786819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_7786819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786819 prefixEnd_7786819 := by exact prefixLift 7786819
  have htrace : WordTrace (prefixWord ++ tailWord_7786819) baseStart_7786819 baseEnd_7786819 := by
    simpa [prefixWord, tailWord_7786819, baseEnd_7786819] using wordTrace_append hprefix tailTrace_7786819
  have hstable : (prefixWord ++ tailWord_7786819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786819).length < 2 ^ (prefixWord ++ tailWord_7786819).sum := by decide
  have hdescent : baseEnd_7786819 < baseStart_7786819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786876 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 3, 6, 2]
def baseStart_7786876 : Nat := 118140960795 + 7786876 * 2 ^ 59
def prefixEnd_7786876 : Nat := 4983230072969 + 3 ^ 40 * 7786876 * 2
def baseEnd_7786876 : Nat := 3998410184959981045538815

theorem tailTrace_7786876 : CollatzResearch.WordTrace tailWord_7786876 prefixEnd_7786876 3998410184959981045538815 := by
  unfold tailWord_7786876
  simp only [CollatzResearch.WordTrace]
  refine ⟨142005350068742809693878241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189340466758323746258504321 142005350068742809693878241)
  ·
    refine ⟨106504012551557107270408681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142005350068742809693878241 106504012551557107270408681)
    ·
      refine ⟨79878009413667830452806511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106504012551557107270408681 79878009413667830452806511)
      ·
        refine ⟨119817014120501745679209767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79878009413667830452806511 119817014120501745679209767)
        ·
          refine ⟨179725521180752618518814651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119817014120501745679209767 179725521180752618518814651)
          ·
            refine ⟨269588281771128927778221977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179725521180752618518814651 269588281771128927778221977)
            ·
              refine ⟨202191211328346695833666483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269588281771128927778221977 202191211328346695833666483)
              ·
                refine ⟨303286816992520043750499725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202191211328346695833666483 303286816992520043750499725)
                ·
                  refine ⟨113732556372195016406437397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303286816992520043750499725 113732556372195016406437397)
                  ·
                    refine ⟨5331213579946641394051753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113732556372195016406437397 5331213579946641394051753)
                    ·
                      refine ⟨3998410184959981045538815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5331213579946641394051753 3998410184959981045538815)
                      ·
                        rfl

theorem cell23_7786876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_7786876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786876 prefixEnd_7786876 := by exact prefixLift 7786876
  have htrace : WordTrace (prefixWord ++ tailWord_7786876) baseStart_7786876 baseEnd_7786876 := by
    simpa [prefixWord, tailWord_7786876, baseEnd_7786876] using wordTrace_append hprefix tailTrace_7786876
  have hstable : (prefixWord ++ tailWord_7786876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786876).length < 2 ^ (prefixWord ++ tailWord_7786876).sum := by decide
  have hdescent : baseEnd_7786876 < baseStart_7786876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786910 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_7786910 : Nat := 118140960795 + 7786910 * 2 ^ 59
def prefixEnd_7786910 : Nat := 4983230072969 + 3 ^ 40 * 7786910 * 2
def baseEnd_7786910 : Nat := 3998427643302233912513659

theorem tailTrace_7786910 : CollatzResearch.WordTrace tailWord_7786910 prefixEnd_7786910 3998427643302233912513659 := by
  unfold tailWord_7786910
  simp only [CollatzResearch.WordTrace]
  refine ⟨35501492527420305399311773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189341293479574962129662789 35501492527420305399311773)
  ·
    refine ⟨13313059697782614524741915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35501492527420305399311773 13313059697782614524741915)
    ·
      refine ⟨19969589546673921787112873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13313059697782614524741915 19969589546673921787112873)
      ·
        refine ⟨14977192160005441340334655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19969589546673921787112873 14977192160005441340334655)
        ·
          refine ⟨22465788240008162010501983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14977192160005441340334655 22465788240008162010501983)
          ·
            refine ⟨33698682360012243015752975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22465788240008162010501983 33698682360012243015752975)
            ·
              refine ⟨50548023540018364523629463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33698682360012243015752975 50548023540018364523629463)
              ·
                refine ⟨75822035310027546785444195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50548023540018364523629463 75822035310027546785444195)
                ·
                  refine ⟨113733052965041320178166293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75822035310027546785444195 113733052965041320178166293)
                  ·
                    refine ⟨5331236857736311883351545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113733052965041320178166293 5331236857736311883351545)
                    ·
                      refine ⟨3998427643302233912513659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5331236857736311883351545 3998427643302233912513659)
                      ·
                        rfl

theorem cell23_7786910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_7786910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786910 prefixEnd_7786910 := by exact prefixLift 7786910
  have htrace : WordTrace (prefixWord ++ tailWord_7786910) baseStart_7786910 baseEnd_7786910 := by
    simpa [prefixWord, tailWord_7786910, baseEnd_7786910] using wordTrace_append hprefix tailTrace_7786910
  have hstable : (prefixWord ++ tailWord_7786910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786910).length < 2 ^ (prefixWord ++ tailWord_7786910).sum := by decide
  have hdescent : baseEnd_7786910 < baseStart_7786910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786916 : List Nat := [2, 3, 1, 2, 1, 1, 4, 3, 6]
def baseStart_7786916 : Nat := 118140960795 + 7786916 * 2 ^ 59
def prefixEnd_7786916 : Nat := 4983230072969 + 3 ^ 40 * 7786916 * 2
def baseEnd_7786916 : Nat := 444270080465128987670959

theorem tailTrace_7786916 : CollatzResearch.WordTrace tailWord_7786916 prefixEnd_7786916 444270080465128987670959 := by
  unfold tailWord_7786916
  simp only [CollatzResearch.WordTrace]
  refine ⟨142006079528670353109606301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189341439371560470812808401 142006079528670353109606301)
  ·
    refine ⟨53252279823251382416102363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142006079528670353109606301 53252279823251382416102363)
    ·
      refine ⟨79878419734877073624153545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53252279823251382416102363 79878419734877073624153545)
      ·
        refine ⟨59908814801157805218115159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79878419734877073624153545 59908814801157805218115159)
        ·
          refine ⟨89863222201736707827172739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59908814801157805218115159 89863222201736707827172739)
          ·
            refine ⟨134794833302605061740759109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89863222201736707827172739 134794833302605061740759109)
            ·
              refine ⟨25274031244238449076392333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134794833302605061740759109 25274031244238449076392333)
              ·
                refine ⟨9477761716589418403647125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25274031244238449076392333 9477761716589418403647125)
                ·
                  refine ⟨444270080465128987670959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9477761716589418403647125 444270080465128987670959)
                  ·
                    rfl

theorem cell23_7786916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_7786916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786916 prefixEnd_7786916 := by exact prefixLift 7786916
  have htrace : WordTrace (prefixWord ++ tailWord_7786916) baseStart_7786916 baseEnd_7786916 := by
    simpa [prefixWord, tailWord_7786916, baseEnd_7786916] using wordTrace_append hprefix tailTrace_7786916
  have hstable : (prefixWord ++ tailWord_7786916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786916).length < 2 ^ (prefixWord ++ tailWord_7786916).sum := by decide
  have hdescent : baseEnd_7786916 < baseStart_7786916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786920 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 3, 4]
def baseStart_7786920 : Nat := 118140960795 + 7786920 * 2 ^ 59
def prefixEnd_7786920 : Nat := 4983230072969 + 3 ^ 40 * 7786920 * 2
def baseEnd_7786920 : Nat := 1332810926036259624462871

theorem tailTrace_7786920 : CollatzResearch.WordTrace tailWord_7786920 prefixEnd_7786920 1332810926036259624462871 := by
  unfold tailWord_7786920
  simp only [CollatzResearch.WordTrace]
  refine ⟨142006152474663107451179107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189341536632884143268238809 142006152474663107451179107)
  ·
    refine ⟨213009228711994661176768661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142006152474663107451179107 213009228711994661176768661)
    ·
      refine ⟨9984807595874749742661031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 213009228711994661176768661 9984807595874749742661031)
      ·
        refine ⟨14977211393812124613991547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9984807595874749742661031 14977211393812124613991547)
        ·
          refine ⟨22465817090718186920987321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14977211393812124613991547 22465817090718186920987321)
          ·
            refine ⟨16849362818038640190740491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22465817090718186920987321 16849362818038640190740491)
            ·
              refine ⟨25274044227057960286110737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16849362818038640190740491 25274044227057960286110737)
              ·
                refine ⟨18955533170293470214583053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25274044227057960286110737 18955533170293470214583053)
                ·
                  refine ⟨7108324938860051330468645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18955533170293470214583053 7108324938860051330468645)
                  ·
                    refine ⟨1332810926036259624462871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7108324938860051330468645 1332810926036259624462871)
                    ·
                      rfl

theorem cell23_7786920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_7786920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786920 prefixEnd_7786920 := by exact prefixLift 7786920
  have htrace : WordTrace (prefixWord ++ tailWord_7786920) baseStart_7786920 baseEnd_7786920 := by
    simpa [prefixWord, tailWord_7786920, baseEnd_7786920] using wordTrace_append hprefix tailTrace_7786920
  have hstable : (prefixWord ++ tailWord_7786920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786920).length < 2 ^ (prefixWord ++ tailWord_7786920).sum := by decide
  have hdescent : baseEnd_7786920 < baseStart_7786920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786953 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 2, 3, 2]
def baseStart_7786953 : Nat := 118140960795 + 7786953 * 2 ^ 59
def prefixEnd_7786953 : Nat := 4983230072969 + 3 ^ 40 * 7786953 * 2
def baseEnd_7786953 : Nat := 3998449722970377244275961

theorem tailTrace_7786953 : CollatzResearch.WordTrace tailWord_7786953 prefixEnd_7786953 3998449722970377244275961 := by
  unfold tailWord_7786953
  simp only [CollatzResearch.WordTrace]
  refine ⟨284013508558206661538309513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189342339038804441025539675 284013508558206661538309513)
  ·
    refine ⟨213010131418654996153732135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284013508558206661538309513 213010131418654996153732135)
    ·
      refine ⟨319515197127982494230598203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213010131418654996153732135 319515197127982494230598203)
      ·
        refine ⟨479272795691973741345897305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319515197127982494230598203 479272795691973741345897305)
        ·
          refine ⟨359454596768980306009422979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479272795691973741345897305 359454596768980306009422979)
          ·
            refine ⟨539181895153470459014134469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359454596768980306009422979 539181895153470459014134469)
            ·
              refine ⟨101096605341275711065150213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 539181895153470459014134469 101096605341275711065150213)
              ·
                refine ⟨18955613501489195824715665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101096605341275711065150213 18955613501489195824715665)
                ·
                  refine ⟨14216710126116896868536749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18955613501489195824715665 14216710126116896868536749)
                  ·
                    refine ⟨5331266297293836325701281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14216710126116896868536749 5331266297293836325701281)
                    ·
                      refine ⟨3998449722970377244275961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5331266297293836325701281 3998449722970377244275961)
                      ·
                        rfl

theorem cell23_7786953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 3, 2].length) (baseStart_7786953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786953 prefixEnd_7786953 := by exact prefixLift 7786953
  have htrace : WordTrace (prefixWord ++ tailWord_7786953) baseStart_7786953 baseEnd_7786953 := by
    simpa [prefixWord, tailWord_7786953, baseEnd_7786953] using wordTrace_append hprefix tailTrace_7786953
  have hstable : (prefixWord ++ tailWord_7786953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786953).length < 2 ^ (prefixWord ++ tailWord_7786953).sum := by decide
  have hdescent : baseEnd_7786953 < baseStart_7786953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7786983 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 2, 6, 2]
def baseStart_7786983 : Nat := 118140960795 + 7786983 * 2 ^ 59
def prefixEnd_7786983 : Nat := 4983230072969 + 3 ^ 40 * 7786983 * 2
def baseEnd_7786983 : Nat := 3998465127390012126900823

theorem tailTrace_7786983 : CollatzResearch.WordTrace tailWord_7786983 prefixEnd_7786983 3998465127390012126900823 := by
  unfold tailWord_7786983
  simp only [CollatzResearch.WordTrace]
  refine ⟨284014602748097976661901603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189343068498731984441267735 284014602748097976661901603)
  ·
    refine ⟨426021904122146964992852405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284014602748097976661901603 426021904122146964992852405)
    ·
      refine ⟨39939553511451277968079913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 426021904122146964992852405 39939553511451277968079913)
      ·
        refine ⟨29954665133588458476059935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39939553511451277968079913 29954665133588458476059935)
        ·
          refine ⟨44931997700382687714089903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29954665133588458476059935 44931997700382687714089903)
          ·
            refine ⟨67397996550574031571134855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44931997700382687714089903 67397996550574031571134855)
            ·
              refine ⟨101096994825861047356702283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67397996550574031571134855 101096994825861047356702283)
              ·
                refine ⟨151645492238791571035053425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101096994825861047356702283 151645492238791571035053425)
                ·
                  refine ⟨113734119179093678276290069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151645492238791571035053425 113734119179093678276290069)
                  ·
                    refine ⟨5331286836520016169201097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113734119179093678276290069 5331286836520016169201097)
                    ·
                      refine ⟨3998465127390012126900823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5331286836520016169201097 3998465127390012126900823)
                      ·
                        rfl

theorem cell23_7786983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_7786983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7786983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7786983 prefixEnd_7786983 := by exact prefixLift 7786983
  have htrace : WordTrace (prefixWord ++ tailWord_7786983) baseStart_7786983 baseEnd_7786983 := by
    simpa [prefixWord, tailWord_7786983, baseEnd_7786983] using wordTrace_append hprefix tailTrace_7786983
  have hstable : (prefixWord ++ tailWord_7786983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7786983).length < 2 ^ (prefixWord ++ tailWord_7786983).sum := by decide
  have hdescent : baseEnd_7786983 < baseStart_7786983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7786983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787037 : List Nat := [1, 4, 2, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_7787037 : Nat := 118140960795 + 7787037 * 2 ^ 59
def prefixEnd_7787037 : Nat := 4983230072969 + 3 ^ 40 * 7787037 * 2
def baseEnd_7787037 : Nat := 3998492855345354915625575

theorem tailTrace_7787037 : CollatzResearch.WordTrace tailWord_7787037 prefixEnd_7787037 3998492855345354915625575 := by
  unfold tailWord_7787037
  simp only [CollatzResearch.WordTrace]
  refine ⟨284016572289902343884367365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189344381526601562589578243 284016572289902343884367365)
  ·
    refine ⟨53253107304356689478318881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284016572289902343884367365 53253107304356689478318881)
    ·
      refine ⟨39939830478267517108739161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53253107304356689478318881 39939830478267517108739161)
      ·
        refine ⟨29954872858700637831554371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39939830478267517108739161 29954872858700637831554371)
        ·
          refine ⟨44932309288050956747331557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29954872858700637831554371 44932309288050956747331557)
          ·
            refine ⟨8424807991509554390124667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44932309288050956747331557 8424807991509554390124667)
            ·
              refine ⟨12637211987264331585187001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8424807991509554390124667 12637211987264331585187001)
              ·
                refine ⟨9477908990448248688890251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12637211987264331585187001 9477908990448248688890251)
                ·
                  refine ⟨14216863485672373033335377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9477908990448248688890251 14216863485672373033335377)
                  ·
                    refine ⟨10662647614254279775001533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14216863485672373033335377 10662647614254279775001533)
                    ·
                      refine ⟨3998492855345354915625575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10662647614254279775001533 3998492855345354915625575)
                      ·
                        rfl

theorem cell23_7787037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_7787037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787037 prefixEnd_7787037 := by exact prefixLift 7787037
  have htrace : WordTrace (prefixWord ++ tailWord_7787037) baseStart_7787037 baseEnd_7787037 := by
    simpa [prefixWord, tailWord_7787037, baseEnd_7787037] using wordTrace_append hprefix tailTrace_7787037
  have hstable : (prefixWord ++ tailWord_7787037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787037).length < 2 ^ (prefixWord ++ tailWord_7787037).sum := by decide
  have hdescent : baseEnd_7787037 < baseStart_7787037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787047 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_7787047 : Nat := 118140960795 + 7787047 * 2 ^ 59
def prefixEnd_7787047 : Nat := 4983230072969 + 3 ^ 40 * 7787047 * 2
def baseEnd_7787047 : Nat := 3998497990151899876500529

theorem tailTrace_7787047 : CollatzResearch.WordTrace tailWord_7787047 prefixEnd_7787047 3998497990151899876500529 := by
  unfold tailWord_7787047
  simp only [CollatzResearch.WordTrace]
  refine ⟨284016937019866115592231395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189344624679910743728154263 284016937019866115592231395)
  ·
    refine ⟨426025405529799173388347093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284016937019866115592231395 426025405529799173388347093)
    ·
      refine ⟨9984970442104668126289385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 426025405529799173388347093 9984970442104668126289385)
      ·
        refine ⟨7488727831578501094717039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9984970442104668126289385 7488727831578501094717039)
        ·
          refine ⟨11233091747367751642075559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7488727831578501094717039 11233091747367751642075559)
          ·
            refine ⟨16849637621051627463113339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11233091747367751642075559 16849637621051627463113339)
            ·
              refine ⟨25274456431577441194670009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16849637621051627463113339 25274456431577441194670009)
              ·
                refine ⟨18955842323683080896002507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25274456431577441194670009 18955842323683080896002507)
                ·
                  refine ⟨28433763485524621344003761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18955842323683080896002507 28433763485524621344003761)
                  ·
                    refine ⟨21325322614143466008002821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28433763485524621344003761 21325322614143466008002821)
                    ·
                      refine ⟨3998497990151899876500529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21325322614143466008002821 3998497990151899876500529)
                      ·
                        rfl

theorem cell23_7787047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_7787047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787047 prefixEnd_7787047 := by exact prefixLift 7787047
  have htrace : WordTrace (prefixWord ++ tailWord_7787047) baseStart_7787047 baseEnd_7787047 := by
    simpa [prefixWord, tailWord_7787047, baseEnd_7787047] using wordTrace_append hprefix tailTrace_7787047
  have hstable : (prefixWord ++ tailWord_7787047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787047).length < 2 ^ (prefixWord ++ tailWord_7787047).sum := by decide
  have hdescent : baseEnd_7787047 < baseStart_7787047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787050 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_7787050 : Nat := 118140960795 + 7787050 * 2 ^ 59
def prefixEnd_7787050 : Nat := 4983230072969 + 3 ^ 40 * 7787050 * 2
def baseEnd_7787050 : Nat := 3998499530593863364763015

theorem tailTrace_7787050 : CollatzResearch.WordTrace tailWord_7787050 prefixEnd_7787050 3998499530593863364763015 := by
  unfold tailWord_7787050
  simp only [CollatzResearch.WordTrace]
  refine ⟨71004261609713811776147651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189344697625903498069727069 71004261609713811776147651)
  ·
    refine ⟨106506392414570717664221477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71004261609713811776147651 106506392414570717664221477)
    ·
      refine ⟨19969948577732009562041527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106506392414570717664221477 19969948577732009562041527)
      ·
        refine ⟨29954922866598014343062291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19969948577732009562041527 29954922866598014343062291)
        ·
          refine ⟨44932384299897021514593437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29954922866598014343062291 44932384299897021514593437)
          ·
            refine ⟨16849644112461383067972539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44932384299897021514593437 16849644112461383067972539)
            ·
              refine ⟨25274466168692074601958809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16849644112461383067972539 25274466168692074601958809)
              ·
                refine ⟨18955849626519055951469107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25274466168692074601958809 18955849626519055951469107)
                ·
                  refine ⟨28433774439778583927203661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18955849626519055951469107 28433774439778583927203661)
                  ·
                    refine ⟨10662665414916968972701373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28433774439778583927203661 10662665414916968972701373)
                    ·
                      refine ⟨3998499530593863364763015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10662665414916968972701373 3998499530593863364763015)
                      ·
                        rfl

theorem cell23_7787050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_7787050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787050 prefixEnd_7787050 := by exact prefixLift 7787050
  have htrace : WordTrace (prefixWord ++ tailWord_7787050) baseStart_7787050 baseEnd_7787050 := by
    simpa [prefixWord, tailWord_7787050, baseEnd_7787050] using wordTrace_append hprefix tailTrace_7787050
  have hstable : (prefixWord ++ tailWord_7787050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787050).length < 2 ^ (prefixWord ++ tailWord_7787050).sum := by decide
  have hdescent : baseEnd_7787050 < baseStart_7787050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787054 : List Nat := [4, 1, 3, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_7787054 : Nat := 118140960795 + 7787054 * 2 ^ 59
def prefixEnd_7787054 : Nat := 4983230072969 + 3 ^ 40 * 7787054 * 2
def baseEnd_7787054 : Nat := 3998501584516481349112997

theorem tailTrace_7787054 : CollatzResearch.WordTrace tailWord_7787054 prefixEnd_7787054 3998501584516481349112997 := by
  unfold tailWord_7787054
  simp only [CollatzResearch.WordTrace]
  refine ⟨35502149041355094473467027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189344794887227170525157477 35502149041355094473467027)
  ·
    refine ⟨53253223562032641710200541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35502149041355094473467027 53253223562032641710200541)
    ·
      refine ⟨19969958835762240641325203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53253223562032641710200541 19969958835762240641325203)
      ·
        refine ⟨29954938253643360961987805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19969958835762240641325203 29954938253643360961987805)
        ·
          refine ⟨11233101845116260360745427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29954938253643360961987805 11233101845116260360745427)
          ·
            refine ⟨16849652767674390541118141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11233101845116260360745427 16849652767674390541118141)
            ·
              refine ⟨6318619787877896452919303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16849652767674390541118141 6318619787877896452919303)
              ·
                refine ⟨9477929681816844679378955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6318619787877896452919303 9477929681816844679378955)
                ·
                  refine ⟨14216894522725267019068433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9477929681816844679378955 14216894522725267019068433)
                  ·
                    refine ⟨10662670892043950264301325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14216894522725267019068433 10662670892043950264301325)
                    ·
                      refine ⟨3998501584516481349112997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10662670892043950264301325 3998501584516481349112997)
                      ·
                        rfl

theorem cell23_7787054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_7787054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787054 prefixEnd_7787054 := by exact prefixLift 7787054
  have htrace : WordTrace (prefixWord ++ tailWord_7787054) baseStart_7787054 baseEnd_7787054 := by
    simpa [prefixWord, tailWord_7787054, baseEnd_7787054] using wordTrace_append hprefix tailTrace_7787054
  have hstable : (prefixWord ++ tailWord_7787054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787054).length < 2 ^ (prefixWord ++ tailWord_7787054).sum := by decide
  have hdescent : baseEnd_7787054 < baseStart_7787054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787073 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_7787073 : Nat := 118140960795 + 7787073 * 2 ^ 59
def prefixEnd_7787073 : Nat := 4983230072969 + 3 ^ 40 * 7787073 * 2
def baseEnd_7787073 : Nat := 3998511340648916774775409

theorem tailTrace_7787073 : CollatzResearch.WordTrace tailWord_7787073 prefixEnd_7787073 3998511340648916774775409 := by
  unfold tailWord_7787073
  simp only [CollatzResearch.WordTrace]
  refine ⟨284017885317771922032677873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189345256878514614688451915 284017885317771922032677873)
  ·
    refine ⟨213013413988328941524508405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284017885317771922032677873 213013413988328941524508405)
    ·
      refine ⟨19970007561405838267922663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213013413988328941524508405 19970007561405838267922663)
      ·
        refine ⟨29955011342108757401883995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19970007561405838267922663 29955011342108757401883995)
        ·
          refine ⟨44932517013163136102825993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29955011342108757401883995 44932517013163136102825993)
          ·
            refine ⟨33699387759872352077119495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44932517013163136102825993 33699387759872352077119495)
            ·
              refine ⟨50549081639808528115679243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33699387759872352077119495 50549081639808528115679243)
              ·
                refine ⟨75823622459712792173518865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50549081639808528115679243 75823622459712792173518865)
                ·
                  refine ⟨56867716844784594130139149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75823622459712792173518865 56867716844784594130139149)
                  ·
                    refine ⟨21325393816794222798802181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56867716844784594130139149 21325393816794222798802181)
                    ·
                      refine ⟨3998511340648916774775409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21325393816794222798802181 3998511340648916774775409)
                      ·
                        rfl

theorem cell23_7787073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_7787073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787073 prefixEnd_7787073 := by exact prefixLift 7787073
  have htrace : WordTrace (prefixWord ++ tailWord_7787073) baseStart_7787073 baseEnd_7787073 := by
    simpa [prefixWord, tailWord_7787073, baseEnd_7787073] using wordTrace_append hprefix tailTrace_7787073
  have hstable : (prefixWord ++ tailWord_7787073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787073).length < 2 ^ (prefixWord ++ tailWord_7787073).sum := by decide
  have hdescent : baseEnd_7787073 < baseStart_7787073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787096 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 9]
def baseStart_7787096 : Nat := 118140960795 + 7787096 * 2 ^ 59
def prefixEnd_7787096 : Nat := 4983230072969 + 3 ^ 40 * 7787096 * 2
def baseEnd_7787096 : Nat := 444280350078218909420867

theorem tailTrace_7787096 : CollatzResearch.WordTrace tailWord_7787096 prefixEnd_7787096 444280350078218909420867 := by
  unfold tailWord_7787096
  simp only [CollatzResearch.WordTrace]
  refine ⟨142009362098344298480382571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189345816131125731307176761 142009362098344298480382571)
  ·
    refine ⟨213014043147516447720573857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142009362098344298480382571 213014043147516447720573857)
    ·
      refine ⟨159760532360637335790430393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213014043147516447720573857 159760532360637335790430393)
      ·
        refine ⟨119820399270478001842822795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159760532360637335790430393 119820399270478001842822795)
        ·
          refine ⟨179730598905717002764234193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119820399270478001842822795 179730598905717002764234193)
          ·
            refine ⟨134797949179287752073175645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179730598905717002764234193 134797949179287752073175645)
            ·
              refine ⟨50549230942232907027440867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134797949179287752073175645 50549230942232907027440867)
              ·
                refine ⟨75823846413349360541161301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50549230942232907027440867 75823846413349360541161301)
                ·
                  refine ⟨444280350078218909420867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75823846413349360541161301 444280350078218909420867)
                  ·
                    rfl

theorem cell23_7787096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 9].length) (baseStart_7787096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787096 prefixEnd_7787096 := by exact prefixLift 7787096
  have htrace : WordTrace (prefixWord ++ tailWord_7787096) baseStart_7787096 baseEnd_7787096 := by
    simpa [prefixWord, tailWord_7787096, baseEnd_7787096] using wordTrace_append hprefix tailTrace_7787096
  have hstable : (prefixWord ++ tailWord_7787096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787096).length < 2 ^ (prefixWord ++ tailWord_7787096).sum := by decide
  have hdescent : baseEnd_7787096 < baseStart_7787096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787140 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_7787140 : Nat := 118140960795 + 7787140 * 2 ^ 59
def prefixEnd_7787140 : Nat := 4983230072969 + 3 ^ 40 * 7787140 * 2
def baseEnd_7787140 : Nat := 3998545743852768012637601

theorem tailTrace_7787140 : CollatzResearch.WordTrace tailWord_7787140 prefixEnd_7787140 3998545743852768012637601 := by
  unfold tailWord_7787140
  simp only [CollatzResearch.WordTrace]
  refine ⟨142010164504264596237683437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189346886005686128316911249 142010164504264596237683437)
  ·
    refine ⟨53253811689099223589131289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142010164504264596237683437 53253811689099223589131289)
    ·
      refine ⟨39940358766824417691848467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53253811689099223589131289 39940358766824417691848467)
      ·
        refine ⟨59910538150236626537772701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39940358766824417691848467 59910538150236626537772701)
        ·
          refine ⟨22466451806338734951664763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59910538150236626537772701 22466451806338734951664763)
          ·
            refine ⟨33699677709508102427497145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22466451806338734951664763 33699677709508102427497145)
            ·
              refine ⟨25274758282131076820622859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33699677709508102427497145 25274758282131076820622859)
              ·
                refine ⟨37912137423196615230934289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25274758282131076820622859 37912137423196615230934289)
                ·
                  refine ⟨28434103067397461423200717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37912137423196615230934289 28434103067397461423200717)
                  ·
                    refine ⟨10662788650274048033700269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28434103067397461423200717 10662788650274048033700269)
                    ·
                      refine ⟨3998545743852768012637601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10662788650274048033700269 3998545743852768012637601)
                      ·
                        rfl

theorem cell23_7787140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_7787140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787140 prefixEnd_7787140 := by exact prefixLift 7787140
  have htrace : WordTrace (prefixWord ++ tailWord_7787140) baseStart_7787140 baseEnd_7787140 := by
    simpa [prefixWord, tailWord_7787140, baseEnd_7787140] using wordTrace_append hprefix tailTrace_7787140
  have hstable : (prefixWord ++ tailWord_7787140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787140).length < 2 ^ (prefixWord ++ tailWord_7787140).sum := by decide
  have hdescent : baseEnd_7787140 < baseStart_7787140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787250 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 3, 5]
def baseStart_7787250 : Nat := 118140960795 + 7787250 * 2 ^ 59
def prefixEnd_7787250 : Nat := 4983230072969 + 3 ^ 40 * 7787250 * 2
def baseEnd_7787250 : Nat := 1332867408908254194087365

theorem tailTrace_7787250 : CollatzResearch.WordTrace tailWord_7787250 prefixEnd_7787250 1332867408908254194087365 := by
  unfold tailWord_7787250
  simp only [CollatzResearch.WordTrace]
  refine ⟨71006085259532670315467801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189349560692087120841247469 71006085259532670315467801)
  ·
    refine ⟨53254563944649502736600851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71006085259532670315467801 53254563944649502736600851)
    ·
      refine ⟨79881845916974254104901277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53254563944649502736600851 79881845916974254104901277)
      ·
        refine ⟨29955692218865345289337979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79881845916974254104901277 29955692218865345289337979)
        ·
          refine ⟨44933538328298017934006969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29955692218865345289337979 44933538328298017934006969)
          ·
            refine ⟨33700153746223513450505227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44933538328298017934006969 33700153746223513450505227)
            ·
              refine ⟨50550230619335270175757841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33700153746223513450505227 50550230619335270175757841)
              ·
                refine ⟨37912672964501452631818381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50550230619335270175757841 37912672964501452631818381)
                ·
                  refine ⟨14217252361688044736931893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37912672964501452631818381 14217252361688044736931893)
                  ·
                    refine ⟨1332867408908254194087365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14217252361688044736931893 1332867408908254194087365)
                    ·
                      rfl

theorem cell23_7787250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_7787250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787250 prefixEnd_7787250 := by exact prefixLift 7787250
  have htrace : WordTrace (prefixWord ++ tailWord_7787250) baseStart_7787250 baseEnd_7787250 := by
    simpa [prefixWord, tailWord_7787250, baseEnd_7787250] using wordTrace_append hprefix tailTrace_7787250
  have hstable : (prefixWord ++ tailWord_7787250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787250).length < 2 ^ (prefixWord ++ tailWord_7787250).sum := by decide
  have hdescent : baseEnd_7787250 < baseStart_7787250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787290 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5]
def baseStart_7787290 : Nat := 118140960795 + 7787290 * 2 ^ 59
def prefixEnd_7787290 : Nat := 4983230072969 + 3 ^ 40 * 7787290 * 2
def baseEnd_7787290 : Nat := 3998622765950942425761911

theorem tailTrace_7787290 : CollatzResearch.WordTrace tailWord_7787290 prefixEnd_7787290 3998622765950942425761911 := by
  unfold tailWord_7787290
  simp only [CollatzResearch.WordTrace]
  refine ⟨71006449989496442023331831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189350533305323845395551549 71006449989496442023331831)
  ·
    refine ⟨106509674984244663034997747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71006449989496442023331831 106509674984244663034997747)
    ·
      refine ⟨159764512476366994552496621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106509674984244663034997747 159764512476366994552496621)
      ·
        refine ⟨59911692178637622957186233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159764512476366994552496621 59911692178637622957186233)
        ·
          refine ⟨44933769133978217217889675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59911692178637622957186233 44933769133978217217889675)
          ·
            refine ⟨67400653700967325826834513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44933769133978217217889675 67400653700967325826834513)
            ·
              refine ⟨50550490275725494370125885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67400653700967325826834513 50550490275725494370125885)
              ·
                refine ⟨18956433853397060388797207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50550490275725494370125885 18956433853397060388797207)
                ·
                  refine ⟨28434650780095590583195811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18956433853397060388797207 28434650780095590583195811)
                  ·
                    refine ⟨42651976170143385874793717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28434650780095590583195811 42651976170143385874793717)
                    ·
                      refine ⟨3998622765950942425761911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42651976170143385874793717 3998622765950942425761911)
                      ·
                        rfl

theorem cell23_7787290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_7787290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787290 prefixEnd_7787290 := by exact prefixLift 7787290
  have htrace : WordTrace (prefixWord ++ tailWord_7787290) baseStart_7787290 baseEnd_7787290 := by
    simpa [prefixWord, tailWord_7787290, baseEnd_7787290] using wordTrace_append hprefix tailTrace_7787290
  have hstable : (prefixWord ++ tailWord_7787290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787290).length < 2 ^ (prefixWord ++ tailWord_7787290).sum := by decide
  have hdescent : baseEnd_7787290 < baseStart_7787290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787314 : List Nat := [3, 2, 1, 1, 3, 1, 5, 1, 2, 4]
def baseStart_7787314 : Nat := 118140960795 + 7787314 * 2 ^ 59
def prefixEnd_7787314 : Nat := 4983230072969 + 3 ^ 40 * 7787314 * 2
def baseEnd_7787314 : Nat := 1332878363162216777287267

theorem tailTrace_7787314 : CollatzResearch.WordTrace tailWord_7787314 prefixEnd_7787314 1332878363162216777287267 := by
  unfold tailWord_7787314
  simp only [CollatzResearch.WordTrace]
  refine ⟨71006668827474705048050249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189351116873265880128133997 71006668827474705048050249)
  ·
    refine ⟨53255001620606028786037687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71006668827474705048050249 53255001620606028786037687)
    ·
      refine ⟨79882502430909043179056531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53255001620606028786037687 79882502430909043179056531)
      ·
        refine ⟨119823753646363564768584797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79882502430909043179056531 119823753646363564768584797)
        ·
          refine ⟨44933907617386336788219299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119823753646363564768584797 44933907617386336788219299)
          ·
            refine ⟨67400861426079505182328949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44933907617386336788219299 67400861426079505182328949)
            ·
              refine ⟨6318830758694953610843339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67400861426079505182328949 6318830758694953610843339)
              ·
                refine ⟨9478246138042430416265009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6318830758694953610843339 9478246138042430416265009)
                ·
                  refine ⟨7108684603531822812198757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9478246138042430416265009 7108684603531822812198757)
                  ·
                    refine ⟨1332878363162216777287267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7108684603531822812198757 1332878363162216777287267)
                    ·
                      rfl

theorem cell23_7787314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_7787314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787314 prefixEnd_7787314 := by exact prefixLift 7787314
  have htrace : WordTrace (prefixWord ++ tailWord_7787314) baseStart_7787314 baseEnd_7787314 := by
    simpa [prefixWord, tailWord_7787314, baseEnd_7787314] using wordTrace_append hprefix tailTrace_7787314
  have hstable : (prefixWord ++ tailWord_7787314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787314).length < 2 ^ (prefixWord ++ tailWord_7787314).sum := by decide
  have hdescent : baseEnd_7787314 < baseStart_7787314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787317 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_7787317 : Nat := 118140960795 + 7787317 * 2 ^ 59
def prefixEnd_7787317 : Nat := 4983230072969 + 3 ^ 40 * 7787317 * 2
def baseEnd_7787317 : Nat := 3998636629928613820124287

theorem tailTrace_7787317 : CollatzResearch.WordTrace tailWord_7787317 prefixEnd_7787317 3998636629928613820124287 := by
  unfold tailWord_7787317
  simp only [CollatzResearch.WordTrace]
  refine ⟨284026784728887951704560205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189351189819258634469706803 284026784728887951704560205)
  ·
    refine ⟨106510044273332981889210077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284026784728887951704560205 106510044273332981889210077)
    ·
      refine ⟨39941266602499868208453779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106510044273332981889210077 39941266602499868208453779)
      ·
        refine ⟨59911899903749802312680669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39941266602499868208453779 59911899903749802312680669)
        ·
          refine ⟨22466962463906175867255251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59911899903749802312680669 22466962463906175867255251)
          ·
            refine ⟨33700443695859263800882877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22466962463906175867255251 33700443695859263800882877)
            ·
              refine ⟨12637666385947223925331079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33700443695859263800882877 12637666385947223925331079)
              ·
                refine ⟨18956499578920835887996619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12637666385947223925331079 18956499578920835887996619)
                ·
                  refine ⟨28434749368381253831994929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18956499578920835887996619 28434749368381253831994929)
                  ·
                    refine ⟨21326062026285940373996197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28434749368381253831994929 21326062026285940373996197)
                    ·
                      refine ⟨3998636629928613820124287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21326062026285940373996197 3998636629928613820124287)
                      ·
                        rfl

theorem cell23_7787317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_7787317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787317 prefixEnd_7787317 := by exact prefixLift 7787317
  have htrace : WordTrace (prefixWord ++ tailWord_7787317) baseStart_7787317 baseEnd_7787317 := by
    simpa [prefixWord, tailWord_7787317, baseEnd_7787317] using wordTrace_append hprefix tailTrace_7787317
  have hstable : (prefixWord ++ tailWord_7787317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787317).length < 2 ^ (prefixWord ++ tailWord_7787317).sum := by decide
  have hdescent : baseEnd_7787317 < baseStart_7787317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787327 : List Nat := [1, 1, 2, 2, 5, 3, 2, 7]
def baseStart_7787327 : Nat := 118140960795 + 7787327 * 2 ^ 59
def prefixEnd_7787327 : Nat := 4983230072969 + 3 ^ 40 * 7787327 * 2
def baseEnd_7787327 : Nat := 148097843138339214111083

theorem tailTrace_7787327 : CollatzResearch.WordTrace tailWord_7787327 prefixEnd_7787327 148097843138339214111083 := by
  unfold tailWord_7787327
  simp only [CollatzResearch.WordTrace]
  refine ⟨284027149458851723412424235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189351432972567815608282823 284027149458851723412424235)
  ·
    refine ⟨426040724188277585118636353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284027149458851723412424235 426040724188277585118636353)
    ·
      refine ⟨319530543141208188838977265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426040724188277585118636353 319530543141208188838977265)
      ·
        refine ⟨239647907355906141629232949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319530543141208188838977265 239647907355906141629232949)
        ·
          refine ⟨22466991314616200777740589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239647907355906141629232949 22466991314616200777740589)
          ·
            refine ⟨8425121742981075291652721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22466991314616200777740589 8425121742981075291652721)
            ·
              refine ⟨6318841307235806468739541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8425121742981075291652721 6318841307235806468739541)
              ·
                refine ⟨148097843138339214111083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6318841307235806468739541 148097843138339214111083)
                ·
                  rfl

theorem cell23_7787327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 7].length) (baseStart_7787327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787327 prefixEnd_7787327 := by exact prefixLift 7787327
  have htrace : WordTrace (prefixWord ++ tailWord_7787327) baseStart_7787327 baseEnd_7787327 := by
    simpa [prefixWord, tailWord_7787327, baseEnd_7787327] using wordTrace_append hprefix tailTrace_7787327
  have hstable : (prefixWord ++ tailWord_7787327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787327).length < 2 ^ (prefixWord ++ tailWord_7787327).sum := by decide
  have hdescent : baseEnd_7787327 < baseStart_7787327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787332 : List Nat := [2, 3, 4, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_7787332 : Nat := 118140960795 + 7787332 * 2 ^ 59
def prefixEnd_7787332 : Nat := 4983230072969 + 3 ^ 40 * 7787332 * 2
def baseEnd_7787332 : Nat := 3998644332138431261436719

theorem tailTrace_7787332 : CollatzResearch.WordTrace tailWord_7787332 prefixEnd_7787332 3998644332138431261436719 := by
  unfold tailWord_7787332
  simp only [CollatzResearch.WordTrace]
  refine ⟨142013665911916804633178125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189351554549222406177570833 142013665911916804633178125)
  ·
    refine ⟨53255124716968801737441797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142013665911916804633178125 53255124716968801737441797)
    ·
      refine ⟨9985335884431650325770337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53255124716968801737441797 9985335884431650325770337)
      ·
        refine ⟨7489001913323737744327753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9985335884431650325770337 7489001913323737744327753)
        ·
          refine ⟨5616751434992803308245815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7489001913323737744327753 5616751434992803308245815)
          ·
            refine ⟨8425127152489204962368723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5616751434992803308245815 8425127152489204962368723)
            ·
              refine ⟨12637690728733807443553085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8425127152489204962368723 12637690728733807443553085)
              ·
                refine ⟨4739134023275177791332407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12637690728733807443553085 4739134023275177791332407)
                ·
                  refine ⟨7108701034912766686998611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4739134023275177791332407 7108701034912766686998611)
                  ·
                    refine ⟨10663051552369150030497917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7108701034912766686998611 10663051552369150030497917)
                    ·
                      refine ⟨3998644332138431261436719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10663051552369150030497917 3998644332138431261436719)
                      ·
                        rfl

theorem cell23_7787332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_7787332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787332 prefixEnd_7787332 := by exact prefixLift 7787332
  have htrace : WordTrace (prefixWord ++ tailWord_7787332) baseStart_7787332 baseEnd_7787332 := by
    simpa [prefixWord, tailWord_7787332, baseEnd_7787332] using wordTrace_append hprefix tailTrace_7787332
  have hstable : (prefixWord ++ tailWord_7787332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787332).length < 2 ^ (prefixWord ++ tailWord_7787332).sum := by decide
  have hdescent : baseEnd_7787332 < baseStart_7787332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787337 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 4, 1, 3]
def baseStart_7787337 : Nat := 118140960795 + 7787337 * 2 ^ 59
def prefixEnd_7787337 : Nat := 4983230072969 + 3 ^ 40 * 7787337 * 2
def baseEnd_7787337 : Nat := 3998646899541703741874195

theorem tailTrace_7787337 : CollatzResearch.WordTrace tailWord_7787337 prefixEnd_7787337 3998646899541703741874195 := by
  unfold tailWord_7787337
  simp only [CollatzResearch.WordTrace]
  refine ⟨284027514188815495120288265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189351676125876996746858843 284027514188815495120288265)
  ·
    refine ⟨213020635641611621340216199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284027514188815495120288265 213020635641611621340216199)
    ·
      refine ⟨319530953462417432010324299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213020635641611621340216199 319530953462417432010324299)
      ·
        refine ⟨479296430193626148015486449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319530953462417432010324299 479296430193626148015486449)
        ·
          refine ⟨359472322645219611011614837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479296430193626148015486449 359472322645219611011614837)
          ·
            refine ⟨33700530247989338532338891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 359472322645219611011614837 33700530247989338532338891)
            ·
              refine ⟨50550795371984007798508337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33700530247989338532338891 50550795371984007798508337)
              ·
                refine ⟨37913096528988005848881253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50550795371984007798508337 37913096528988005848881253)
                ·
                  refine ⟨7108705599185251096665235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37913096528988005848881253 7108705599185251096665235)
                  ·
                    refine ⟨10663058398777876644997853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7108705599185251096665235 10663058398777876644997853)
                    ·
                      refine ⟨3998646899541703741874195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10663058398777876644997853 3998646899541703741874195)
                      ·
                        rfl

theorem cell23_7787337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 1, 3].length) (baseStart_7787337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787337 prefixEnd_7787337 := by exact prefixLift 7787337
  have htrace : WordTrace (prefixWord ++ tailWord_7787337) baseStart_7787337 baseEnd_7787337 := by
    simpa [prefixWord, tailWord_7787337, baseEnd_7787337] using wordTrace_append hprefix tailTrace_7787337
  have hstable : (prefixWord ++ tailWord_7787337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787337).length < 2 ^ (prefixWord ++ tailWord_7787337).sum := by decide
  have hdescent : baseEnd_7787337 < baseStart_7787337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787343 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 8]
def baseStart_7787343 : Nat := 118140960795 + 7787343 * 2 ^ 59
def prefixEnd_7787343 : Nat := 4983230072969 + 3 ^ 40 * 7787343 * 2
def baseEnd_7787343 : Nat := 3998649980425630718399167

theorem tailTrace_7787343 : CollatzResearch.WordTrace tailWord_7787343 prefixEnd_7787343 3998649980425630718399167 := by
  unfold tailWord_7787343
  simp only [CollatzResearch.WordTrace]
  refine ⟨284027733026793758145006683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189351822017862505430004455 284027733026793758145006683)
  ·
    refine ⟨426041599540190637217510025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284027733026793758145006683 426041599540190637217510025)
    ·
      refine ⟨319531199655142977913132519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426041599540190637217510025 319531199655142977913132519)
      ·
        refine ⟨479296799482714466869698779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319531199655142977913132519 479296799482714466869698779)
        ·
          refine ⟨718945199224071700304548169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479296799482714466869698779 718945199224071700304548169)
          ·
            refine ⟨539208899418053775228411127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718945199224071700304548169 539208899418053775228411127)
            ·
              refine ⟨808813349127080662842616691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539208899418053775228411127 808813349127080662842616691)
              ·
                refine ⟨1213220023690620994263925037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808813349127080662842616691 1213220023690620994263925037)
                ·
                  refine ⟨454957508883982872848971889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1213220023690620994263925037 454957508883982872848971889)
                  ·
                    refine ⟨341218131662987154636728917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 454957508883982872848971889 341218131662987154636728917)
                    ·
                      refine ⟨3998649980425630718399167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 341218131662987154636728917 3998649980425630718399167)
                      ·
                        rfl

theorem cell23_7787343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_7787343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787343 prefixEnd_7787343 := by exact prefixLift 7787343
  have htrace : WordTrace (prefixWord ++ tailWord_7787343) baseStart_7787343 baseEnd_7787343 := by
    simpa [prefixWord, tailWord_7787343, baseEnd_7787343] using wordTrace_append hprefix tailTrace_7787343
  have hstable : (prefixWord ++ tailWord_7787343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787343).length < 2 ^ (prefixWord ++ tailWord_7787343).sum := by decide
  have hdescent : baseEnd_7787343 < baseStart_7787343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787360 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 4]
def baseStart_7787360 : Nat := 118140960795 + 7787360 * 2 ^ 59
def prefixEnd_7787360 : Nat := 4983230072969 + 3 ^ 40 * 7787360 * 2
def baseEnd_7787360 : Nat := 3998658709596757151886589

theorem tailTrace_7787360 : CollatzResearch.WordTrace tailWord_7787360 prefixEnd_7787360 3998658709596757151886589 := by
  unfold tailWord_7787360
  simp only [CollatzResearch.WordTrace]
  refine ⟨142014176533866085024187767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189352235378488113365583689 142014176533866085024187767)
  ·
    refine ⟨213021264800799127536281651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142014176533866085024187767 213021264800799127536281651)
    ·
      refine ⟨319531897201198691304422477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213021264800799127536281651 319531897201198691304422477)
      ·
        refine ⟨119824461450449509239158429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319531897201198691304422477 119824461450449509239158429)
        ·
          refine ⟨44934173043918565964684411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119824461450449509239158429 44934173043918565964684411)
          ·
            refine ⟨67401259565877848947026617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44934173043918565964684411 67401259565877848947026617)
            ·
              refine ⟨50550944674408386710269963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67401259565877848947026617 50550944674408386710269963)
              ·
                refine ⟨75826417011612580065404945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50550944674408386710269963 75826417011612580065404945)
                ·
                  refine ⟨56869812758709435049053709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75826417011612580065404945 56869812758709435049053709)
                  ·
                    refine ⟨21326179784516038143395141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56869812758709435049053709 21326179784516038143395141)
                    ·
                      refine ⟨3998658709596757151886589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21326179784516038143395141 3998658709596757151886589)
                      ·
                        rfl

theorem cell23_7787360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_7787360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787360 prefixEnd_7787360 := by exact prefixLift 7787360
  have htrace : WordTrace (prefixWord ++ tailWord_7787360) baseStart_7787360 baseEnd_7787360 := by
    simpa [prefixWord, tailWord_7787360, baseEnd_7787360] using wordTrace_append hprefix tailTrace_7787360
  have hstable : (prefixWord ++ tailWord_7787360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787360).length < 2 ^ (prefixWord ++ tailWord_7787360).sum := by decide
  have hdescent : baseEnd_7787360 < baseStart_7787360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787381 : List Nat := [1, 3, 4, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_7787381 : Nat := 118140960795 + 7787381 * 2 ^ 59
def prefixEnd_7787381 : Nat := 4983230072969 + 3 ^ 40 * 7787381 * 2
def baseEnd_7787381 : Nat := 3998669492690501569723993

theorem tailTrace_7787381 : CollatzResearch.WordTrace tailWord_7787381 prefixEnd_7787381 3998669492690501569723993 := by
  unfold tailWord_7787381
  simp only [CollatzResearch.WordTrace]
  refine ⟨284029119000656090634889997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189352746000437393756593331 284029119000656090634889997)
  ·
    refine ⟨106510919625246033988083749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284029119000656090634889997 106510919625246033988083749)
    ·
      refine ⟨19970797429733631372765703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106510919625246033988083749 19970797429733631372765703)
      ·
        refine ⟨29956196144600447059148555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19970797429733631372765703 29956196144600447059148555)
        ·
          refine ⟨44934294216900670588722833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29956196144600447059148555 44934294216900670588722833)
          ·
            refine ⟨33700720662675502941542125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44934294216900670588722833 33700720662675502941542125)
            ·
              refine ⟨12637770248503313603078297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33700720662675502941542125 12637770248503313603078297)
              ·
                refine ⟨9478327686377485202308723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12637770248503313603078297 9478327686377485202308723)
                ·
                  refine ⟨14217491529566227803463085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9478327686377485202308723 14217491529566227803463085)
                  ·
                    refine ⟨5331559323587335426298657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14217491529566227803463085 5331559323587335426298657)
                    ·
                      refine ⟨3998669492690501569723993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5331559323587335426298657 3998669492690501569723993)
                      ·
                        rfl

theorem cell23_7787381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_7787381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787381 prefixEnd_7787381 := by exact prefixLift 7787381
  have htrace : WordTrace (prefixWord ++ tailWord_7787381) baseStart_7787381 baseEnd_7787381 := by
    simpa [prefixWord, tailWord_7787381, baseEnd_7787381] using wordTrace_append hprefix tailTrace_7787381
  have hstable : (prefixWord ++ tailWord_7787381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787381).length < 2 ^ (prefixWord ++ tailWord_7787381).sum := by decide
  have hdescent : baseEnd_7787381 < baseStart_7787381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787447 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 2, 5]
def baseStart_7787447 : Nat := 118140960795 + 7787447 * 2 ^ 59
def prefixEnd_7787447 : Nat := 4983230072969 + 3 ^ 40 * 7787447 * 2
def baseEnd_7787447 : Nat := 1332901127471232770499563

theorem tailTrace_7787447 : CollatzResearch.WordTrace tailWord_7787447 prefixEnd_7787447 1332901127471232770499563 := by
  unfold tailWord_7787447
  simp only [CollatzResearch.WordTrace]
  refine ⟨284031526218416983906792595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189354350812277989271195063 284031526218416983906792595)
  ·
    refine ⟨426047289327625475860188893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284031526218416983906792595 426047289327625475860188893)
    ·
      refine ⟨159767733497859553447570835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426047289327625475860188893 159767733497859553447570835)
      ·
        refine ⟨239651600246789330171356253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159767733497859553447570835 239651600246789330171356253)
        ·
          refine ⟨89869350092545998814258595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239651600246789330171356253 89869350092545998814258595)
          ·
            refine ⟨134804025138818998221387893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89869350092545998814258595 134804025138818998221387893)
            ·
              refine ⟨12637877356764281083255115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134804025138818998221387893 12637877356764281083255115)
              ·
                refine ⟨18956816035146421624882673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12637877356764281083255115 18956816035146421624882673)
                ·
                  refine ⟨14217612026359816218662005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18956816035146421624882673 14217612026359816218662005)
                  ·
                    refine ⟨1332901127471232770499563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14217612026359816218662005 1332901127471232770499563)
                    ·
                      rfl

theorem cell23_7787447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_7787447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787447 prefixEnd_7787447 := by exact prefixLift 7787447
  have htrace : WordTrace (prefixWord ++ tailWord_7787447) baseStart_7787447 baseEnd_7787447 := by
    simpa [prefixWord, tailWord_7787447, baseEnd_7787447] using wordTrace_append hprefix tailTrace_7787447
  have hstable : (prefixWord ++ tailWord_7787447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787447).length < 2 ^ (prefixWord ++ tailWord_7787447).sum := by decide
  have hdescent : baseEnd_7787447 < baseStart_7787447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787500 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 9]
def baseStart_7787500 : Nat := 118140960795 + 7787500 * 2 ^ 59
def prefixEnd_7787500 : Nat := 4983230072969 + 3 ^ 40 * 7787500 * 2
def baseEnd_7787500 : Nat := 3998730596888386604135945

theorem tailTrace_7787500 : CollatzResearch.WordTrace tailWord_7787500 prefixEnd_7787500 3998730596888386604135945 := by
  unfold tailWord_7787500
  simp only [CollatzResearch.WordTrace]
  refine ⟨142016729643612486979235977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189355639524816649305647969 142016729643612486979235977)
  ·
    refine ⟨106512547232709365234426983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142016729643612486979235977 106512547232709365234426983)
    ·
      refine ⟨159768820849064047851640475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106512547232709365234426983 159768820849064047851640475)
      ·
        refine ⟨239653231273596071777460713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159768820849064047851640475 239653231273596071777460713)
        ·
          refine ⟨179739923455197053833095535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239653231273596071777460713 179739923455197053833095535)
          ·
            refine ⟨269609885182795580749643303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179739923455197053833095535 269609885182795580749643303)
            ·
              refine ⟨404414827774193371124464955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269609885182795580749643303 404414827774193371124464955)
              ·
                refine ⟨606622241661290056686697433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404414827774193371124464955 606622241661290056686697433)
                ·
                  refine ⟨454966681245967542515023075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606622241661290056686697433 454966681245967542515023075)
                  ·
                    refine ⟨682450021868951313772534613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 454966681245967542515023075 682450021868951313772534613)
                    ·
                      refine ⟨3998730596888386604135945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 682450021868951313772534613 3998730596888386604135945)
                      ·
                        rfl

theorem cell23_7787500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_7787500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787500 prefixEnd_7787500 := by exact prefixLift 7787500
  have htrace : WordTrace (prefixWord ++ tailWord_7787500) baseStart_7787500 baseEnd_7787500 := by
    simpa [prefixWord, tailWord_7787500, baseEnd_7787500] using wordTrace_append hprefix tailTrace_7787500
  have hstable : (prefixWord ++ tailWord_7787500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787500).length < 2 ^ (prefixWord ++ tailWord_7787500).sum := by decide
  have hdescent : baseEnd_7787500 < baseStart_7787500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787520 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 1, 11]
def baseStart_7787520 : Nat := 118140960795 + 7787520 * 2 ^ 59
def prefixEnd_7787520 : Nat := 4983230072969 + 3 ^ 40 * 7787520 * 2
def baseEnd_7787520 : Nat := 1332913622167158841961951

theorem tailTrace_7787520 : CollatzResearch.WordTrace tailWord_7787520 prefixEnd_7787520 1332913622167158841961951 := by
  unfold tailWord_7787520
  simp only [CollatzResearch.WordTrace]
  refine ⟨142017094373576258687100007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189356125831435011582800009 142017094373576258687100007)
  ·
    refine ⟨213025641560364388030650011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142017094373576258687100007 213025641560364388030650011)
    ·
      refine ⟨319538462340546582045975017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213025641560364388030650011 319538462340546582045975017)
      ·
        refine ⟨239653846755409936534481263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319538462340546582045975017 239653846755409936534481263)
        ·
          refine ⟨359480770133114904801721895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239653846755409936534481263 359480770133114904801721895)
          ·
            refine ⟨539221155199672357202582843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359480770133114904801721895 539221155199672357202582843)
            ·
              refine ⟨808831732799508535803874265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539221155199672357202582843 808831732799508535803874265)
              ·
                refine ⟨606623799599631401852905699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808831732799508535803874265 606623799599631401852905699)
                ·
                  refine ⟨909935699399447102779358549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 606623799599631401852905699 909935699399447102779358549)
                  ·
                    refine ⟨1332913622167158841961951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 909935699399447102779358549 1332913622167158841961951)
                    ·
                      rfl

theorem cell23_7787520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 11].length) (baseStart_7787520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787520 prefixEnd_7787520 := by exact prefixLift 7787520
  have htrace : WordTrace (prefixWord ++ tailWord_7787520) baseStart_7787520 baseEnd_7787520 := by
    simpa [prefixWord, tailWord_7787520, baseEnd_7787520] using wordTrace_append hprefix tailTrace_7787520
  have hstable : (prefixWord ++ tailWord_7787520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787520).length < 2 ^ (prefixWord ++ tailWord_7787520).sum := by decide
  have hdescent : baseEnd_7787520 < baseStart_7787520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787528 : List Nat := [2, 1, 3, 2, 1, 4, 3, 2, 1, 4]
def baseStart_7787528 : Nat := 118140960795 + 7787528 * 2 ^ 59
def prefixEnd_7787528 : Nat := 4983230072969 + 3 ^ 40 * 7787528 * 2
def baseEnd_7787528 : Nat := 1332914991448904164861939

theorem tailTrace_7787528 : CollatzResearch.WordTrace tailWord_7787528 prefixEnd_7787528 1332914991448904164861939 := by
  unfold tailWord_7787528
  simp only [CollatzResearch.WordTrace]
  refine ⟨142017240265561767370245619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189356320354082356493660825 142017240265561767370245619)
  ·
    refine ⟨213025860398342651055368429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142017240265561767370245619 213025860398342651055368429)
    ·
      refine ⟨79884697649378494145763161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213025860398342651055368429 79884697649378494145763161)
      ·
        refine ⟨59913523237033870609322371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79884697649378494145763161 59913523237033870609322371)
        ·
          refine ⟨89870284855550805913983557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59913523237033870609322371 89870284855550805913983557)
          ·
            refine ⟨16850678410415776108871917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89870284855550805913983557 16850678410415776108871917)
            ·
              refine ⟨6319004403905916040826969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16850678410415776108871917 6319004403905916040826969)
              ·
                refine ⟨4739253302929437030620227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6319004403905916040826969 4739253302929437030620227)
                ·
                  refine ⟨7108879954394155545930341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4739253302929437030620227 7108879954394155545930341)
                  ·
                    refine ⟨1332914991448904164861939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7108879954394155545930341 1332914991448904164861939)
                    ·
                      rfl

theorem cell23_7787528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_7787528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787528 prefixEnd_7787528 := by exact prefixLift 7787528
  have htrace : WordTrace (prefixWord ++ tailWord_7787528) baseStart_7787528 baseEnd_7787528 := by
    simpa [prefixWord, tailWord_7787528, baseEnd_7787528] using wordTrace_append hprefix tailTrace_7787528
  have hstable : (prefixWord ++ tailWord_7787528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787528).length < 2 ^ (prefixWord ++ tailWord_7787528).sum := by decide
  have hdescent : baseEnd_7787528 < baseStart_7787528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787541 : List Nat := [1, 3, 2, 1, 4, 3, 2, 1, 6]
def baseStart_7787541 : Nat := 118140960795 + 7787541 * 2 ^ 59
def prefixEnd_7787541 : Nat := 4983230072969 + 3 ^ 40 * 7787541 * 2
def baseEnd_7787541 : Nat := 444305738843913438191473

theorem tailTrace_7787541 : CollatzResearch.WordTrace tailWord_7787541 prefixEnd_7787541 444305738843913438191473 := by
  unfold tailWord_7787541
  simp only [CollatzResearch.WordTrace]
  refine ⟨284034954680076437960714477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189356636453384291973809651 284034954680076437960714477)
  ·
    refine ⟨106513108005028664235267929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284034954680076437960714477 106513108005028664235267929)
    ·
      refine ⟨79884831003771498176450947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106513108005028664235267929 79884831003771498176450947)
      ·
        refine ⟨119827246505657247264676421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79884831003771498176450947 119827246505657247264676421)
        ·
          refine ⟨22467608719810733862126829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119827246505657247264676421 22467608719810733862126829)
          ·
            refine ⟨8425353269929025198297561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22467608719810733862126829 8425353269929025198297561)
            ·
              refine ⟨6319014952446768898723171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8425353269929025198297561 6319014952446768898723171)
              ·
                refine ⟨9478522428670153348084757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6319014952446768898723171 9478522428670153348084757)
                ·
                  refine ⟨444305738843913438191473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9478522428670153348084757 444305738843913438191473)
                  ·
                    rfl

theorem cell23_7787541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 6].length) (baseStart_7787541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787541 prefixEnd_7787541 := by exact prefixLift 7787541
  have htrace : WordTrace (prefixWord ++ tailWord_7787541) baseStart_7787541 baseEnd_7787541 := by
    simpa [prefixWord, tailWord_7787541, baseEnd_7787541] using wordTrace_append hprefix tailTrace_7787541
  have hstable : (prefixWord ++ tailWord_7787541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787541).length < 2 ^ (prefixWord ++ tailWord_7787541).sum := by decide
  have hdescent : baseEnd_7787541 < baseStart_7787541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787554 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_7787554 : Nat := 118140960795 + 7787554 * 2 ^ 59
def prefixEnd_7787554 : Nat := 4983230072969 + 3 ^ 40 * 7787554 * 2
def baseEnd_7787554 : Nat := 1332919441614576464286899

theorem tailTrace_7787554 : CollatzResearch.WordTrace tailWord_7787554 prefixEnd_7787554 1332919441614576464286899 := by
  unfold tailWord_7787554
  simp only [CollatzResearch.WordTrace]
  refine ⟨71008857207257335295234429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189356952552686227453958477 71008857207257335295234429)
  ·
    refine ⟨26628321452721500735712911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71008857207257335295234429 26628321452721500735712911)
    ·
      refine ⟨39942482179082251103569367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26628321452721500735712911 39942482179082251103569367)
      ·
        refine ⟨59913723268623376655354051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39942482179082251103569367 59913723268623376655354051)
        ·
          refine ⟨89870584902935064983031077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59913723268623376655354051 89870584902935064983031077)
          ·
            refine ⟨16850734669300324684318327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89870584902935064983031077 16850734669300324684318327)
            ·
              refine ⟨25276102003950487026477491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16850734669300324684318327 25276102003950487026477491)
              ·
                refine ⟨37914153005925730539716237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25276102003950487026477491 37914153005925730539716237)
                ·
                  refine ⟨14217807377222148952393589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37914153005925730539716237 14217807377222148952393589)
                  ·
                    refine ⟨1332919441614576464286899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14217807377222148952393589 1332919441614576464286899)
                    ·
                      rfl

theorem cell23_7787554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_7787554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787554 prefixEnd_7787554 := by exact prefixLift 7787554
  have htrace : WordTrace (prefixWord ++ tailWord_7787554) baseStart_7787554 baseEnd_7787554 := by
    simpa [prefixWord, tailWord_7787554, baseEnd_7787554] using wordTrace_append hprefix tailTrace_7787554
  have hstable : (prefixWord ++ tailWord_7787554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787554).length < 2 ^ (prefixWord ++ tailWord_7787554).sum := by decide
  have hdescent : baseEnd_7787554 < baseStart_7787554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787585 : List Nat := [1, 2, 5, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_7787585 : Nat := 118140960795 + 7787585 * 2 ^ 59
def prefixEnd_7787585 : Nat := 4983230072969 + 3 ^ 40 * 7787585 * 2
def baseEnd_7787585 : Nat := 3998774242744018771573055

theorem tailTrace_7787585 : CollatzResearch.WordTrace tailWord_7787585 prefixEnd_7787585 3998774242744018771573055 := by
  unfold tailWord_7787585
  simp only [CollatzResearch.WordTrace]
  refine ⟨284036559491917033475316209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189357706327944688983544139 284036559491917033475316209)
  ·
    refine ⟨213027419618937775106487157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284036559491917033475316209 213027419618937775106487157)
    ·
      refine ⟨19971320589275416416233171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213027419618937775106487157 19971320589275416416233171)
      ·
        refine ⟨29956980883913124624349757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19971320589275416416233171 29956980883913124624349757)
        ·
          refine ⟨11233867831467421734131159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29956980883913124624349757 11233867831467421734131159)
          ·
            refine ⟨16850801747201132601196739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11233867831467421734131159 16850801747201132601196739)
            ·
              refine ⟨25276202620801698901795109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16850801747201132601196739 25276202620801698901795109)
              ·
                refine ⟨4739287991400318544086583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25276202620801698901795109 4739287991400318544086583)
                ·
                  refine ⟨7108931987100477816129875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4739287991400318544086583 7108931987100477816129875)
                  ·
                    refine ⟨10663397980650716724194813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7108931987100477816129875 10663397980650716724194813)
                    ·
                      refine ⟨3998774242744018771573055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10663397980650716724194813 3998774242744018771573055)
                      ·
                        rfl

theorem cell23_7787585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_7787585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787585 prefixEnd_7787585 := by exact prefixLift 7787585
  have htrace : WordTrace (prefixWord ++ tailWord_7787585) baseStart_7787585 baseEnd_7787585 := by
    simpa [prefixWord, tailWord_7787585, baseEnd_7787585] using wordTrace_append hprefix tailTrace_7787585
  have hstable : (prefixWord ++ tailWord_7787585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787585).length < 2 ^ (prefixWord ++ tailWord_7787585).sum := by decide
  have hdescent : baseEnd_7787585 < baseStart_7787585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787587 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 4]
def baseStart_7787587 : Nat := 118140960795 + 7787587 * 2 ^ 59
def prefixEnd_7787587 : Nat := 4983230072969 + 3 ^ 40 * 7787587 * 2
def baseEnd_7787587 : Nat := 3998775269705327763748045

theorem tailTrace_7787587 : CollatzResearch.WordTrace tailWord_7787587 prefixEnd_7787587 3998775269705327763748045 := by
  unfold tailWord_7787587
  simp only [CollatzResearch.WordTrace]
  refine ⟨284036632437909787816889015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189357754958606525211259343 284036632437909787816889015)
  ·
    refine ⟨426054948656864681725333523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284036632437909787816889015 426054948656864681725333523)
    ·
      refine ⟨639082422985297022588000285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426054948656864681725333523 639082422985297022588000285)
      ·
        refine ⟨239655908619486383470500107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 639082422985297022588000285 239655908619486383470500107)
        ·
          refine ⟨359483862929229575205750161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239655908619486383470500107 359483862929229575205750161)
          ·
            refine ⟨269612897196922181404312621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359483862929229575205750161 269612897196922181404312621)
            ·
              refine ⟨101104836448845818026617233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269612897196922181404312621 101104836448845818026617233)
              ·
                refine ⟨75828627336634363519962925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101104836448845818026617233 75828627336634363519962925)
                ·
                  refine ⟨28435735251237886319986097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75828627336634363519962925 28435735251237886319986097)
                  ·
                    refine ⟨21326801438428414739989573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28435735251237886319986097 21326801438428414739989573)
                    ·
                      refine ⟨3998775269705327763748045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21326801438428414739989573 3998775269705327763748045)
                      ·
                        rfl

theorem cell23_7787587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_7787587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787587 prefixEnd_7787587 := by exact prefixLift 7787587
  have htrace : WordTrace (prefixWord ++ tailWord_7787587) baseStart_7787587 baseEnd_7787587 := by
    simpa [prefixWord, tailWord_7787587, baseEnd_7787587] using wordTrace_append hprefix tailTrace_7787587
  have hstable : (prefixWord ++ tailWord_7787587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787587).length < 2 ^ (prefixWord ++ tailWord_7787587).sum := by decide
  have hdescent : baseEnd_7787587 < baseStart_7787587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787594 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 3, 2, 3]
def baseStart_7787594 : Nat := 118140960795 + 7787594 * 2 ^ 59
def prefixEnd_7787594 : Nat := 4983230072969 + 3 ^ 40 * 7787594 * 2
def baseEnd_7787594 : Nat := 3998778864069909236360513

theorem tailTrace_7787594 : CollatzResearch.WordTrace tailWord_7787594 prefixEnd_7787594 3998778864069909236360513 := by
  unfold tailWord_7787594
  simp only [CollatzResearch.WordTrace]
  refine ⟨71009221937221107003098459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189357925165922952008262557 71009221937221107003098459)
  ·
    refine ⟨106513832905831660504647689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71009221937221107003098459 106513832905831660504647689)
    ·
      refine ⟨79885374679373745378485767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106513832905831660504647689 79885374679373745378485767)
      ·
        refine ⟨119828062019060618067728651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79885374679373745378485767 119828062019060618067728651)
        ·
          refine ⟨179742093028590927101592977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119828062019060618067728651 179742093028590927101592977)
          ·
            refine ⟨134806569771443195326194733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179742093028590927101592977 134806569771443195326194733)
            ·
              refine ⟨50552463664291198247323025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134806569771443195326194733 50552463664291198247323025)
              ·
                refine ⟨37914347748218398685492269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50552463664291198247323025 37914347748218398685492269)
                ·
                  refine ⟨14217880405581899507059601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37914347748218398685492269 14217880405581899507059601)
                  ·
                    refine ⟨10663410304186424630294701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14217880405581899507059601 10663410304186424630294701)
                    ·
                      refine ⟨3998778864069909236360513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10663410304186424630294701 3998778864069909236360513)
                      ·
                        rfl

theorem cell23_7787594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_7787594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787594 prefixEnd_7787594 := by exact prefixLift 7787594
  have htrace : WordTrace (prefixWord ++ tailWord_7787594) baseStart_7787594 baseEnd_7787594 := by
    simpa [prefixWord, tailWord_7787594, baseEnd_7787594] using wordTrace_append hprefix tailTrace_7787594
  have hstable : (prefixWord ++ tailWord_7787594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787594).length < 2 ^ (prefixWord ++ tailWord_7787594).sum := by decide
  have hdescent : baseEnd_7787594 < baseStart_7787594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787604 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_7787604 : Nat := 118140960795 + 7787604 * 2 ^ 59
def prefixEnd_7787604 : Nat := 4983230072969 + 3 ^ 40 * 7787604 * 2
def baseEnd_7787604 : Nat := 3998783998876454197235467

theorem tailTrace_7787604 : CollatzResearch.WordTrace tailWord_7787604 prefixEnd_7787604 3998783998876454197235467 := by
  unfold tailWord_7787604
  simp only [CollatzResearch.WordTrace]
  refine ⟨142018626239424099860128933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189358168319232133146838577 142018626239424099860128933)
  ·
    refine ⟨26628492419892018723774175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142018626239424099860128933 26628492419892018723774175)
    ·
      refine ⟨39942738629838028085661263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26628492419892018723774175 39942738629838028085661263)
      ·
        refine ⟨59914107944757042128491895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39942738629838028085661263 59914107944757042128491895)
        ·
          refine ⟨89871161917135563192737843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59914107944757042128491895 89871161917135563192737843)
          ·
            refine ⟨134806742875703344789106765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89871161917135563192737843 134806742875703344789106765)
            ·
              refine ⟨50552528578388754295915037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134806742875703344789106765 50552528578388754295915037)
              ·
                refine ⟨18957198216895782860968139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50552528578388754295915037 18957198216895782860968139)
                ·
                  refine ⟨28435797325343674291452209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18957198216895782860968139 28435797325343674291452209)
                  ·
                    refine ⟨21326847994007755718589157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28435797325343674291452209 21326847994007755718589157)
                    ·
                      refine ⟨3998783998876454197235467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21326847994007755718589157 3998783998876454197235467)
                      ·
                        rfl

theorem cell23_7787604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_7787604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787604 prefixEnd_7787604 := by exact prefixLift 7787604
  have htrace : WordTrace (prefixWord ++ tailWord_7787604) baseStart_7787604 baseEnd_7787604 := by
    simpa [prefixWord, tailWord_7787604, baseEnd_7787604] using wordTrace_append hprefix tailTrace_7787604
  have hstable : (prefixWord ++ tailWord_7787604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787604).length < 2 ^ (prefixWord ++ tailWord_7787604).sum := by decide
  have hdescent : baseEnd_7787604 < baseStart_7787604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787625 : List Nat := [1, 2, 1, 1, 1, 7, 2, 3, 1, 2, 2]
def baseStart_7787625 : Nat := 118140960795 + 7787625 * 2 ^ 59
def prefixEnd_7787625 : Nat := 4983230072969 + 3 ^ 40 * 7787625 * 2
def baseEnd_7787625 : Nat := 3998794781970198615072871

theorem tailTrace_7787625 : CollatzResearch.WordTrace tailWord_7787625 prefixEnd_7787625 3998794781970198615072871 := by
  unfold tailWord_7787625
  simp only [CollatzResearch.WordTrace]
  refine ⟨284038018411772120306772329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189358678941181413537848219 284038018411772120306772329)
  ·
    refine ⟨213028513808829090230079247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284038018411772120306772329 213028513808829090230079247)
    ·
      refine ⟨319542770713243635345118871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213028513808829090230079247 319542770713243635345118871)
      ·
        refine ⟨479314156069865453017678307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319542770713243635345118871 479314156069865453017678307)
        ·
          refine ⟨718971234104798179526517461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479314156069865453017678307 718971234104798179526517461)
          ·
            refine ⟨16850888299331207332652753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 718971234104798179526517461 16850888299331207332652753)
            ·
              refine ⟨12638166224498405499489565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16850888299331207332652753 12638166224498405499489565)
              ·
                refine ⟨4739312334186902062308587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12638166224498405499489565 4739312334186902062308587)
                ·
                  refine ⟨7108968501280353093462881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4739312334186902062308587 7108968501280353093462881)
                  ·
                    refine ⟨5331726375960264820097161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7108968501280353093462881 5331726375960264820097161)
                    ·
                      refine ⟨3998794781970198615072871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5331726375960264820097161 3998794781970198615072871)
                      ·
                        rfl

theorem cell23_7787625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 1, 2, 2].length) (baseStart_7787625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787625 prefixEnd_7787625 := by exact prefixLift 7787625
  have htrace : WordTrace (prefixWord ++ tailWord_7787625) baseStart_7787625 baseEnd_7787625 := by
    simpa [prefixWord, tailWord_7787625, baseEnd_7787625] using wordTrace_append hprefix tailTrace_7787625
  have hstable : (prefixWord ++ tailWord_7787625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787625).length < 2 ^ (prefixWord ++ tailWord_7787625).sum := by decide
  have hdescent : baseEnd_7787625 < baseStart_7787625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787681 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 3, 4, 2]
def baseStart_7787681 : Nat := 118140960795 + 7787681 * 2 ^ 59
def prefixEnd_7787681 : Nat := 4983230072969 + 3 ^ 40 * 7787681 * 2
def baseEnd_7787681 : Nat := 3998823536886850395972613

theorem tailTrace_7787681 : CollatzResearch.WordTrace tailWord_7787681 prefixEnd_7787681 3998823536886850395972613 := by
  unfold tailWord_7787681
  simp only [CollatzResearch.WordTrace]
  refine ⟨284040060899569241870810897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189360040599712827913873931 284040060899569241870810897)
  ·
    refine ⟨213030045674676931403108173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284040060899569241870810897 213030045674676931403108173)
    ·
      refine ⟨79886267128003849276165565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213030045674676931403108173 79886267128003849276165565)
      ·
        refine ⟨29957350173001443478562087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79886267128003849276165565 29957350173001443478562087)
        ·
          refine ⟨44936025259502165217843131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29957350173001443478562087 44936025259502165217843131)
          ·
            refine ⟨67404037889253247826764697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44936025259502165217843131 67404037889253247826764697)
            ·
              refine ⟨50553028416939935870073523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67404037889253247826764697 50553028416939935870073523)
              ·
                refine ⟨75829542625409903805110285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50553028416939935870073523 75829542625409903805110285)
                ·
                  refine ⟨28436078484528713926916357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75829542625409903805110285 28436078484528713926916357)
                  ·
                    refine ⟨5331764715849133861296817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28436078484528713926916357 5331764715849133861296817)
                    ·
                      refine ⟨3998823536886850395972613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5331764715849133861296817 3998823536886850395972613)
                      ·
                        rfl

theorem cell23_7787681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_7787681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787681 prefixEnd_7787681 := by exact prefixLift 7787681
  have htrace : WordTrace (prefixWord ++ tailWord_7787681) baseStart_7787681 baseEnd_7787681 := by
    simpa [prefixWord, tailWord_7787681, baseEnd_7787681] using wordTrace_append hprefix tailTrace_7787681
  have hstable : (prefixWord ++ tailWord_7787681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787681).length < 2 ^ (prefixWord ++ tailWord_7787681).sum := by decide
  have hdescent : baseEnd_7787681 < baseStart_7787681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787684 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_7787684 : Nat := 118140960795 + 7787684 * 2 ^ 59
def prefixEnd_7787684 : Nat := 4983230072969 + 3 ^ 40 * 7787684 * 2
def baseEnd_7787684 : Nat := 3998825077328813884235099

theorem tailTrace_7787684 : CollatzResearch.WordTrace tailWord_7787684 prefixEnd_7787684 3998825077328813884235099 := by
  unfold tailWord_7787684
  simp only [CollatzResearch.WordTrace]
  refine ⟨142020085159279186691585053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189360113545705582255446737 142020085159279186691585053)
  ·
    refine ⟨53257531934729695009344395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142020085159279186691585053 53257531934729695009344395)
    ·
      refine ⟨79886297902094542514016593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53257531934729695009344395 79886297902094542514016593)
      ·
        refine ⟨59914723426570906885512445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79886297902094542514016593 59914723426570906885512445)
        ·
          refine ⟨22468021284964090082067167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59914723426570906885512445 22468021284964090082067167)
          ·
            refine ⟨33702031927446135123100751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22468021284964090082067167 33702031927446135123100751)
            ·
              refine ⟨50553047891169202684651127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33702031927446135123100751 50553047891169202684651127)
              ·
                refine ⟨75829571836753804026976691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50553047891169202684651127 75829571836753804026976691)
                ·
                  refine ⟨113744357755130706040465037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75829571836753804026976691 113744357755130706040465037)
                  ·
                    refine ⟨42654134158174014765174389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113744357755130706040465037 42654134158174014765174389)
                    ·
                      refine ⟨3998825077328813884235099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42654134158174014765174389 3998825077328813884235099)
                      ·
                        rfl

theorem cell23_7787684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_7787684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787684 prefixEnd_7787684 := by exact prefixLift 7787684
  have htrace : WordTrace (prefixWord ++ tailWord_7787684) baseStart_7787684 baseEnd_7787684 := by
    simpa [prefixWord, tailWord_7787684, baseEnd_7787684] using wordTrace_append hprefix tailTrace_7787684
  have hstable : (prefixWord ++ tailWord_7787684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787684).length < 2 ^ (prefixWord ++ tailWord_7787684).sum := by decide
  have hdescent : baseEnd_7787684 < baseStart_7787684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787698 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2]
def baseStart_7787698 : Nat := 118140960795 + 7787698 * 2 ^ 59
def prefixEnd_7787698 : Nat := 4983230072969 + 3 ^ 40 * 7787698 * 2
def baseEnd_7787698 : Nat := 3998832266057976829460035

theorem tailTrace_7787698 : CollatzResearch.WordTrace tailWord_7787698 prefixEnd_7787698 3998832266057976829460035 := by
  unfold tailWord_7787698
  simp only [CollatzResearch.WordTrace]
  refine ⟨71010170235126913443544937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189360453960338435849453165 71010170235126913443544937)
  ·
    refine ⟨53257627676345185082658703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71010170235126913443544937 53257627676345185082658703)
    ·
      refine ⟨79886441514517777623988055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53257627676345185082658703 79886441514517777623988055)
      ·
        refine ⟨119829662271776666435982083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79886441514517777623988055 119829662271776666435982083)
        ·
          refine ⟨179744493407664999653973125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119829662271776666435982083 179744493407664999653973125)
          ·
            refine ⟨33702092513937187435119961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179744493407664999653973125 33702092513937187435119961)
            ·
              refine ⟨25276569385452890576339971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33702092513937187435119961 25276569385452890576339971)
              ·
                refine ⟨37914854078179335864509957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25276569385452890576339971 37914854078179335864509957)
                ·
                  refine ⟨7109035139658625474595617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37914854078179335864509957 7109035139658625474595617)
                  ·
                    refine ⟨5331776354743969105946713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7109035139658625474595617 5331776354743969105946713)
                    ·
                      refine ⟨3998832266057976829460035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5331776354743969105946713 3998832266057976829460035)
                      ·
                        rfl

theorem cell23_7787698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_7787698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787698 prefixEnd_7787698 := by exact prefixLift 7787698
  have htrace : WordTrace (prefixWord ++ tailWord_7787698) baseStart_7787698 baseEnd_7787698 := by
    simpa [prefixWord, tailWord_7787698, baseEnd_7787698] using wordTrace_append hprefix tailTrace_7787698
  have hstable : (prefixWord ++ tailWord_7787698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787698).length < 2 ^ (prefixWord ++ tailWord_7787698).sum := by decide
  have hdescent : baseEnd_7787698 < baseStart_7787698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787707 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 8]
def baseStart_7787707 : Nat := 118140960795 + 7787707 * 2 ^ 59
def prefixEnd_7787707 : Nat := 4983230072969 + 3 ^ 40 * 7787707 * 2
def baseEnd_7787707 : Nat := 3998836887383867294247493

theorem tailTrace_7787707 : CollatzResearch.WordTrace tailWord_7787707 prefixEnd_7787707 3998836887383867294247493 := by
  unfold tailWord_7787707
  simp only [CollatzResearch.WordTrace]
  refine ⟨284041009197475048311257375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189360672798316698874171583 284041009197475048311257375)
  ·
    refine ⟨426061513796212572466886063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284041009197475048311257375 426061513796212572466886063)
    ·
      refine ⟨639092270694318858700329095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426061513796212572466886063 639092270694318858700329095)
      ·
        refine ⟨958638406041478288050493643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639092270694318858700329095 958638406041478288050493643)
        ·
          refine ⟨1437957609062217432075740465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958638406041478288050493643 1437957609062217432075740465)
          ·
            refine ⟨1078468206796663074056805349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1437957609062217432075740465 1078468206796663074056805349)
            ·
              refine ⟨202212788774374326385651003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1078468206796663074056805349 202212788774374326385651003)
              ·
                refine ⟨303319183161561489578476505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202212788774374326385651003 303319183161561489578476505)
                ·
                  refine ⟨227489387371171117183857379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303319183161561489578476505 227489387371171117183857379)
                  ·
                    refine ⟨341234081056756675775786069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 227489387371171117183857379 341234081056756675775786069)
                    ·
                      refine ⟨3998836887383867294247493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 341234081056756675775786069 3998836887383867294247493)
                      ·
                        rfl

theorem cell23_7787707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 8].length) (baseStart_7787707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787707 prefixEnd_7787707 := by exact prefixLift 7787707
  have htrace : WordTrace (prefixWord ++ tailWord_7787707) baseStart_7787707 baseEnd_7787707 := by
    simpa [prefixWord, tailWord_7787707, baseEnd_7787707] using wordTrace_append hprefix tailTrace_7787707
  have hstable : (prefixWord ++ tailWord_7787707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787707).length < 2 ^ (prefixWord ++ tailWord_7787707).sum := by decide
  have hdescent : baseEnd_7787707 < baseStart_7787707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787744 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 5]
def baseStart_7787744 : Nat := 118140960795 + 7787744 * 2 ^ 59
def prefixEnd_7787744 : Nat := 4983230072969 + 3 ^ 40 * 7787744 * 2
def baseEnd_7787744 : Nat := 3998855886168083649484823

theorem tailTrace_7787744 : CollatzResearch.WordTrace tailWord_7787744 prefixEnd_7787744 3998855886168083649484823 := by
  unfold tailWord_7787744
  simp only [CollatzResearch.WordTrace]
  refine ⟨142021179349170501815177143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189361572465560669086902857 142021179349170501815177143)
  ·
    refine ⟨213031769023755752722765715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142021179349170501815177143 213031769023755752722765715)
    ·
      refine ⟨319547653535633629084148573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213031769023755752722765715 319547653535633629084148573)
      ·
        refine ⟨119830370075862610906555715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319547653535633629084148573 119830370075862610906555715)
        ·
          refine ⟨179745555113793916359833573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119830370075862610906555715 179745555113793916359833573)
          ·
            refine ⟨33702291583836359317468795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179745555113793916359833573 33702291583836359317468795)
            ·
              refine ⟨50553437375754538976203193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33702291583836359317468795 50553437375754538976203193)
              ·
                refine ⟨37915078031815904232152395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50553437375754538976203193 37915078031815904232152395)
                ·
                  refine ⟨56872617047723856348228593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37915078031815904232152395 56872617047723856348228593)
                  ·
                    refine ⟨42654462785792892261171445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56872617047723856348228593 42654462785792892261171445)
                    ·
                      refine ⟨3998855886168083649484823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42654462785792892261171445 3998855886168083649484823)
                      ·
                        rfl

theorem cell23_7787744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_7787744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787744 prefixEnd_7787744 := by exact prefixLift 7787744
  have htrace : WordTrace (prefixWord ++ tailWord_7787744) baseStart_7787744 baseEnd_7787744 := by
    simpa [prefixWord, tailWord_7787744, baseEnd_7787744] using wordTrace_append hprefix tailTrace_7787744
  have hstable : (prefixWord ++ tailWord_7787744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787744).length < 2 ^ (prefixWord ++ tailWord_7787744).sum := by decide
  have hdescent : baseEnd_7787744 < baseStart_7787744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787781 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 3, 4]
def baseStart_7787781 : Nat := 118140960795 + 7787781 * 2 ^ 59
def prefixEnd_7787781 : Nat := 4983230072969 + 3 ^ 40 * 7787781 * 2
def baseEnd_7787781 : Nat := 1332958294984100001574051

theorem tailTrace_7787781 : CollatzResearch.WordTrace tailWord_7787781 prefixEnd_7787781 1332958294984100001574051 := by
  unfold tailWord_7787781
  simp only [CollatzResearch.WordTrace]
  refine ⟨284043708199206958949451197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189362472132804639299634131 284043708199206958949451197)
  ·
    refine ⟨106516390574702609606044199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284043708199206958949451197 106516390574702609606044199)
    ·
      refine ⟨159774585862053914409066299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106516390574702609606044199 159774585862053914409066299)
      ·
        refine ⟨239661878793080871613599449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159774585862053914409066299 239661878793080871613599449)
        ·
          refine ⟨179746409094810653710199587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239661878793080871613599449 179746409094810653710199587)
          ·
            refine ⟨269619613642215980565299381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179746409094810653710199587 269619613642215980565299381)
            ·
              refine ⟨25276838778957748177996817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269619613642215980565299381 25276838778957748177996817)
              ·
                refine ⟨18957629084218311133497613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25276838778957748177996817 18957629084218311133497613)
                ·
                  refine ⟨7109110906581866675061605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18957629084218311133497613 7109110906581866675061605)
                  ·
                    refine ⟨1332958294984100001574051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7109110906581866675061605 1332958294984100001574051)
                    ·
                      rfl

theorem cell23_7787781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_7787781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787781 prefixEnd_7787781 := by exact prefixLift 7787781
  have htrace : WordTrace (prefixWord ++ tailWord_7787781) baseStart_7787781 baseEnd_7787781 := by
    simpa [prefixWord, tailWord_7787781, baseEnd_7787781] using wordTrace_append hprefix tailTrace_7787781
  have hstable : (prefixWord ++ tailWord_7787781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787781).length < 2 ^ (prefixWord ++ tailWord_7787781).sum := by decide
  have hdescent : baseEnd_7787781 < baseStart_7787781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787788 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 2, 1, 4]
def baseStart_7787788 : Nat := 118140960795 + 7787788 * 2 ^ 59
def prefixEnd_7787788 : Nat := 4983230072969 + 3 ^ 40 * 7787788 * 2
def baseEnd_7787788 : Nat := 3998878479316881477334621

theorem tailTrace_7787788 : CollatzResearch.WordTrace tailWord_7787788 prefixEnd_7787788 3998878479316881477334621 := by
  unfold tailWord_7787788
  simp only [CollatzResearch.WordTrace]
  refine ⟨142021981755090799572478009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189362642340121066096637345 142021981755090799572478009)
  ·
    refine ⟨106516486316318099679358507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142021981755090799572478009 106516486316318099679358507)
    ·
      refine ⟨159774729474477149519037761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106516486316318099679358507 159774729474477149519037761)
      ·
        refine ⟨119831047105857862139278321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159774729474477149519037761 119831047105857862139278321)
        ·
          refine ⟨89873285329393396604458741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119831047105857862139278321 89873285329393396604458741)
          ·
            refine ⟨8425620499630630931668007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89873285329393396604458741 8425620499630630931668007)
            ·
              refine ⟨12638430749445946397502011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8425620499630630931668007 12638430749445946397502011)
              ·
                refine ⟨18957646124168919596253017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12638430749445946397502011 18957646124168919596253017)
                ·
                  refine ⟨14218234593126689697189763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18957646124168919596253017 14218234593126689697189763)
                  ·
                    refine ⟨21327351889690034545784645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14218234593126689697189763 21327351889690034545784645)
                    ·
                      refine ⟨3998878479316881477334621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21327351889690034545784645 3998878479316881477334621)
                      ·
                        rfl

theorem cell23_7787788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_7787788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787788 prefixEnd_7787788 := by exact prefixLift 7787788
  have htrace : WordTrace (prefixWord ++ tailWord_7787788) baseStart_7787788 baseEnd_7787788 := by
    simpa [prefixWord, tailWord_7787788, baseEnd_7787788] using wordTrace_append hprefix tailTrace_7787788
  have hstable : (prefixWord ++ tailWord_7787788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787788).length < 2 ^ (prefixWord ++ tailWord_7787788).sum := by decide
  have hdescent : baseEnd_7787788 < baseStart_7787788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787811 : List Nat := [1, 1, 1, 4, 2, 3, 3, 2, 6]
def baseStart_7787811 : Nat := 118140960795 + 7787811 * 2 ^ 59
def prefixEnd_7787811 : Nat := 4983230072969 + 3 ^ 40 * 7787811 * 2
def baseEnd_7787811 : Nat := 444321143263548320816335

theorem tailTrace_7787811 : CollatzResearch.WordTrace tailWord_7787811 prefixEnd_7787811 444321143263548320816335 := by
  unfold tailWord_7787811
  simp only [CollatzResearch.WordTrace]
  refine ⟨284044802389098274073043287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189363201592732182715362191 284044802389098274073043287)
  ·
    refine ⟨426067203583647411109564931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284044802389098274073043287 426067203583647411109564931)
    ·
      refine ⟨639100805375471116664347397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426067203583647411109564931 639100805375471116664347397)
      ·
        refine ⟨119831401007900834374565137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 639100805375471116664347397 119831401007900834374565137)
        ·
          refine ⟨89873550755925625780923853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119831401007900834374565137 89873550755925625780923853)
          ·
            refine ⟨33702581533472109667846445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89873550755925625780923853 33702581533472109667846445)
            ·
              refine ⟨12638468075052041125442417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33702581533472109667846445 12638468075052041125442417)
              ·
                refine ⟨9478851056289030844081813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12638468075052041125442417 9478851056289030844081813)
                ·
                  refine ⟨444321143263548320816335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9478851056289030844081813 444321143263548320816335)
                  ·
                    rfl

theorem cell23_7787811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 6].length) (baseStart_7787811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787811 prefixEnd_7787811 := by exact prefixLift 7787811
  have htrace : WordTrace (prefixWord ++ tailWord_7787811) baseStart_7787811 baseEnd_7787811 := by
    simpa [prefixWord, tailWord_7787811, baseEnd_7787811] using wordTrace_append hprefix tailTrace_7787811
  have hstable : (prefixWord ++ tailWord_7787811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787811).length < 2 ^ (prefixWord ++ tailWord_7787811).sum := by decide
  have hdescent : baseEnd_7787811 < baseStart_7787811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787848 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 2, 3, 2]
def baseStart_7787848 : Nat := 118140960795 + 7787848 * 2 ^ 59
def prefixEnd_7787848 : Nat := 4983230072969 + 3 ^ 40 * 7787848 * 2
def baseEnd_7787848 : Nat := 3998909288156151242584345

theorem tailTrace_7787848 : CollatzResearch.WordTrace tailWord_7787848 prefixEnd_7787848 3998909288156151242584345 := by
  unfold tailWord_7787848
  simp only [CollatzResearch.WordTrace]
  refine ⟨142023075944982114696070099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189364101259976152928093465 142023075944982114696070099)
  ·
    refine ⟨213034613917473172044105149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142023075944982114696070099 213034613917473172044105149)
    ·
      refine ⟨79887980219052439516539431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213034613917473172044105149 79887980219052439516539431)
      ·
        refine ⟨119831970328578659274809147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79887980219052439516539431 119831970328578659274809147)
        ·
          refine ⟨179747955492867988912213721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119831970328578659274809147 179747955492867988912213721)
          ·
            refine ⟨134810966619650991684160291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179747955492867988912213721 134810966619650991684160291)
            ·
              refine ⟨202216449929476487526240437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134810966619650991684160291 202216449929476487526240437)
              ·
                refine ⟨18957792180888420705585041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202216449929476487526240437 18957792180888420705585041)
                ·
                  refine ⟨14218344135666315529188781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18957792180888420705585041 14218344135666315529188781)
                  ·
                    refine ⟨5331879050874868323445793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14218344135666315529188781 5331879050874868323445793)
                    ·
                      refine ⟨3998909288156151242584345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5331879050874868323445793 3998909288156151242584345)
                      ·
                        rfl

theorem cell23_7787848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_7787848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787848 prefixEnd_7787848 := by exact prefixLift 7787848
  have htrace : WordTrace (prefixWord ++ tailWord_7787848) baseStart_7787848 baseEnd_7787848 := by
    simpa [prefixWord, tailWord_7787848, baseEnd_7787848] using wordTrace_append hprefix tailTrace_7787848
  have hstable : (prefixWord ++ tailWord_7787848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787848).length < 2 ^ (prefixWord ++ tailWord_7787848).sum := by decide
  have hdescent : baseEnd_7787848 < baseStart_7787848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7787888 : List Nat := [2, 1, 1, 1, 4, 2, 3, 3, 2, 4]
def baseStart_7787888 : Nat := 118140960795 + 7787888 * 2 ^ 59
def prefixEnd_7787888 : Nat := 4983230072969 + 3 ^ 40 * 7787888 * 2
def baseEnd_7787888 : Nat := 1332976609127443695361387

theorem tailTrace_7787888 : CollatzResearch.WordTrace tailWord_7787888 prefixEnd_7787888 1332976609127443695361387 := by
  unfold tailWord_7787888
  simp only [CollatzResearch.WordTrace]
  refine ⟨142023805404909658111798159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189365073873212877482397545 142023805404909658111798159)
  ·
    refine ⟨213035708107364487167697239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142023805404909658111798159 213035708107364487167697239)
    ·
      refine ⟨319553562161046730751545859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213035708107364487167697239 319553562161046730751545859)
      ·
        refine ⟨479330343241570096127318789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319553562161046730751545859 479330343241570096127318789)
        ·
          refine ⟨89874439357794393023872273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 479330343241570096127318789 89874439357794393023872273)
          ·
            refine ⟨67405829518345794767904205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89874439357794393023872273 67405829518345794767904205)
            ·
              refine ⟨25277186069379673037964077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67405829518345794767904205 25277186069379673037964077)
              ·
                refine ⟨9478944776017377389236529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25277186069379673037964077 9478944776017377389236529)
                ·
                  refine ⟨7109208582013033041927397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9478944776017377389236529 7109208582013033041927397)
                  ·
                    refine ⟨1332976609127443695361387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7109208582013033041927397 1332976609127443695361387)
                    ·
                      rfl

theorem cell23_7787888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 2, 4].length) (baseStart_7787888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7787888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7787888 prefixEnd_7787888 := by exact prefixLift 7787888
  have htrace : WordTrace (prefixWord ++ tailWord_7787888) baseStart_7787888 baseEnd_7787888 := by
    simpa [prefixWord, tailWord_7787888, baseEnd_7787888] using wordTrace_append hprefix tailTrace_7787888
  have hstable : (prefixWord ++ tailWord_7787888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7787888).length < 2 ^ (prefixWord ++ tailWord_7787888).sum := by decide
  have hdescent : baseEnd_7787888 < baseStart_7787888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7787888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
