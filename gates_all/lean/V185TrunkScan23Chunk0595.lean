import V185TrunkScan23Chunk0594

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3517732 : List Nat := [2, 3, 1, 3, 1, 1, 1, 6, 5]
def baseStart_3517732 : Nat := 118140960795 + 3517732 * 2 ^ 59
def prefixEnd_3517732 : Nat := 4983230072969 + 3 ^ 40 * 3517732 * 2
def baseEnd_3517732 : Nat := 200698592189104010119139

theorem tailTrace_3517732 : CollatzResearch.WordTrace tailWord_3517732 prefixEnd_3517732 200698592189104010119139 := by
  unfold tailWord_3517732
  simp only [CollatzResearch.WordTrace]
  refine ⟨64151113245932609820053725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85534817661243479760071633 64151113245932609820053725)
  ·
    refine ⟨24056667467224728682520147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64151113245932609820053725 24056667467224728682520147)
    ·
      refine ⟨36085001200837093023780221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24056667467224728682520147 36085001200837093023780221)
      ·
        refine ⟨13531875450313909883917583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36085001200837093023780221 13531875450313909883917583)
        ·
          refine ⟨20297813175470864825876375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13531875450313909883917583 20297813175470864825876375)
          ·
            refine ⟨30446719763206297238814563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20297813175470864825876375 30446719763206297238814563)
            ·
              refine ⟨45670079644809445858221845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30446719763206297238814563 45670079644809445858221845)
              ·
                refine ⟨2140784983350442774604149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45670079644809445858221845 2140784983350442774604149)
                ·
                  refine ⟨200698592189104010119139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2140784983350442774604149 200698592189104010119139)
                  ·
                    rfl

theorem cell23_3517732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_3517732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517732 prefixEnd_3517732 := by exact prefixLift 3517732
  have htrace : WordTrace (prefixWord ++ tailWord_3517732) baseStart_3517732 baseEnd_3517732 := by
    simpa [prefixWord, tailWord_3517732, baseEnd_3517732] using wordTrace_append hprefix tailTrace_3517732
  have hstable : (prefixWord ++ tailWord_3517732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517732).length < 2 ^ (prefixWord ++ tailWord_3517732).sum := by decide
  have hdescent : baseEnd_3517732 < baseStart_3517732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517745 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 1, 7]
def baseStart_3517745 : Nat := 118140960795 + 3517745 * 2 ^ 59
def prefixEnd_3517745 : Nat := 4983230072969 + 3 ^ 40 * 3517745 * 2
def baseEnd_3517745 : Nat := 602098001650148180069897

theorem tailTrace_3517745 : CollatzResearch.WordTrace tailWord_3517745 prefixEnd_3517745 602098001650148180069897 := by
  unfold tailWord_3517745
  simp only [CollatzResearch.WordTrace]
  refine ⟨128302700640818122860330689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85535133760545415240220459 128302700640818122860330689)
  ·
    refine ⟨96227025480613592145248017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128302700640818122860330689 96227025480613592145248017)
    ·
      refine ⟨72170269110460194108936013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96227025480613592145248017 72170269110460194108936013)
      ·
        refine ⟨27063850916422572790851005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72170269110460194108936013 27063850916422572790851005)
        ·
          refine ⟨10148944093658464796569127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27063850916422572790851005 10148944093658464796569127)
          ·
            refine ⟨15223416140487697194853691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10148944093658464796569127 15223416140487697194853691)
            ·
              refine ⟨22835124210731545792280537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15223416140487697194853691 22835124210731545792280537)
              ·
                refine ⟨17126343158048659344210403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22835124210731545792280537 17126343158048659344210403)
                ·
                  refine ⟨25689514737072989016315605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17126343158048659344210403 25689514737072989016315605)
                  ·
                    refine ⟨602098001650148180069897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25689514737072989016315605 602098001650148180069897)
                    ·
                      rfl

theorem cell23_3517745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_3517745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517745 prefixEnd_3517745 := by exact prefixLift 3517745
  have htrace : WordTrace (prefixWord ++ tailWord_3517745) baseStart_3517745 baseEnd_3517745 := by
    simpa [prefixWord, tailWord_3517745, baseEnd_3517745] using wordTrace_append hprefix tailTrace_3517745
  have hstable : (prefixWord ++ tailWord_3517745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517745).length < 2 ^ (prefixWord ++ tailWord_3517745).sum := by decide
  have hdescent : baseEnd_3517745 < baseStart_3517745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517765 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 6, 1, 4]
def baseStart_3517765 : Nat := 118140960795 + 3517765 * 2 ^ 59
def prefixEnd_3517765 : Nat := 4983230072969 + 3 ^ 40 * 3517765 * 2
def baseEnd_3517765 : Nat := 1806304274563534461959599

theorem tailTrace_3517765 : CollatzResearch.WordTrace tailWord_3517765 prefixEnd_3517765 1806304274563534461959599 := by
  unfold tailWord_3517765
  simp only [CollatzResearch.WordTrace]
  refine ⟨128303430100745666276058749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85535620067163777517372499 128303430100745666276058749)
  ·
    refine ⟨48113786287779624853522031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128303430100745666276058749 48113786287779624853522031)
    ·
      refine ⟨72170679431669437280283047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48113786287779624853522031 72170679431669437280283047)
      ·
        refine ⟨108256019147504155920424571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72170679431669437280283047 108256019147504155920424571)
        ·
          refine ⟨162384028721256233880636857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108256019147504155920424571 162384028721256233880636857)
          ·
            refine ⟨121788021540942175410477643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162384028721256233880636857 121788021540942175410477643)
            ·
              refine ⟨182682032311413263115716465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121788021540942175410477643 182682032311413263115716465)
              ·
                refine ⟨137011524233559947336787349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182682032311413263115716465 137011524233559947336787349)
                ·
                  refine ⟨6422415198448122531411907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137011524233559947336787349 6422415198448122531411907)
                  ·
                    refine ⟨9633622797672183797117861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6422415198448122531411907 9633622797672183797117861)
                    ·
                      refine ⟨1806304274563534461959599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9633622797672183797117861 1806304274563534461959599)
                      ·
                        rfl

theorem cell23_3517765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_3517765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517765 prefixEnd_3517765 := by exact prefixLift 3517765
  have htrace : WordTrace (prefixWord ++ tailWord_3517765) baseStart_3517765 baseEnd_3517765 := by
    simpa [prefixWord, tailWord_3517765, baseEnd_3517765] using wordTrace_append hprefix tailTrace_3517765
  have hstable : (prefixWord ++ tailWord_3517765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517765).length < 2 ^ (prefixWord ++ tailWord_3517765).sum := by decide
  have hdescent : baseEnd_3517765 < baseStart_3517765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517869 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_3517869 : Nat := 118140960795 + 3517869 * 2 ^ 59
def prefixEnd_3517869 : Nat := 4983230072969 + 3 ^ 40 * 3517869 * 2
def baseEnd_3517869 : Nat := 602119225517200685019707

theorem tailTrace_3517869 : CollatzResearch.WordTrace tailWord_3517869 prefixEnd_3517869 602119225517200685019707 := by
  unfold tailWord_3517869
  simp only [CollatzResearch.WordTrace]
  refine ⟨128307223292368892037844661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85538148861579261358563107 128307223292368892037844661)
  ·
    refine ⟨12028802183659583628547937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128307223292368892037844661 12028802183659583628547937)
    ·
      refine ⟨9021601637744687721410953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12028802183659583628547937 9021601637744687721410953)
      ·
        refine ⟨6766201228308515791058215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9021601637744687721410953 6766201228308515791058215)
        ·
          refine ⟨10149301842462773686587323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6766201228308515791058215 10149301842462773686587323)
          ·
            refine ⟨15223952763694160529880985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10149301842462773686587323 15223952763694160529880985)
            ·
              refine ⟨11417964572770620397410739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15223952763694160529880985 11417964572770620397410739)
              ·
                refine ⟨17126946859155930596116109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11417964572770620397410739 17126946859155930596116109)
                ·
                  refine ⟨6422605072183473973543541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17126946859155930596116109 6422605072183473973543541)
                  ·
                    refine ⟨602119225517200685019707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6422605072183473973543541 602119225517200685019707)
                    ·
                      rfl

theorem cell23_3517869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_3517869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517869 prefixEnd_3517869 := by exact prefixLift 3517869
  have htrace : WordTrace (prefixWord ++ tailWord_3517869) baseStart_3517869 baseEnd_3517869 := by
    simpa [prefixWord, tailWord_3517869, baseEnd_3517869] using wordTrace_append hprefix tailTrace_3517869
  have hstable : (prefixWord ++ tailWord_3517869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517869).length < 2 ^ (prefixWord ++ tailWord_3517869).sum := by decide
  have hdescent : baseEnd_3517869 < baseStart_3517869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517872 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 1, 8, 2]
def baseStart_3517872 : Nat := 118140960795 + 3517872 * 2 ^ 59
def prefixEnd_3517872 : Nat := 4983230072969 + 3 ^ 40 * 3517872 * 2
def baseEnd_3517872 : Nat := 1806359216993565543321607

theorem tailTrace_3517872 : CollatzResearch.WordTrace tailWord_3517872 prefixEnd_3517872 1806359216993565543321607 := by
  unfold tailWord_3517872
  simp only [CollatzResearch.WordTrace]
  refine ⟨64153666355679011775101935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85538221807572015700135913 64153666355679011775101935)
  ·
    refine ⟨96230499533518517662652903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64153666355679011775101935 96230499533518517662652903)
    ·
      refine ⟨144345749300277776493979355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96230499533518517662652903 144345749300277776493979355)
      ·
        refine ⟨216518623950416664740969033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144345749300277776493979355 216518623950416664740969033)
        ·
          refine ⟨162388967962812498555726775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216518623950416664740969033 162388967962812498555726775)
          ·
            refine ⟨243583451944218747833590163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162388967962812498555726775 243583451944218747833590163)
            ·
              refine ⟨365375177916328121750385245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243583451944218747833590163 365375177916328121750385245)
              ·
                refine ⟨137015691718623045656394467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365375177916328121750385245 137015691718623045656394467)
                ·
                  refine ⟨205523537577934568484591701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137015691718623045656394467 205523537577934568484591701)
                  ·
                    refine ⟨2408478955991420724428809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 205523537577934568484591701 2408478955991420724428809)
                    ·
                      refine ⟨1806359216993565543321607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2408478955991420724428809 1806359216993565543321607)
                      ·
                        rfl

theorem cell23_3517872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 8, 2].length) (baseStart_3517872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517872 prefixEnd_3517872 := by exact prefixLift 3517872
  have htrace : WordTrace (prefixWord ++ tailWord_3517872) baseStart_3517872 baseEnd_3517872 := by
    simpa [prefixWord, tailWord_3517872, baseEnd_3517872] using wordTrace_append hprefix tailTrace_3517872
  have hstable : (prefixWord ++ tailWord_3517872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517872).length < 2 ^ (prefixWord ++ tailWord_3517872).sum := by decide
  have hdescent : baseEnd_3517872 < baseStart_3517872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517895 : List Nat := [1, 1, 4, 1, 1, 3, 12]
def baseStart_3517895 : Nat := 118140960795 + 3517895 * 2 ^ 59
def prefixEnd_3517895 : Nat := 4983230072969 + 3 ^ 40 * 3517895 * 2
def baseEnd_3517895 : Nat := 22300876877143443868321

theorem tailTrace_3517895 : CollatzResearch.WordTrace tailWord_3517895 prefixEnd_3517895 22300876877143443868321 := by
  unfold tailWord_3517895
  simp only [CollatzResearch.WordTrace]
  refine ⟨128308171590274698478291139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85538781060183132318860759 128308171590274698478291139)
  ·
    refine ⟨192462257385412047717436709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128308171590274698478291139 192462257385412047717436709)
    ·
      refine ⟨36086673259764758947019383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192462257385412047717436709 36086673259764758947019383)
      ·
        refine ⟨54130009889647138420529075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36086673259764758947019383 54130009889647138420529075)
        ·
          refine ⟨81195014834470707630793613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54130009889647138420529075 81195014834470707630793613)
          ·
            refine ⟨30448130562926515361547605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81195014834470707630793613 30448130562926515361547605)
            ·
              refine ⟨22300876877143443868321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 30448130562926515361547605 22300876877143443868321)
              ·
                rfl

theorem cell23_3517895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 12].length) (baseStart_3517895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517895 prefixEnd_3517895 := by exact prefixLift 3517895
  have htrace : WordTrace (prefixWord ++ tailWord_3517895) baseStart_3517895 baseEnd_3517895 := by
    simpa [prefixWord, tailWord_3517895, baseEnd_3517895] using wordTrace_append hprefix tailTrace_3517895
  have hstable : (prefixWord ++ tailWord_3517895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517895).length < 2 ^ (prefixWord ++ tailWord_3517895).sum := by decide
  have hdescent : baseEnd_3517895 < baseStart_3517895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517899 : List Nat := [1, 1, 1, 1, 3, 3, 5, 2, 2, 4]
def baseStart_3517899 : Nat := 118140960795 + 3517899 * 2 ^ 59
def prefixEnd_3517899 : Nat := 4983230072969 + 3 ^ 40 * 3517899 * 2
def baseEnd_3517899 : Nat := 602124360323745645894661

theorem tailTrace_3517899 : CollatzResearch.WordTrace tailWord_3517899 prefixEnd_3517899 602124360323745645894661 := by
  unfold tailWord_3517899
  simp only [CollatzResearch.WordTrace]
  refine ⟨128308317482260207161436751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85538878321506804774291167 128308317482260207161436751)
  ·
    refine ⟨192462476223390310742155127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128308317482260207161436751 192462476223390310742155127)
    ·
      refine ⟨288693714335085466113232691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192462476223390310742155127 288693714335085466113232691)
      ·
        refine ⟨433040571502628199169849037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288693714335085466113232691 433040571502628199169849037)
        ·
          refine ⟨162390214313485574688693389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433040571502628199169849037 162390214313485574688693389)
          ·
            refine ⟨60896330367557090508260021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162390214313485574688693389 60896330367557090508260021)
            ·
              refine ⟨5709030971958477235149377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60896330367557090508260021 5709030971958477235149377)
              ·
                refine ⟨4281773228968857926362033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5709030971958477235149377 4281773228968857926362033)
                ·
                  refine ⟨3211329921726643444771525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4281773228968857926362033 3211329921726643444771525)
                  ·
                    refine ⟨602124360323745645894661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3211329921726643444771525 602124360323745645894661)
                    ·
                      rfl

theorem cell23_3517899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 2, 4].length) (baseStart_3517899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517899 prefixEnd_3517899 := by exact prefixLift 3517899
  have htrace : WordTrace (prefixWord ++ tailWord_3517899) baseStart_3517899 baseEnd_3517899 := by
    simpa [prefixWord, tailWord_3517899, baseEnd_3517899] using wordTrace_append hprefix tailTrace_3517899
  have hstable : (prefixWord ++ tailWord_3517899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517899).length < 2 ^ (prefixWord ++ tailWord_3517899).sum := by decide
  have hdescent : baseEnd_3517899 < baseStart_3517899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517902 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_3517902 : Nat := 118140960795 + 3517902 * 2 ^ 59
def prefixEnd_3517902 : Nat := 4983230072969 + 3 ^ 40 * 3517902 * 2
def baseEnd_3517902 : Nat := 1806374621413200425946469

theorem tailTrace_3517902 : CollatzResearch.WordTrace tailWord_3517902 prefixEnd_3517902 1806374621413200425946469 := by
  unfold tailWord_3517902
  simp only [CollatzResearch.WordTrace]
  refine ⟨16038553362656167334224495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85538951267499559115863973 16038553362656167334224495)
  ·
    refine ⟨24057830043984251001336743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16038553362656167334224495 24057830043984251001336743)
    ·
      refine ⟨36086745065976376502005115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24057830043984251001336743 36086745065976376502005115)
      ·
        refine ⟨54130117598964564753007673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36086745065976376502005115 54130117598964564753007673)
        ·
          refine ⟨40597588199223423564755755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54130117598964564753007673 40597588199223423564755755)
          ·
            refine ⟨60896382298835135347133633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40597588199223423564755755 60896382298835135347133633)
            ·
              refine ⟨45672286724126351510350225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60896382298835135347133633 45672286724126351510350225)
              ·
                refine ⟨34254215043094763632762669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45672286724126351510350225 34254215043094763632762669)
                ·
                  refine ⟨12845330641160536362286001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34254215043094763632762669 12845330641160536362286001)
                  ·
                    refine ⟨9633997980870402271714501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12845330641160536362286001 9633997980870402271714501)
                    ·
                      refine ⟨1806374621413200425946469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9633997980870402271714501 1806374621413200425946469)
                      ·
                        rfl

theorem cell23_3517902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_3517902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517902 prefixEnd_3517902 := by exact prefixLift 3517902
  have htrace : WordTrace (prefixWord ++ tailWord_3517902) baseStart_3517902 baseEnd_3517902 := by
    simpa [prefixWord, tailWord_3517902, baseEnd_3517902] using wordTrace_append hprefix tailTrace_3517902
  have hstable : (prefixWord ++ tailWord_3517902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517902).length < 2 ^ (prefixWord ++ tailWord_3517902).sum := by decide
  have hdescent : baseEnd_3517902 < baseStart_3517902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517905 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 7]
def baseStart_3517905 : Nat := 118140960795 + 3517905 * 2 ^ 59
def prefixEnd_3517905 : Nat := 4983230072969 + 3 ^ 40 * 3517905 * 2
def baseEnd_3517905 : Nat := 1806376161855163914208955

theorem tailTrace_3517905 : CollatzResearch.WordTrace tailWord_3517905 prefixEnd_3517905 1806376161855163914208955 := by
  unfold tailWord_3517905
  simp only [CollatzResearch.WordTrace]
  refine ⟨128308536320238470186155169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85539024213492313457436779 128308536320238470186155169)
  ·
    refine ⟨96231402240178852639616377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128308536320238470186155169 96231402240178852639616377)
    ·
      refine ⟨72173551680134139479712283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96231402240178852639616377 72173551680134139479712283)
      ·
        refine ⟨108260327520201209219568425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72173551680134139479712283 108260327520201209219568425)
        ·
          refine ⟨81195245640150906914676319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108260327520201209219568425 81195245640150906914676319)
          ·
            refine ⟨121792868460226360372014479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81195245640150906914676319 121792868460226360372014479)
            ·
              refine ⟨182689302690339540558021719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121792868460226360372014479 182689302690339540558021719)
              ·
                refine ⟨274033954035509310837032579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182689302690339540558021719 274033954035509310837032579)
                ·
                  refine ⟨411050931053263966255548869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274033954035509310837032579 411050931053263966255548869)
                  ·
                    refine ⟨77072049572486993672915413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 411050931053263966255548869 77072049572486993672915413)
                    ·
                      refine ⟨1806376161855163914208955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77072049572486993672915413 1806376161855163914208955)
                      ·
                        rfl

theorem cell23_3517905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_3517905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517905 prefixEnd_3517905 := by exact prefixLift 3517905
  have htrace : WordTrace (prefixWord ++ tailWord_3517905) baseStart_3517905 baseEnd_3517905 := by
    simpa [prefixWord, tailWord_3517905, baseEnd_3517905] using wordTrace_append hprefix tailTrace_3517905
  have hstable : (prefixWord ++ tailWord_3517905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517905).length < 2 ^ (prefixWord ++ tailWord_3517905).sum := by decide
  have hdescent : baseEnd_3517905 < baseStart_3517905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517915 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 6]
def baseStart_3517915 : Nat := 118140960795 + 3517915 * 2 ^ 59
def prefixEnd_3517915 : Nat := 4983230072969 + 3 ^ 40 * 3517915 * 2
def baseEnd_3517915 : Nat := 1806381296661708875083909

theorem tailTrace_3517915 : CollatzResearch.WordTrace tailWord_3517915 prefixEnd_3517915 1806381296661708875083909 := by
  unfold tailWord_3517915
  simp only [CollatzResearch.WordTrace]
  refine ⟨128308901050202241894019199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85539267366801494596012799 128308901050202241894019199)
  ·
    refine ⟨192463351575303362841028799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128308901050202241894019199 192463351575303362841028799)
    ·
      refine ⟨288695027362955044261543199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192463351575303362841028799 288695027362955044261543199)
      ·
        refine ⟨433042541044432566392314799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288695027362955044261543199 433042541044432566392314799)
        ·
          refine ⟨649563811566648849588472199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433042541044432566392314799 649563811566648849588472199)
          ·
            refine ⟨974345717349973274382708299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649563811566648849588472199 974345717349973274382708299)
            ·
              refine ⟨1461518576024959911574062449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974345717349973274382708299 1461518576024959911574062449)
              ·
                refine ⟨1096138932018719933680546837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1461518576024959911574062449 1096138932018719933680546837)
                ·
                  refine ⟨51381512438377496891275633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1096138932018719933680546837 51381512438377496891275633)
                  ·
                    refine ⟨38536134328783122668456725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51381512438377496891275633 38536134328783122668456725)
                    ·
                      refine ⟨1806381296661708875083909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38536134328783122668456725 1806381296661708875083909)
                      ·
                        rfl

theorem cell23_3517915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 6].length) (baseStart_3517915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517915 prefixEnd_3517915 := by exact prefixLift 3517915
  have htrace : WordTrace (prefixWord ++ tailWord_3517915) baseStart_3517915 baseEnd_3517915 := by
    simpa [prefixWord, tailWord_3517915, baseEnd_3517915] using wordTrace_append hprefix tailTrace_3517915
  have hstable : (prefixWord ++ tailWord_3517915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517915).length < 2 ^ (prefixWord ++ tailWord_3517915).sum := by decide
  have hdescent : baseEnd_3517915 < baseStart_3517915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517973 : List Nat := [1, 3, 2, 1, 3, 2, 4, 1, 2, 1, 3]
def baseStart_3517973 : Nat := 118140960795 + 3517973 * 2 ^ 59
def prefixEnd_3517973 : Nat := 4983230072969 + 3 ^ 40 * 3517973 * 2
def baseEnd_3517973 : Nat := 1806411078539669648158643

theorem tailTrace_3517973 : CollatzResearch.WordTrace tailWord_3517973 prefixEnd_3517973 1806411078539669648158643 := by
  unfold tailWord_3517973
  simp only [CollatzResearch.WordTrace]
  refine ⟨128311016483992117799630573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85540677655994745199753715 128311016483992117799630573)
  ·
    refine ⟨48116631181497044174861465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128311016483992117799630573 48116631181497044174861465)
    ·
      refine ⟨36087473386122783131146099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48116631181497044174861465 36087473386122783131146099)
      ·
        refine ⟨54131210079184174696719149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36087473386122783131146099 54131210079184174696719149)
        ·
          refine ⟨20299203779694065511269681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54131210079184174696719149 20299203779694065511269681)
          ·
            refine ⟨15224402834770549133452261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20299203779694065511269681 15224402834770549133452261)
            ·
              refine ⟨2854575531519477962522299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15224402834770549133452261 2854575531519477962522299)
              ·
                refine ⟨4281863297279216943783449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2854575531519477962522299 4281863297279216943783449)
                ·
                  refine ⟨3211397472959412707837587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4281863297279216943783449 3211397472959412707837587)
                  ·
                    refine ⟨4817096209439119061756381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3211397472959412707837587 4817096209439119061756381)
                    ·
                      refine ⟨1806411078539669648158643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4817096209439119061756381 1806411078539669648158643)
                      ·
                        rfl

theorem cell23_3517973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_3517973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3517973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3517973 prefixEnd_3517973 := by exact prefixLift 3517973
  have htrace : WordTrace (prefixWord ++ tailWord_3517973) baseStart_3517973 baseEnd_3517973 := by
    simpa [prefixWord, tailWord_3517973, baseEnd_3517973] using wordTrace_append hprefix tailTrace_3517973
  have hstable : (prefixWord ++ tailWord_3517973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517973).length < 2 ^ (prefixWord ++ tailWord_3517973).sum := by decide
  have hdescent : baseEnd_3517973 < baseStart_3517973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518032 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 1, 7]
def baseStart_3518032 : Nat := 118140960795 + 3518032 * 2 ^ 59
def prefixEnd_3518032 : Nat := 4983230072969 + 3 ^ 40 * 3518032 * 2
def baseEnd_3518032 : Nat := 602147124632761639106957

theorem tailTrace_3518032 : CollatzResearch.WordTrace tailWord_3518032 prefixEnd_3518032 602147124632761639106957 := by
  unfold tailWord_3518032
  simp only [CollatzResearch.WordTrace]
  refine ⟨64156584195389185438014175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85542112260518913917352233 64156584195389185438014175)
  ·
    refine ⟨96234876293083778157021263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64156584195389185438014175 96234876293083778157021263)
    ·
      refine ⟨144352314439625667235531895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96234876293083778157021263 144352314439625667235531895)
      ·
        refine ⟨216528471659438500853297843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144352314439625667235531895 216528471659438500853297843)
        ·
          refine ⟨324792707489157751279946765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216528471659438500853297843 324792707489157751279946765)
          ·
            refine ⟨121797265308434156729980037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324792707489157751279946765 121797265308434156729980037)
            ·
              refine ⟨22836987245331404386871257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121797265308434156729980037 22836987245331404386871257)
              ·
                refine ⟨17127740433998553290153443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22836987245331404386871257 17127740433998553290153443)
                ·
                  refine ⟨25691610650997829935230165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17127740433998553290153443 25691610650997829935230165)
                  ·
                    refine ⟨602147124632761639106957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25691610650997829935230165 602147124632761639106957)
                    ·
                      rfl

theorem cell23_3518032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 1, 7].length) (baseStart_3518032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518032 prefixEnd_3518032 := by exact prefixLift 3518032
  have htrace : WordTrace (prefixWord ++ tailWord_3518032) baseStart_3518032 baseEnd_3518032 := by
    simpa [prefixWord, tailWord_3518032, baseEnd_3518032] using wordTrace_append hprefix tailTrace_3518032
  have hstable : (prefixWord ++ tailWord_3518032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518032).length < 2 ^ (prefixWord ++ tailWord_3518032).sum := by decide
  have hdescent : baseEnd_3518032 < baseStart_3518032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518042 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7]
def baseStart_3518042 : Nat := 118140960795 + 3518042 * 2 ^ 59
def prefixEnd_3518042 : Nat := 4983230072969 + 3 ^ 40 * 3518042 * 2
def baseEnd_3518042 : Nat := 1806446508704829878195825

theorem tailTrace_3518042 : CollatzResearch.WordTrace tailWord_3518042 prefixEnd_3518042 1806446508704829878195825 := by
  unfold tailWord_3518042
  simp only [CollatzResearch.WordTrace]
  refine ⟨32078383280185535645973095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85542355413828095055928253 32078383280185535645973095)
  ·
    refine ⟨48117574920278303468959643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32078383280185535645973095 48117574920278303468959643)
    ·
      refine ⟨72176362380417455203439465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48117574920278303468959643 72176362380417455203439465)
      ·
        refine ⟨54132271785313091402579599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72176362380417455203439465 54132271785313091402579599)
        ·
          refine ⟨81198407677969637103869399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54132271785313091402579599 81198407677969637103869399)
          ·
            refine ⟨121797611516954455655804099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81198407677969637103869399 121797611516954455655804099)
            ·
              refine ⟨182696417275431683483706149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121797611516954455655804099 182696417275431683483706149)
              ·
                refine ⟨34255578239143440653194903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182696417275431683483706149 34255578239143440653194903)
                ·
                  refine ⟨51383367358715160979792355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34255578239143440653194903 51383367358715160979792355)
                  ·
                    refine ⟨77075051038072741469688533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51383367358715160979792355 77075051038072741469688533)
                    ·
                      refine ⟨1806446508704829878195825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77075051038072741469688533 1806446508704829878195825)
                      ·
                        rfl

theorem cell23_3518042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_3518042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518042 prefixEnd_3518042 := by exact prefixLift 3518042
  have htrace : WordTrace (prefixWord ++ tailWord_3518042) baseStart_3518042 baseEnd_3518042 := by
    simpa [prefixWord, tailWord_3518042, baseEnd_3518042] using wordTrace_append hprefix tailTrace_3518042
  have hstable : (prefixWord ++ tailWord_3518042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518042).length < 2 ^ (prefixWord ++ tailWord_3518042).sum := by decide
  have hdescent : baseEnd_3518042 < baseStart_3518042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518089 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 1, 4, 3]
def baseStart_3518089 : Nat := 118140960795 + 3518089 * 2 ^ 59
def prefixEnd_3518089 : Nat := 4983230072969 + 3 ^ 40 * 3518089 * 2
def baseEnd_3518089 : Nat := 1806470642295591194308109

theorem tailTrace_3518089 : CollatzResearch.WordTrace tailWord_3518089 prefixEnd_3518089 1806470642295591194308109 := by
  unfold tailWord_3518089
  simp only [CollatzResearch.WordTrace]
  refine ⟨128315247351571869610853321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85543498234381246407235547 128315247351571869610853321)
  ·
    refine ⟨96236435513678902208139991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128315247351571869610853321 96236435513678902208139991)
    ·
      refine ⟨144354653270518353312209987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96236435513678902208139991 144354653270518353312209987)
      ·
        refine ⟨216531979905777529968314981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144354653270518353312209987 216531979905777529968314981)
        ·
          refine ⟨40599746232333286869059059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216531979905777529968314981 40599746232333286869059059)
          ·
            refine ⟨60899619348499930303588589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40599746232333286869059059 60899619348499930303588589)
            ·
              refine ⟨22837357255687473863845721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60899619348499930303588589 22837357255687473863845721)
              ·
                refine ⟨17128017941765605397884291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22837357255687473863845721 17128017941765605397884291)
                ·
                  refine ⟨25692026912648408096826437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17128017941765605397884291 25692026912648408096826437)
                  ·
                    refine ⟨4817255046121576518154957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25692026912648408096826437 4817255046121576518154957)
                    ·
                      refine ⟨1806470642295591194308109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4817255046121576518154957 1806470642295591194308109)
                      ·
                        rfl

theorem cell23_3518089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 4, 3].length) (baseStart_3518089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518089 prefixEnd_3518089 := by exact prefixLift 3518089
  have htrace : WordTrace (prefixWord ++ tailWord_3518089) baseStart_3518089 baseEnd_3518089 := by
    simpa [prefixWord, tailWord_3518089, baseEnd_3518089] using wordTrace_append hprefix tailTrace_3518089
  have hstable : (prefixWord ++ tailWord_3518089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518089).length < 2 ^ (prefixWord ++ tailWord_3518089).sum := by decide
  have hdescent : baseEnd_3518089 < baseStart_3518089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518169 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 3, 6]
def baseStart_3518169 : Nat := 118140960795 + 3518169 * 2 ^ 59
def prefixEnd_3518169 : Nat := 4983230072969 + 3 ^ 40 * 3518169 * 2
def baseEnd_3518169 : Nat := 602170573582650293769247

theorem tailTrace_3518169 : CollatzResearch.WordTrace tailWord_3518169 prefixEnd_3518169 602170573582650293769247 := by
  unfold tailWord_3518169
  simp only [CollatzResearch.WordTrace]
  refine ⟨128318165191282043273765561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85545443460854695515843707 128318165191282043273765561)
  ·
    refine ⟨96238623893461532455324171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128318165191282043273765561 96238623893461532455324171)
    ·
      refine ⟨144357935840192298682986257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96238623893461532455324171 144357935840192298682986257)
      ·
        refine ⟨108268451880144224012239693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144357935840192298682986257 108268451880144224012239693)
        ·
          refine ⟨40600669455054084004589885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108268451880144224012239693 40600669455054084004589885)
          ·
            refine ⟨15225251045645281501721207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40600669455054084004589885 15225251045645281501721207)
            ·
              refine ⟨22837876568467922252581811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15225251045645281501721207 22837876568467922252581811)
              ·
                refine ⟨34256814852701883378872717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22837876568467922252581811 34256814852701883378872717)
                ·
                  refine ⟨12846305569763206267077269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34256814852701883378872717 12846305569763206267077269)
                  ·
                    refine ⟨602170573582650293769247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12846305569763206267077269 602170573582650293769247)
                    ·
                      rfl

theorem cell23_3518169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 6].length) (baseStart_3518169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518169 prefixEnd_3518169 := by exact prefixLift 3518169
  have htrace : WordTrace (prefixWord ++ tailWord_3518169) baseStart_3518169 baseEnd_3518169 := by
    simpa [prefixWord, tailWord_3518169, baseEnd_3518169] using wordTrace_append hprefix tailTrace_3518169
  have hstable : (prefixWord ++ tailWord_3518169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518169).length < 2 ^ (prefixWord ++ tailWord_3518169).sum := by decide
  have hdescent : baseEnd_3518169 < baseStart_3518169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518176 : List Nat := [2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 4]
def baseStart_3518176 : Nat := 118140960795 + 3518176 * 2 ^ 59
def prefixEnd_3518176 : Nat := 4983230072969 + 3 ^ 40 * 3518176 * 2
def baseEnd_3518176 : Nat := 1806515315112532353920209

theorem tailTrace_3518176 : CollatzResearch.WordTrace tailWord_3518176 prefixEnd_3518176 1806515315112532353920209 := by
  unfold tailWord_3518176
  simp only [CollatzResearch.WordTrace]
  refine ⟨64159210251128341734635191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85545613668171122312846921 64159210251128341734635191)
  ·
    refine ⟨96238815376692512601952787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64159210251128341734635191 96238815376692512601952787)
    ·
      refine ⟨144358223065038768902929181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96238815376692512601952787 144358223065038768902929181)
      ·
        refine ⟨54134333649389538338598443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144358223065038768902929181 54134333649389538338598443)
        ·
          refine ⟨81201500474084307507897665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54134333649389538338598443 81201500474084307507897665)
          ·
            refine ⟨60901125355563230630923249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81201500474084307507897665 60901125355563230630923249)
            ·
              refine ⟨45675844016672422973192437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60901125355563230630923249 45675844016672422973192437)
              ·
                refine ⟨4282110376563039653736791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45675844016672422973192437 4282110376563039653736791)
                ·
                  refine ⟨6423165564844559480605187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4282110376563039653736791 6423165564844559480605187)
                  ·
                    refine ⟨9634748347266839220907781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6423165564844559480605187 9634748347266839220907781)
                    ·
                      refine ⟨1806515315112532353920209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9634748347266839220907781 1806515315112532353920209)
                      ·
                        rfl

theorem cell23_3518176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_3518176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518176 prefixEnd_3518176 := by exact prefixLift 3518176
  have htrace : WordTrace (prefixWord ++ tailWord_3518176) baseStart_3518176 baseEnd_3518176 := by
    simpa [prefixWord, tailWord_3518176, baseEnd_3518176] using wordTrace_append hprefix tailTrace_3518176
  have hstable : (prefixWord ++ tailWord_3518176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518176).length < 2 ^ (prefixWord ++ tailWord_3518176).sum := by decide
  have hdescent : baseEnd_3518176 < baseStart_3518176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518186 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 4, 4]
def baseStart_3518186 : Nat := 118140960795 + 3518186 * 2 ^ 59
def prefixEnd_3518186 : Nat := 4983230072969 + 3 ^ 40 * 3518186 * 2
def baseEnd_3518186 : Nat := 602173483306359104931721

theorem tailTrace_3518186 : CollatzResearch.WordTrace tailWord_3518186 prefixEnd_3518186 602173483306359104931721 := by
  unfold tailWord_3518186
  simp only [CollatzResearch.WordTrace]
  refine ⟨32079696308055113794283603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85545856821480303451422941 32079696308055113794283603)
  ·
    refine ⟨48119544462082670691425405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32079696308055113794283603 48119544462082670691425405)
    ·
      refine ⟨18044829173281001509284527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48119544462082670691425405 18044829173281001509284527)
      ·
        refine ⟨27067243759921502263926791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18044829173281001509284527 27067243759921502263926791)
        ·
          refine ⟨40600865639882253395890187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27067243759921502263926791 40600865639882253395890187)
          ·
            refine ⟨60901298459823380093835281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40600865639882253395890187 60901298459823380093835281)
            ·
              refine ⟨45675973844867535070376461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60901298459823380093835281 45675973844867535070376461)
              ·
                refine ⟨17128490191825325651391173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45675973844867535070376461 17128490191825325651391173)
                ·
                  refine ⟨3211591910967248559635845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17128490191825325651391173 3211591910967248559635845)
                  ·
                    refine ⟨602173483306359104931721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3211591910967248559635845 602173483306359104931721)
                    ·
                      rfl

theorem cell23_3518186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_3518186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518186 prefixEnd_3518186 := by exact prefixLift 3518186
  have htrace : WordTrace (prefixWord ++ tailWord_3518186) baseStart_3518186 baseEnd_3518186 := by
    simpa [prefixWord, tailWord_3518186, baseEnd_3518186] using wordTrace_append hprefix tailTrace_3518186
  have hstable : (prefixWord ++ tailWord_3518186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518186).length < 2 ^ (prefixWord ++ tailWord_3518186).sum := by decide
  have hdescent : baseEnd_3518186 < baseStart_3518186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518199 : List Nat := [1, 1, 3, 1, 1, 1, 7, 8]
def baseStart_3518199 : Nat := 118140960795 + 3518199 * 2 ^ 59
def prefixEnd_3518199 : Nat := 4983230072969 + 3 ^ 40 * 3518199 * 2
def baseEnd_3518199 : Nat := 66908412043243917182689

theorem tailTrace_3518199 : CollatzResearch.WordTrace tailWord_3518199 prefixEnd_3518199 66908412043243917182689 := by
  unfold tailWord_3518199
  simp only [CollatzResearch.WordTrace]
  refine ⟨128319259381173358397357651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85546172920782238931571767 128319259381173358397357651)
  ·
    refine ⟨192478889071760037596036477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128319259381173358397357651 192478889071760037596036477)
    ·
      refine ⟨72179583401910014098513679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192478889071760037596036477 72179583401910014098513679)
      ·
        refine ⟨108269375102865021147770519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72179583401910014098513679 108269375102865021147770519)
        ·
          refine ⟨162404062654297531721655779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108269375102865021147770519 162404062654297531721655779)
          ·
            refine ⟨243606093981446297582483669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162404062654297531721655779 243606093981446297582483669)
            ·
              refine ⟨5709517827690147599589461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 243606093981446297582483669 5709517827690147599589461)
              ·
                refine ⟨66908412043243917182689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5709517827690147599589461 66908412043243917182689)
                ·
                  rfl

theorem cell23_3518199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 8].length) (baseStart_3518199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518199 prefixEnd_3518199 := by exact prefixLift 3518199
  have htrace : WordTrace (prefixWord ++ tailWord_3518199) baseStart_3518199 baseEnd_3518199 := by
    simpa [prefixWord, tailWord_3518199, baseEnd_3518199] using wordTrace_append hprefix tailTrace_3518199
  have hstable : (prefixWord ++ tailWord_3518199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518199).length < 2 ^ (prefixWord ++ tailWord_3518199).sum := by decide
  have hdescent : baseEnd_3518199 < baseStart_3518199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518216 : List Nat := [2, 1, 3, 2, 2, 1, 5, 7]
def baseStart_3518216 : Nat := 118140960795 + 3518216 * 2 ^ 59
def prefixEnd_3518216 : Nat := 4983230072969 + 3 ^ 40 * 3518216 * 2
def baseEnd_3518216 : Nat := 66908735345878229534075

theorem tailTrace_3518216 : CollatzResearch.WordTrace tailWord_3518216 prefixEnd_3518216 66908735345878229534075 := by
  unfold tailWord_3518216
  simp only [CollatzResearch.WordTrace]
  refine ⟨64159939711055885150363251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85546586281407846867151001 64159939711055885150363251)
  ·
    refine ⟨96239909566583827725544877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64159939711055885150363251 96239909566583827725544877)
    ·
      refine ⟨36089966087468935397079329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96239909566583827725544877 36089966087468935397079329)
      ·
        refine ⟨27067474565601701547809497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36089966087468935397079329 27067474565601701547809497)
        ·
          refine ⟨20300605924201276160857123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27067474565601701547809497 20300605924201276160857123)
          ·
            refine ⟨30450908886301914241285685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20300605924201276160857123 30450908886301914241285685)
            ·
              refine ⟨2854772708090804460120533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30450908886301914241285685 2854772708090804460120533)
              ·
                refine ⟨66908735345878229534075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2854772708090804460120533 66908735345878229534075)
                ·
                  rfl

theorem cell23_3518216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 7].length) (baseStart_3518216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518216 prefixEnd_3518216 := by exact prefixLift 3518216
  have htrace : WordTrace (prefixWord ++ tailWord_3518216) baseStart_3518216 baseEnd_3518216 := by
    simpa [prefixWord, tailWord_3518216, baseEnd_3518216] using wordTrace_append hprefix tailTrace_3518216
  have hstable : (prefixWord ++ tailWord_3518216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518216).length < 2 ^ (prefixWord ++ tailWord_3518216).sum := by decide
  have hdescent : baseEnd_3518216 < baseStart_3518216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518260 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_3518260 : Nat := 118140960795 + 3518260 * 2 ^ 59
def prefixEnd_3518260 : Nat := 4983230072969 + 3 ^ 40 * 3518260 * 2
def baseEnd_3518260 : Nat := 1806558447487510025269823

theorem tailTrace_3518260 : CollatzResearch.WordTrace tailWord_3518260 prefixEnd_3518260 1806558447487510025269823 := by
  unfold tailWord_3518260
  simp only [CollatzResearch.WordTrace]
  refine ⟨64160742116976182907664117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85547656155968243876885489 64160742116976182907664117)
  ·
    refine ⟨6015069573466517147593511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64160742116976182907664117 6015069573466517147593511)
    ·
      refine ⟨9022604360199775721390267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6015069573466517147593511 9022604360199775721390267)
      ·
        refine ⟨13533906540299663582085401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9022604360199775721390267 13533906540299663582085401)
        ·
          refine ⟨10150429905224747686564051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13533906540299663582085401 10150429905224747686564051)
          ·
            refine ⟨15225644857837121529846077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10150429905224747686564051 15225644857837121529846077)
            ·
              refine ⟨5709616821688920573692279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15225644857837121529846077 5709616821688920573692279)
              ·
                refine ⟨8564425232533380860538419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5709616821688920573692279 8564425232533380860538419)
                ·
                  refine ⟨12846637848800071290807629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8564425232533380860538419 12846637848800071290807629)
                  ·
                    refine ⟨4817489193300026734052861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12846637848800071290807629 4817489193300026734052861)
                    ·
                      refine ⟨1806558447487510025269823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4817489193300026734052861 1806558447487510025269823)
                      ·
                        rfl

theorem cell23_3518260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_3518260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518260 prefixEnd_3518260 := by exact prefixLift 3518260
  have htrace : WordTrace (prefixWord ++ tailWord_3518260) baseStart_3518260 baseEnd_3518260 := by
    simpa [prefixWord, tailWord_3518260, baseEnd_3518260] using wordTrace_append hprefix tailTrace_3518260
  have hstable : (prefixWord ++ tailWord_3518260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518260).length < 2 ^ (prefixWord ++ tailWord_3518260).sum := by decide
  have hdescent : baseEnd_3518260 < baseStart_3518260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518278 : List Nat := [6, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_3518278 : Nat := 118140960795 + 3518278 * 2 ^ 59
def prefixEnd_3518278 : Nat := 4983230072969 + 3 ^ 40 * 3518278 * 2
def baseEnd_3518278 : Nat := 1806567690139290954844741

theorem tailTrace_3518278 : CollatzResearch.WordTrace tailWord_3518278 prefixEnd_3518278 1806567690139290954844741 := by
  unfold tailWord_3518278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4010066898371473590296359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85548093831924769926322325 4010066898371473590296359)
  ·
    refine ⟨6015100347557210385444539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4010066898371473590296359 6015100347557210385444539)
    ·
      refine ⟨9022650521335815578166809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6015100347557210385444539 9022650521335815578166809)
      ·
        refine ⟨6766987891001861683625107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9022650521335815578166809 6766987891001861683625107)
        ·
          refine ⟨10150481836502792525437661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6766987891001861683625107 10150481836502792525437661)
          ·
            refine ⟨3806430688688547197039123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10150481836502792525437661 3806430688688547197039123)
            ·
              refine ⟨5709646033032820795558685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3806430688688547197039123 5709646033032820795558685)
              ·
                refine ⟨2141117262387307798334507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5709646033032820795558685 2141117262387307798334507)
                ·
                  refine ⟨3211675893580961697501761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2141117262387307798334507 3211675893580961697501761)
                  ·
                    refine ⟨2408756920185721273126321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3211675893580961697501761 2408756920185721273126321)
                    ·
                      refine ⟨1806567690139290954844741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2408756920185721273126321 1806567690139290954844741)
                      ·
                        rfl

theorem cell23_3518278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_3518278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518278 prefixEnd_3518278 := by exact prefixLift 3518278
  have htrace : WordTrace (prefixWord ++ tailWord_3518278) baseStart_3518278 baseEnd_3518278 := by
    simpa [prefixWord, tailWord_3518278, baseEnd_3518278] using wordTrace_append hprefix tailTrace_3518278
  have hstable : (prefixWord ++ tailWord_3518278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518278).length < 2 ^ (prefixWord ++ tailWord_3518278).sum := by decide
  have hdescent : baseEnd_3518278 < baseStart_3518278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518286 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3]
def baseStart_3518286 : Nat := 118140960795 + 3518286 * 2 ^ 59
def prefixEnd_3518286 : Nat := 4983230072969 + 3 ^ 40 * 3518286 * 2
def baseEnd_3518286 : Nat := 1806571797984526923544703

theorem tailTrace_3518286 : CollatzResearch.WordTrace tailWord_3518286 prefixEnd_3518286 1806571797984526923544703 := by
  unfold tailWord_3518286
  simp only [CollatzResearch.WordTrace]
  refine ⟨16040304066482271531971839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85548288354572114837183141 16040304066482271531971839)
  ·
    refine ⟨24060456099723407297957759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16040304066482271531971839 24060456099723407297957759)
    ·
      refine ⟨36090684149585110946936639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24060456099723407297957759 36090684149585110946936639)
      ·
        refine ⟨54136026224377666420404959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36090684149585110946936639 54136026224377666420404959)
        ·
          refine ⟨81204039336566499630607439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54136026224377666420404959 81204039336566499630607439)
          ·
            refine ⟨121806059004849749445911159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81204039336566499630607439 121806059004849749445911159)
            ·
              refine ⟨182709088507274624168866739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121806059004849749445911159 182709088507274624168866739)
              ·
                refine ⟨274063632760911936253300109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182709088507274624168866739 274063632760911936253300109)
                ·
                  refine ⟨102773862285341976094987541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274063632760911936253300109 102773862285341976094987541)
                  ·
                    refine ⟨4817524794625405129452541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102773862285341976094987541 4817524794625405129452541)
                    ·
                      refine ⟨1806571797984526923544703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4817524794625405129452541 1806571797984526923544703)
                      ·
                        rfl

theorem cell23_3518286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_3518286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518286 prefixEnd_3518286 := by exact prefixLift 3518286
  have htrace : WordTrace (prefixWord ++ tailWord_3518286) baseStart_3518286 baseEnd_3518286 := by
    simpa [prefixWord, tailWord_3518286, baseEnd_3518286] using wordTrace_append hprefix tailTrace_3518286
  have hstable : (prefixWord ++ tailWord_3518286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518286).length < 2 ^ (prefixWord ++ tailWord_3518286).sum := by decide
  have hdescent : baseEnd_3518286 < baseStart_3518286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518383 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 3, 4]
def baseStart_3518383 : Nat := 118140960795 + 3518383 * 2 ^ 59
def prefixEnd_3518383 : Nat := 4983230072969 + 3 ^ 40 * 3518383 * 2
def baseEnd_3518383 : Nat := 602207201869337681343919

theorem tailTrace_3518383 : CollatzResearch.WordTrace tailWord_3518383 prefixEnd_3518383 602207201869337681343919 := by
  unfold tailWord_3518383
  simp only [CollatzResearch.WordTrace]
  refine ⟨128325970412506757822055803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85550646941671171881370535 128325970412506757822055803)
  ·
    refine ⟨192488955618760136733083705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128325970412506757822055803 192488955618760136733083705)
    ·
      refine ⟨144366716714070102549812779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192488955618760136733083705 144366716714070102549812779)
      ·
        refine ⟨216550075071105153824719169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144366716714070102549812779 216550075071105153824719169)
        ·
          refine ⟨162412556303328865368539377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216550075071105153824719169 162412556303328865368539377)
          ·
            refine ⟨121809417227496649026404533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162412556303328865368539377 121809417227496649026404533)
            ·
              refine ⟨11419632865077810846225425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121809417227496649026404533 11419632865077810846225425)
              ·
                refine ⟨8564724648808358134669069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11419632865077810846225425 8564724648808358134669069)
                ·
                  refine ⟨3211771743303134300500901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8564724648808358134669069 3211771743303134300500901)
                  ·
                    refine ⟨602207201869337681343919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3211771743303134300500901 602207201869337681343919)
                    ·
                      rfl

theorem cell23_3518383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 4].length) (baseStart_3518383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518383 prefixEnd_3518383 := by exact prefixLift 3518383
  have htrace : WordTrace (prefixWord ++ tailWord_3518383) baseStart_3518383 baseEnd_3518383 := by
    simpa [prefixWord, tailWord_3518383, baseEnd_3518383] using wordTrace_append hprefix tailTrace_3518383
  have hstable : (prefixWord ++ tailWord_3518383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518383).length < 2 ^ (prefixWord ++ tailWord_3518383).sum := by decide
  have hdescent : baseEnd_3518383 < baseStart_3518383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518386 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_3518386 : Nat := 118140960795 + 3518386 * 2 ^ 59
def prefixEnd_3518386 : Nat := 4983230072969 + 3 ^ 40 * 3518386 * 2
def baseEnd_3518386 : Nat := 1806623146049976532294243

theorem tailTrace_3518386 : CollatzResearch.WordTrace tailWord_3518386 prefixEnd_3518386 1806623146049976532294243 := by
  unfold tailWord_3518386
  simp only [CollatzResearch.WordTrace]
  refine ⟨32081519957873972333603753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85550719887663926222943341 32081519957873972333603753)
  ·
    refine ⟨24061139968405479250202815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32081519957873972333603753 24061139968405479250202815)
    ·
      refine ⟨36091709952608218875304223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24061139968405479250202815 36091709952608218875304223)
      ·
        refine ⟨54137564928912328312956335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36091709952608218875304223 54137564928912328312956335)
        ·
          refine ⟨81206347393368492469434503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54137564928912328312956335 81206347393368492469434503)
          ·
            refine ⟨121809521090052738704151755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81206347393368492469434503 121809521090052738704151755)
            ·
              refine ⟨182714281635079108056227633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121809521090052738704151755 182714281635079108056227633)
              ·
                refine ⟨137035711226309331042170725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182714281635079108056227633 137035711226309331042170725)
                ·
                  refine ⟨25694195854932999570407011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137035711226309331042170725 25694195854932999570407011)
                  ·
                    refine ⟨38541293782399499355610517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25694195854932999570407011 38541293782399499355610517)
                    ·
                      refine ⟨1806623146049976532294243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38541293782399499355610517 1806623146049976532294243)
                      ·
                        rfl

theorem cell23_3518386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_3518386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518386 prefixEnd_3518386 := by exact prefixLift 3518386
  have htrace : WordTrace (prefixWord ++ tailWord_3518386) baseStart_3518386 baseEnd_3518386 := by
    simpa [prefixWord, tailWord_3518386, baseEnd_3518386] using wordTrace_append hprefix tailTrace_3518386
  have hstable : (prefixWord ++ tailWord_3518386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518386).length < 2 ^ (prefixWord ++ tailWord_3518386).sum := by decide
  have hdescent : baseEnd_3518386 < baseStart_3518386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518393 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 1, 4, 3]
def baseStart_3518393 : Nat := 118140960795 + 3518393 * 2 ^ 59
def prefixEnd_3518393 : Nat := 4983230072969 + 3 ^ 40 * 3518393 * 2
def baseEnd_3518393 : Nat := 1806626740414558004906711

theorem tailTrace_3518393 : CollatzResearch.WordTrace tailWord_3518393 prefixEnd_3518393 1806626740414558004906711 := by
  unfold tailWord_3518393
  simp only [CollatzResearch.WordTrace]
  refine ⟨128326335142470529529919833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85550890094980353019946555 128326335142470529529919833)
  ·
    refine ⟨96244751356852897147439875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128326335142470529529919833 96244751356852897147439875)
    ·
      refine ⟨144367127035279345721159813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96244751356852897147439875 144367127035279345721159813)
      ·
        refine ⟨27068836319114877322717465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144367127035279345721159813 27068836319114877322717465)
        ·
          refine ⟨20301627239336157992038099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27068836319114877322717465 20301627239336157992038099)
          ·
            refine ⟨30452440859004236988057149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20301627239336157992038099 30452440859004236988057149)
            ·
              refine ⟨11419665322126588870521431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30452440859004236988057149 11419665322126588870521431)
              ·
                refine ⟨17129497983189883305782147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11419665322126588870521431 17129497983189883305782147)
                ·
                  refine ⟨25694246974784824958673221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17129497983189883305782147 25694246974784824958673221)
                  ·
                    refine ⟨4817671307772154679751229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25694246974784824958673221 4817671307772154679751229)
                    ·
                      refine ⟨1806626740414558004906711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4817671307772154679751229 1806626740414558004906711)
                      ·
                        rfl

theorem cell23_3518393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_3518393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518393 prefixEnd_3518393 := by exact prefixLift 3518393
  have htrace : WordTrace (prefixWord ++ tailWord_3518393) baseStart_3518393 baseEnd_3518393 := by
    simpa [prefixWord, tailWord_3518393, baseEnd_3518393] using wordTrace_append hprefix tailTrace_3518393
  have hstable : (prefixWord ++ tailWord_3518393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518393).length < 2 ^ (prefixWord ++ tailWord_3518393).sum := by decide
  have hdescent : baseEnd_3518393 < baseStart_3518393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518416 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 6]
def baseStart_3518416 : Nat := 118140960795 + 3518416 * 2 ^ 59
def prefixEnd_3518416 : Nat := 4983230072969 + 3 ^ 40 * 3518416 * 2
def baseEnd_3518416 : Nat := 1806638550469611414919105

theorem tailTrace_3518416 : CollatzResearch.WordTrace tailWord_3518416 prefixEnd_3518416 1806638550469611414919105 := by
  unfold tailWord_3518416
  simp only [CollatzResearch.WordTrace]
  refine ⟨64163587010693602229003551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85551449347591469638671401 64163587010693602229003551)
  ·
    refine ⟨96245380516040403343505327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64163587010693602229003551 96245380516040403343505327)
    ·
      refine ⟨144368070774060605015257991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96245380516040403343505327 144368070774060605015257991)
      ·
        refine ⟨216552106161090907522886987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144368070774060605015257991 216552106161090907522886987)
        ·
          refine ⟨324828159241636361284330481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216552106161090907522886987 324828159241636361284330481)
          ·
            refine ⟨243621119431227270963247861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324828159241636361284330481 243621119431227270963247861)
            ·
              refine ⟨22839479946677556652804487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 243621119431227270963247861 22839479946677556652804487)
              ·
                refine ⟨34259219920016334979206731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22839479946677556652804487 34259219920016334979206731)
                ·
                  refine ⟨51388829880024502468810097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34259219920016334979206731 51388829880024502468810097)
                  ·
                    refine ⟨38541622410018376851607573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51388829880024502468810097 38541622410018376851607573)
                    ·
                      refine ⟨1806638550469611414919105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38541622410018376851607573 1806638550469611414919105)
                      ·
                        rfl

theorem cell23_3518416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_3518416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518416 prefixEnd_3518416 := by exact prefixLift 3518416
  have htrace : WordTrace (prefixWord ++ tailWord_3518416) baseStart_3518416 baseEnd_3518416 := by
    simpa [prefixWord, tailWord_3518416, baseEnd_3518416] using wordTrace_append hprefix tailTrace_3518416
  have hstable : (prefixWord ++ tailWord_3518416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518416).length < 2 ^ (prefixWord ++ tailWord_3518416).sum := by decide
  have hdescent : baseEnd_3518416 < baseStart_3518416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518474 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 3, 1, 3]
def baseStart_3518474 : Nat := 118140960795 + 3518474 * 2 ^ 59
def prefixEnd_3518474 : Nat := 4983230072969 + 3 ^ 40 * 3518474 * 2
def baseEnd_3518474 : Nat := 1806668332347572187993839

theorem tailTrace_3518474 : CollatzResearch.WordTrace tailWord_3518474 prefixEnd_3518474 1806668332347572187993839 := by
  unfold tailWord_3518474
  simp only [CollatzResearch.WordTrace]
  refine ⟨32082322363794270090904619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85552859636784720242412317 32082322363794270090904619)
  ·
    refine ⟨48123483545691405136356929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32082322363794270090904619 48123483545691405136356929)
    ·
      refine ⟨36092612659268553852267697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48123483545691405136356929 36092612659268553852267697)
      ·
        refine ⟨27069459494451415389200773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36092612659268553852267697 27069459494451415389200773)
        ·
          refine ⟨5075523655209640385475145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27069459494451415389200773 5075523655209640385475145)
          ·
            refine ⟨3806642741407230289106359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5075523655209640385475145 3806642741407230289106359)
            ·
              refine ⟨5709964112110845433659539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3806642741407230289106359 5709964112110845433659539)
              ·
                refine ⟨8564946168166268150489309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5709964112110845433659539 8564946168166268150489309)
                ·
                  refine ⟨3211854813062350556433491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8564946168166268150489309 3211854813062350556433491)
                  ·
                    refine ⟨4817782219593525834650237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3211854813062350556433491 4817782219593525834650237)
                    ·
                      refine ⟨1806668332347572187993839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4817782219593525834650237 1806668332347572187993839)
                      ·
                        rfl

theorem cell23_3518474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_3518474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518474 prefixEnd_3518474 := by exact prefixLift 3518474
  have htrace : WordTrace (prefixWord ++ tailWord_3518474) baseStart_3518474 baseEnd_3518474 := by
    simpa [prefixWord, tailWord_3518474, baseEnd_3518474] using wordTrace_append hprefix tailTrace_3518474
  have hstable : (prefixWord ++ tailWord_3518474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518474).length < 2 ^ (prefixWord ++ tailWord_3518474).sum := by decide
  have hdescent : baseEnd_3518474 < baseStart_3518474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518483 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 5]
def baseStart_3518483 : Nat := 118140960795 + 3518483 * 2 ^ 59
def prefixEnd_3518483 : Nat := 4983230072969 + 3 ^ 40 * 3518483 * 2
def baseEnd_3518483 : Nat := 1806672953673462652781297

theorem tailTrace_3518483 : CollatzResearch.WordTrace tailWord_3518483 prefixEnd_3518483 1806672953673462652781297 := by
  unfold tailWord_3518483
  simp only [CollatzResearch.WordTrace]
  refine ⟨128329617712144474900696103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85553078474762983267130735 128329617712144474900696103)
  ·
    refine ⟨192494426568216712351044155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128329617712144474900696103 192494426568216712351044155)
    ·
      refine ⟨288741639852325068526566233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192494426568216712351044155 288741639852325068526566233)
      ·
        refine ⟨216556229889243801394924675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288741639852325068526566233 216556229889243801394924675)
        ·
          refine ⟨324834344833865702092387013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216556229889243801394924675 324834344833865702092387013)
          ·
            refine ⟨60906439656349819142322565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 324834344833865702092387013 60906439656349819142322565)
            ·
              refine ⟨11419957435565591089185481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60906439656349819142322565 11419957435565591089185481)
              ·
                refine ⟨8564968076674193316889111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11419957435565591089185481 8564968076674193316889111)
                ·
                  refine ⟨12847452115011289975333667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8564968076674193316889111 12847452115011289975333667)
                  ·
                    refine ⟨19271178172516934963000501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12847452115011289975333667 19271178172516934963000501)
                    ·
                      refine ⟨1806672953673462652781297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19271178172516934963000501 1806672953673462652781297)
                      ·
                        rfl

theorem cell23_3518483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 5].length) (baseStart_3518483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518483 prefixEnd_3518483 := by exact prefixLift 3518483
  have htrace : WordTrace (prefixWord ++ tailWord_3518483) baseStart_3518483 baseEnd_3518483 := by
    simpa [prefixWord, tailWord_3518483, baseEnd_3518483] using wordTrace_append hprefix tailTrace_3518483
  have hstable : (prefixWord ++ tailWord_3518483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518483).length < 2 ^ (prefixWord ++ tailWord_3518483).sum := by decide
  have hdescent : baseEnd_3518483 < baseStart_3518483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518510 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_3518510 : Nat := 118140960795 + 3518510 * 2 ^ 59
def prefixEnd_3518510 : Nat := 4983230072969 + 3 ^ 40 * 3518510 * 2
def baseEnd_3518510 : Nat := 1806686817651134047143673

theorem tailTrace_3518510 : CollatzResearch.WordTrace tailWord_3518510 prefixEnd_3518510 1806686817651134047143673 := by
  unfold tailWord_3518510
  simp only [CollatzResearch.WordTrace]
  refine ⟨16041325310380832313991123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85553734988697772341285989 16041325310380832313991123)
  ·
    refine ⟨24061987965571248470986685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16041325310380832313991123 24061987965571248470986685)
    ·
      refine ⟨9023245487089218176620007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24061987965571248470986685 9023245487089218176620007)
      ·
        refine ⟨13534868230633827264930011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9023245487089218176620007 13534868230633827264930011)
        ·
          refine ⟨20302302345950740897395017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13534868230633827264930011 20302302345950740897395017)
          ·
            refine ⟨15226726759463055673046263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20302302345950740897395017 15226726759463055673046263)
            ·
              refine ⟨22840090139194583509569395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15226726759463055673046263 22840090139194583509569395)
              ·
                refine ⟨34260135208791875264354093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22840090139194583509569395 34260135208791875264354093)
                ·
                  refine ⟨12847550703296953224132785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34260135208791875264354093 12847550703296953224132785)
                  ·
                    refine ⟨9635663027472714918099589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12847550703296953224132785 9635663027472714918099589)
                    ·
                      refine ⟨1806686817651134047143673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9635663027472714918099589 1806686817651134047143673)
                      ·
                        rfl

theorem cell23_3518510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_3518510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518510 prefixEnd_3518510 := by exact prefixLift 3518510
  have htrace : WordTrace (prefixWord ++ tailWord_3518510) baseStart_3518510 baseEnd_3518510 := by
    simpa [prefixWord, tailWord_3518510, baseEnd_3518510] using wordTrace_append hprefix tailTrace_3518510
  have hstable : (prefixWord ++ tailWord_3518510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518510).length < 2 ^ (prefixWord ++ tailWord_3518510).sum := by decide
  have hdescent : baseEnd_3518510 < baseStart_3518510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518553 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 2, 3, 4]
def baseStart_3518553 : Nat := 118140960795 + 3518553 * 2 ^ 59
def prefixEnd_3518553 : Nat := 4983230072969 + 3 ^ 40 * 3518553 * 2
def baseEnd_3518553 : Nat := 1806708897319277378905975

theorem tailTrace_3518553 : CollatzResearch.WordTrace tailWord_3518553 prefixEnd_3518553 1806708897319277378905975 := by
  unfold tailWord_3518553
  simp only [CollatzResearch.WordTrace]
  refine ⟨128332170821890876855744313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85554780547927251237162875 128332170821890876855744313)
  ·
    refine ⟨96249128116418157641808235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128332170821890876855744313 96249128116418157641808235)
    ·
      refine ⟨144373692174627236462712353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96249128116418157641808235 144373692174627236462712353)
      ·
        refine ⟨108280269130970427347034265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144373692174627236462712353 108280269130970427347034265)
        ·
          refine ⟨81210201848227820510275699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108280269130970427347034265 81210201848227820510275699)
          ·
            refine ⟨121815302772341730765413549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81210201848227820510275699 121815302772341730765413549)
            ·
              refine ⟨45680738539628149037030081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121815302772341730765413549 45680738539628149037030081)
              ·
                refine ⟨34260553904721111777772561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45680738539628149037030081 34260553904721111777772561)
                ·
                  refine ⟨25695415428540833833329421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34260553904721111777772561 25695415428540833833329421)
                  ·
                    refine ⟨9635780785702812687498533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25695415428540833833329421 9635780785702812687498533)
                    ·
                      refine ⟨1806708897319277378905975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9635780785702812687498533 1806708897319277378905975)
                      ·
                        rfl

theorem cell23_3518553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_3518553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518553 prefixEnd_3518553 := by exact prefixLift 3518553
  have htrace : WordTrace (prefixWord ++ tailWord_3518553) baseStart_3518553 baseEnd_3518553 := by
    simpa [prefixWord, tailWord_3518553, baseEnd_3518553] using wordTrace_append hprefix tailTrace_3518553
  have hstable : (prefixWord ++ tailWord_3518553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518553).length < 2 ^ (prefixWord ++ tailWord_3518553).sum := by decide
  have hdescent : baseEnd_3518553 < baseStart_3518553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518574 : List Nat := [4, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2]
def baseStart_3518574 : Nat := 118140960795 + 3518574 * 2 ^ 59
def prefixEnd_3518574 : Nat := 4983230072969 + 3 ^ 40 * 3518574 * 2
def baseEnd_3518574 : Nat := 1806719680413021796743379

theorem tailTrace_3518574 : CollatzResearch.WordTrace tailWord_3518574 prefixEnd_3518574 1806719680413021796743379 := by
  unfold tailWord_3518574
  simp only [CollatzResearch.WordTrace]
  refine ⟨16041617094351849680282347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85555291169876531628172517 16041617094351849680282347)
  ·
    refine ⟨24062425641527774520423521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16041617094351849680282347 24062425641527774520423521)
    ·
      refine ⟨18046819231145830890317641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24062425641527774520423521 18046819231145830890317641)
      ·
        refine ⟨13535114423359373167738231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18046819231145830890317641 13535114423359373167738231)
        ·
          refine ⟨20302671635039059751607347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13535114423359373167738231 20302671635039059751607347)
          ·
            refine ⟨30454007452558589627411021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20302671635039059751607347 30454007452558589627411021)
            ·
              refine ⟨11420252794709471110279133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30454007452558589627411021 11420252794709471110279133)
              ·
                refine ⟨4282594798016051666354675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11420252794709471110279133 4282594798016051666354675)
                ·
                  refine ⟨6423892197024077499532013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4282594798016051666354675 6423892197024077499532013)
                  ·
                    refine ⟨2408959573884029062324505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6423892197024077499532013 2408959573884029062324505)
                    ·
                      refine ⟨1806719680413021796743379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2408959573884029062324505 1806719680413021796743379)
                      ·
                        rfl

theorem cell23_3518574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_3518574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518574 prefixEnd_3518574 := by exact prefixLift 3518574
  have htrace : WordTrace (prefixWord ++ tailWord_3518574) baseStart_3518574 baseEnd_3518574 := by
    simpa [prefixWord, tailWord_3518574, baseEnd_3518574] using wordTrace_append hprefix tailTrace_3518574
  have hstable : (prefixWord ++ tailWord_3518574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518574).length < 2 ^ (prefixWord ++ tailWord_3518574).sum := by decide
  have hdescent : baseEnd_3518574 < baseStart_3518574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518610 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 7]
def baseStart_3518610 : Nat := 118140960795 + 3518610 * 2 ^ 59
def prefixEnd_3518610 : Nat := 4983230072969 + 3 ^ 40 * 3518610 * 2
def baseEnd_3518610 : Nat := 200748685079620406210357

theorem tailTrace_3518610 : CollatzResearch.WordTrace tailWord_3518610 prefixEnd_3518610 200748685079620406210357 := by
  unfold tailWord_3518610
  simp only [CollatzResearch.WordTrace]
  refine ⟨32083562445671093897642321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85556166521789583727046189 32083562445671093897642321)
  ·
    refine ⟨24062671834253320423231741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32083562445671093897642321 24062671834253320423231741)
    ·
      refine ⟨9023501937844995158711903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24062671834253320423231741 9023501937844995158711903)
      ·
        refine ⟨13535252906767492738067855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9023501937844995158711903 13535252906767492738067855)
        ·
          refine ⟨20302879360151239107101783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13535252906767492738067855 20302879360151239107101783)
          ·
            refine ⟨30454319040226858660652675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20302879360151239107101783 30454319040226858660652675)
            ·
              refine ⟨45681478560340287990979013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30454319040226858660652675 45681478560340287990979013)
              ·
                refine ⟨8565277230063803998308565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45681478560340287990979013 8565277230063803998308565)
                ·
                  refine ⟨200748685079620406210357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8565277230063803998308565 200748685079620406210357)
                  ·
                    rfl

theorem cell23_3518610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_3518610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518610 prefixEnd_3518610 := by exact prefixLift 3518610
  have htrace : WordTrace (prefixWord ++ tailWord_3518610) baseStart_3518610 baseEnd_3518610 := by
    simpa [prefixWord, tailWord_3518610, baseEnd_3518610] using wordTrace_append hprefix tailTrace_3518610
  have hstable : (prefixWord ++ tailWord_3518610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518610).length < 2 ^ (prefixWord ++ tailWord_3518610).sum := by decide
  have hdescent : baseEnd_3518610 < baseStart_3518610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518784 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 5, 2, 2]
def baseStart_3518784 : Nat := 118140960795 + 3518784 * 2 ^ 59
def prefixEnd_3518784 : Nat := 4983230072969 + 3 ^ 40 * 3518784 * 2
def baseEnd_3518784 : Nat := 1806827511350465975117413

theorem tailTrace_3518784 : CollatzResearch.WordTrace tailWord_3518784 prefixEnd_3518784 1806827511350465975117413 := by
  unfold tailWord_3518784
  simp only [CollatzResearch.WordTrace]
  refine ⟨64170298042027001653701703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85560397389369335538268937 64170298042027001653701703)
  ·
    refine ⟨96255447063040502480552555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64170298042027001653701703 96255447063040502480552555)
    ·
      refine ⟨144383170594560753720828833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96255447063040502480552555 144383170594560753720828833)
      ·
        refine ⟨108287377945920565290621625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144383170594560753720828833 108287377945920565290621625)
        ·
          refine ⟨81215533459440423967966219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108287377945920565290621625 81215533459440423967966219)
          ·
            refine ⟨121823300189160635951949329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81215533459440423967966219 121823300189160635951949329)
            ·
              refine ⟨91367475141870476963961997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121823300189160635951949329 91367475141870476963961997)
              ·
                refine ⟨34262803178201428861485749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91367475141870476963961997 34262803178201428861485749)
                ·
                  refine ⟨3212137797956383955764289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34262803178201428861485749 3212137797956383955764289)
                  ·
                    refine ⟨2409103348467287966823217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3212137797956383955764289 2409103348467287966823217)
                    ·
                      refine ⟨1806827511350465975117413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409103348467287966823217 1806827511350465975117413)
                      ·
                        rfl

theorem cell23_3518784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 5, 2, 2].length) (baseStart_3518784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518784 prefixEnd_3518784 := by exact prefixLift 3518784
  have htrace : WordTrace (prefixWord ++ tailWord_3518784) baseStart_3518784 baseEnd_3518784 := by
    simpa [prefixWord, tailWord_3518784, baseEnd_3518784] using wordTrace_append hprefix tailTrace_3518784
  have hstable : (prefixWord ++ tailWord_3518784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518784).length < 2 ^ (prefixWord ++ tailWord_3518784).sum := by decide
  have hdescent : baseEnd_3518784 < baseStart_3518784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518787 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 3]
def baseStart_3518787 : Nat := 118140960795 + 3518787 * 2 ^ 59
def prefixEnd_3518787 : Nat := 4983230072969 + 3 ^ 40 * 3518787 * 2
def baseEnd_3518787 : Nat := 1806829051792429463379899

theorem tailTrace_3518787 : CollatzResearch.WordTrace tailWord_3518787 prefixEnd_3518787 1806829051792429463379899 := by
  unfold tailWord_3518787
  simp only [CollatzResearch.WordTrace]
  refine ⟨128340705503043134819762615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85560470335362089879841743 128340705503043134819762615)
  ·
    refine ⟨192511058254564702229643923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128340705503043134819762615 192511058254564702229643923)
    ·
      refine ⟨288766587381847053344465885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192511058254564702229643923 288766587381847053344465885)
      ·
        refine ⟨108287470268192645004174707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288766587381847053344465885 108287470268192645004174707)
        ·
          refine ⟨162431205402288967506262061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108287470268192645004174707 162431205402288967506262061)
          ·
            refine ⟨60911702025858362814848273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162431205402288967506262061 60911702025858362814848273)
            ·
              refine ⟨45683776519393772111136205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60911702025858362814848273 45683776519393772111136205)
              ·
                refine ⟨17131416194772664541676077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45683776519393772111136205 17131416194772664541676077)
                ·
                  refine ⟨6424281073039749203128529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17131416194772664541676077 6424281073039749203128529)
                  ·
                    refine ⟨4818210804779811902346397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6424281073039749203128529 4818210804779811902346397)
                    ·
                      refine ⟨1806829051792429463379899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4818210804779811902346397 1806829051792429463379899)
                      ·
                        rfl

theorem cell23_3518787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_3518787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518787 prefixEnd_3518787 := by exact prefixLift 3518787
  have htrace : WordTrace (prefixWord ++ tailWord_3518787) baseStart_3518787 baseEnd_3518787 := by
    simpa [prefixWord, tailWord_3518787, baseEnd_3518787] using wordTrace_append hprefix tailTrace_3518787
  have hstable : (prefixWord ++ tailWord_3518787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518787).length < 2 ^ (prefixWord ++ tailWord_3518787).sum := by decide
  have hdescent : baseEnd_3518787 < baseStart_3518787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518804 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_3518804 : Nat := 118140960795 + 3518804 * 2 ^ 59
def prefixEnd_3518804 : Nat := 4983230072969 + 3 ^ 40 * 3518804 * 2
def baseEnd_3518804 : Nat := 1806837780963555896867321

theorem tailTrace_3518804 : CollatzResearch.WordTrace tailWord_3518804 prefixEnd_3518804 1806837780963555896867321 := by
  unfold tailWord_3518804
  simp only [CollatzResearch.WordTrace]
  refine ⟨64170662771990773361565733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85560883695987697815420977 64170662771990773361565733)
  ·
    refine ⟨12031999269748270005293575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64170662771990773361565733 12031999269748270005293575)
    ·
      refine ⟨18047998904622405007940363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12031999269748270005293575 18047998904622405007940363)
      ·
        refine ⟨27071998356933607511910545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18047998904622405007940363 27071998356933607511910545)
        ·
          refine ⟨20303998767700205633932909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27071998356933607511910545 20303998767700205633932909)
          ·
            refine ⟨7613999537887577112724841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20303998767700205633932909 7613999537887577112724841)
            ·
              refine ⟨5710499653415682834543631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7613999537887577112724841 5710499653415682834543631)
              ·
                refine ⟨8565749480123524251815447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5710499653415682834543631 8565749480123524251815447)
                ·
                  refine ⟨12848624220185286377723171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8565749480123524251815447 12848624220185286377723171)
                  ·
                    refine ⟨19272936330277929566584757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12848624220185286377723171 19272936330277929566584757)
                    ·
                      refine ⟨1806837780963555896867321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19272936330277929566584757 1806837780963555896867321)
                      ·
                        rfl

theorem cell23_3518804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_3518804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518804 prefixEnd_3518804 := by exact prefixLift 3518804
  have htrace : WordTrace (prefixWord ++ tailWord_3518804) baseStart_3518804 baseEnd_3518804 := by
    simpa [prefixWord, tailWord_3518804, baseEnd_3518804] using wordTrace_append hprefix tailTrace_3518804
  have hstable : (prefixWord ++ tailWord_3518804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518804).length < 2 ^ (prefixWord ++ tailWord_3518804).sum := by decide
  have hdescent : baseEnd_3518804 < baseStart_3518804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518812 : List Nat := [2, 2, 4, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_3518812 : Nat := 118140960795 + 3518812 * 2 ^ 59
def prefixEnd_3518812 : Nat := 4983230072969 + 3 ^ 40 * 3518812 * 2
def baseEnd_3518812 : Nat := 1806841888808791865567285

theorem tailTrace_3518812 : CollatzResearch.WordTrace tailWord_3518812 prefixEnd_3518812 1806841888808791865567285 := by
  unfold tailWord_3518812
  simp only [CollatzResearch.WordTrace]
  refine ⟨64170808663976282044711345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85561078218635042726281793 64170808663976282044711345)
  ·
    refine ⟨48128106497982211533533509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64170808663976282044711345 48128106497982211533533509)
    ·
      refine ⟨9024019968371664662537533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48128106497982211533533509 9024019968371664662537533)
      ·
        refine ⟨3384007488139374248451575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9024019968371664662537533 3384007488139374248451575)
        ·
          refine ⟨5076011232209061372677363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3384007488139374248451575 5076011232209061372677363)
          ·
            refine ⟨7614016848313592059016045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5076011232209061372677363 7614016848313592059016045)
            ·
              refine ⟨2855256318117597022131017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7614016848313592059016045 2855256318117597022131017)
              ·
                refine ⟨2141442238588197766598263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2855256318117597022131017 2141442238588197766598263)
                ·
                  refine ⟨3212163357882296649897395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2141442238588197766598263 3212163357882296649897395)
                  ·
                    refine ⟨4818245036823444974846093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3212163357882296649897395 4818245036823444974846093)
                    ·
                      refine ⟨1806841888808791865567285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4818245036823444974846093 1806841888808791865567285)
                      ·
                        rfl

theorem cell23_3518812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_3518812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518812 prefixEnd_3518812 := by exact prefixLift 3518812
  have htrace : WordTrace (prefixWord ++ tailWord_3518812) baseStart_3518812 baseEnd_3518812 := by
    simpa [prefixWord, tailWord_3518812, baseEnd_3518812] using wordTrace_append hprefix tailTrace_3518812
  have hstable : (prefixWord ++ tailWord_3518812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518812).length < 2 ^ (prefixWord ++ tailWord_3518812).sum := by decide
  have hdescent : baseEnd_3518812 < baseStart_3518812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518818 : List Nat := [3, 3, 2, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_3518818 : Nat := 118140960795 + 3518818 * 2 ^ 59
def prefixEnd_3518818 : Nat := 4983230072969 + 3 ^ 40 * 3518818 * 2
def baseEnd_3518818 : Nat := 1806844969692718842092257

theorem tailTrace_3518818 : CollatzResearch.WordTrace tailWord_3518818 prefixEnd_3518818 1806844969692718842092257 := by
  unfold tailWord_3518818
  simp only [CollatzResearch.WordTrace]
  refine ⟨32085459041482706778535277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85561224110620551409427405 32085459041482706778535277)
  ·
    refine ⟨12032047140556015041950729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32085459041482706778535277 12032047140556015041950729)
    ·
      refine ⟨9024035355417011281463047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12032047140556015041950729 9024035355417011281463047)
      ·
        refine ⟨13536053033125516922194571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9024035355417011281463047 13536053033125516922194571)
        ·
          refine ⟨20304079549688275383291857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13536053033125516922194571 20304079549688275383291857)
          ·
            refine ⟨15228059662266206537468893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20304079549688275383291857 15228059662266206537468893)
            ·
              refine ⟨5710522373349827451550835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15228059662266206537468893 5710522373349827451550835)
              ·
                refine ⟨8565783560024741177326253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5710522373349827451550835 8565783560024741177326253)
                ·
                  refine ⟨3212168835009277941497345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8565783560024741177326253 3212168835009277941497345)
                  ·
                    refine ⟨2409126626256958456123009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3212168835009277941497345 2409126626256958456123009)
                    ·
                      refine ⟨1806844969692718842092257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409126626256958456123009 1806844969692718842092257)
                      ·
                        rfl

theorem cell23_3518818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_3518818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518818 prefixEnd_3518818 := by exact prefixLift 3518818
  have htrace : WordTrace (prefixWord ++ tailWord_3518818) baseStart_3518818 baseEnd_3518818 := by
    simpa [prefixWord, tailWord_3518818, baseEnd_3518818] using wordTrace_append hprefix tailTrace_3518818
  have hstable : (prefixWord ++ tailWord_3518818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518818).length < 2 ^ (prefixWord ++ tailWord_3518818).sum := by decide
  have hdescent : baseEnd_3518818 < baseStart_3518818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518828 : List Nat := [2, 2, 1, 1, 6, 2, 2, 1, 2, 4]
def baseStart_3518828 : Nat := 118140960795 + 3518828 * 2 ^ 59
def prefixEnd_3518828 : Nat := 4983230072969 + 3 ^ 40 * 3518828 * 2
def baseEnd_3518828 : Nat := 602283368166421267655737

theorem tailTrace_3518828 : CollatzResearch.WordTrace tailWord_3518828 prefixEnd_3518828 602283368166421267655737 := by
  unfold tailWord_3518828
  simp only [CollatzResearch.WordTrace]
  refine ⟨64171100447947299411002569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85561467263929732548003425 64171100447947299411002569)
  ·
    refine ⟨48128325335960474558251927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64171100447947299411002569 48128325335960474558251927)
    ·
      refine ⟨72192488003940711837377891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48128325335960474558251927 72192488003940711837377891)
      ·
        refine ⟨108288732005911067756066837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72192488003940711837377891 108288732005911067756066837)
        ·
          refine ⟨5076034312777081301065633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108288732005911067756066837 5076034312777081301065633)
          ·
            refine ⟨3807025734582810975799225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5076034312777081301065633 3807025734582810975799225)
            ·
              refine ⟨2855269300937108231849419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3807025734582810975799225 2855269300937108231849419)
              ·
                refine ⟨4282903951405662347774129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855269300937108231849419 4282903951405662347774129)
                ·
                  refine ⟨3212177963554246760830597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4282903951405662347774129 3212177963554246760830597)
                  ·
                    refine ⟨602283368166421267655737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3212177963554246760830597 602283368166421267655737)
                    ·
                      rfl

theorem cell23_3518828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 4].length) (baseStart_3518828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518828 prefixEnd_3518828 := by exact prefixLift 3518828
  have htrace : WordTrace (prefixWord ++ tailWord_3518828) baseStart_3518828 baseEnd_3518828 := by
    simpa [prefixWord, tailWord_3518828, baseEnd_3518828] using wordTrace_append hprefix tailTrace_3518828
  have hstable : (prefixWord ++ tailWord_3518828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518828).length < 2 ^ (prefixWord ++ tailWord_3518828).sum := by decide
  have hdescent : baseEnd_3518828 < baseStart_3518828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518838 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3518838 : Nat := 118140960795 + 3518838 * 2 ^ 59
def prefixEnd_3518838 : Nat := 4983230072969 + 3 ^ 40 * 3518838 * 2
def baseEnd_3518838 : Nat := 1806855239305808763842165

theorem tailTrace_3518838 : CollatzResearch.WordTrace tailWord_3518838 prefixEnd_3518838 1806855239305808763842165 := by
  unfold tailWord_3518838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8021410351616148158116823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85561710417238913686579445 8021410351616148158116823)
  ·
    refine ⟨12032115527424222237175235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8021410351616148158116823 12032115527424222237175235)
    ·
      refine ⟨18048173291136333355762853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12032115527424222237175235 18048173291136333355762853)
      ·
        refine ⟨3384032492088062504205535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18048173291136333355762853 3384032492088062504205535)
        ·
          refine ⟨5076048738132093756308303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3384032492088062504205535 5076048738132093756308303)
          ·
            refine ⟨7614073107198140634462455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5076048738132093756308303 7614073107198140634462455)
            ·
              refine ⟨11421109660797210951693683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7614073107198140634462455 11421109660797210951693683)
              ·
                refine ⟨17131664491195816427540525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11421109660797210951693683 17131664491195816427540525)
                ·
                  refine ⟨6424374184198431160327697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17131664491195816427540525 6424374184198431160327697)
                  ·
                    refine ⟨4818280638148823370245773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6424374184198431160327697 4818280638148823370245773)
                    ·
                      refine ⟨1806855239305808763842165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4818280638148823370245773 1806855239305808763842165)
                      ·
                        rfl

theorem cell23_3518838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3518838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518838 prefixEnd_3518838 := by exact prefixLift 3518838
  have htrace : WordTrace (prefixWord ++ tailWord_3518838) baseStart_3518838 baseEnd_3518838 := by
    simpa [prefixWord, tailWord_3518838, baseEnd_3518838] using wordTrace_append hprefix tailTrace_3518838
  have hstable : (prefixWord ++ tailWord_3518838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518838).length < 2 ^ (prefixWord ++ tailWord_3518838).sum := by decide
  have hdescent : baseEnd_3518838 < baseStart_3518838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518878 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_3518878 : Nat := 118140960795 + 3518878 * 2 ^ 59
def prefixEnd_3518878 : Nat := 4983230072969 + 3 ^ 40 * 3518878 * 2
def baseEnd_3518878 : Nat := 1806875778531988607341981

theorem tailTrace_3518878 : CollatzResearch.WordTrace tailWord_3518878 prefixEnd_3518878 1806875778531988607341981 := by
  unfold tailWord_3518878
  simp only [CollatzResearch.WordTrace]
  refine ⟨16043003068214182170165661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85562683030475638240883525 16043003068214182170165661)
  ·
    refine ⟨6016126150580318313812123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16043003068214182170165661 6016126150580318313812123)
    ·
      refine ⟨9024189225870477470718185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6016126150580318313812123 9024189225870477470718185)
      ·
        refine ⟨6768141919402858103038639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9024189225870477470718185 6768141919402858103038639)
        ·
          refine ⟨10152212879104287154557959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6768141919402858103038639 10152212879104287154557959)
          ·
            refine ⟨15228319318656430731836939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10152212879104287154557959 15228319318656430731836939)
            ·
              refine ⟨22842478977984646097755409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15228319318656430731836939 22842478977984646097755409)
              ·
                refine ⟨17131859233488484573316557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22842478977984646097755409 17131859233488484573316557)
                ·
                  refine ⟨6424447212558181714993709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17131859233488484573316557 6424447212558181714993709)
                  ·
                    refine ⟨2409167704709318143122641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6424447212558181714993709 2409167704709318143122641)
                    ·
                      refine ⟨1806875778531988607341981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409167704709318143122641 1806875778531988607341981)
                      ·
                        rfl

theorem cell23_3518878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_3518878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518878 prefixEnd_3518878 := by exact prefixLift 3518878
  have htrace : WordTrace (prefixWord ++ tailWord_3518878) baseStart_3518878 baseEnd_3518878 := by
    simpa [prefixWord, tailWord_3518878, baseEnd_3518878] using wordTrace_append hprefix tailTrace_3518878
  have hstable : (prefixWord ++ tailWord_3518878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518878).length < 2 ^ (prefixWord ++ tailWord_3518878).sum := by decide
  have hdescent : baseEnd_3518878 < baseStart_3518878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518897 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 9]
def baseStart_3518897 : Nat := 118140960795 + 3518897 * 2 ^ 59
def prefixEnd_3518897 : Nat := 4983230072969 + 3 ^ 40 * 3518897 * 2
def baseEnd_3518897 : Nat := 200765059407158225889377

theorem tailTrace_3518897 : CollatzResearch.WordTrace tailWord_3518897 prefixEnd_3518897 200765059407158225889377 := by
  unfold tailWord_3518897
  simp only [CollatzResearch.WordTrace]
  refine ⟨128344717532644623606266945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85563145021763082404177963 128344717532644623606266945)
  ·
    refine ⟨96258538149483467704700209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128344717532644623606266945 96258538149483467704700209)
    ·
      refine ⟨72193903612112600778525157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96258538149483467704700209 72193903612112600778525157)
      ·
        refine ⟨13536356927271112645973467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72193903612112600778525157 13536356927271112645973467)
        ·
          refine ⟨20304535390906668968960201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13536356927271112645973467 20304535390906668968960201)
          ·
            refine ⟨15228401543180001726720151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20304535390906668968960201 15228401543180001726720151)
            ·
              refine ⟨22842602314770002590080227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15228401543180001726720151 22842602314770002590080227)
              ·
                refine ⟨34263903472155003885120341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22842602314770002590080227 34263903472155003885120341)
                ·
                  refine ⟨200765059407158225889377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34263903472155003885120341 200765059407158225889377)
                  ·
                    rfl

theorem cell23_3518897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 9].length) (baseStart_3518897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518897 prefixEnd_3518897 := by exact prefixLift 3518897
  have htrace : WordTrace (prefixWord ++ tailWord_3518897) baseStart_3518897 baseEnd_3518897 := by
    simpa [prefixWord, tailWord_3518897, baseEnd_3518897] using wordTrace_append hprefix tailTrace_3518897
  have hstable : (prefixWord ++ tailWord_3518897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518897).length < 2 ^ (prefixWord ++ tailWord_3518897).sum := by decide
  have hdescent : baseEnd_3518897 < baseStart_3518897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518927 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 4, 5]
def baseStart_3518927 : Nat := 118140960795 + 3518927 * 2 ^ 59
def prefixEnd_3518927 : Nat := 4983230072969 + 3 ^ 40 * 3518927 * 2
def baseEnd_3518927 : Nat := 602300313028019638543085

theorem tailTrace_3518927 : CollatzResearch.WordTrace tailWord_3518927 prefixEnd_3518927 602300313028019638543085 := by
  unfold tailWord_3518927
  simp only [CollatzResearch.WordTrace]
  refine ⟨128345811722535938729859035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85563874481690625819906023 128345811722535938729859035)
  ·
    refine ⟨192518717583803908094788553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128345811722535938729859035 192518717583803908094788553)
    ·
      refine ⟨144389038187852931071091415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192518717583803908094788553 144389038187852931071091415)
      ·
        refine ⟨216583557281779396606637123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144389038187852931071091415 216583557281779396606637123)
        ·
          refine ⟨324875335922669094909955685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216583557281779396606637123 324875335922669094909955685)
          ·
            refine ⟨60914125485500455295616691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 324875335922669094909955685 60914125485500455295616691)
            ·
              refine ⟨91371188228250682943425037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60914125485500455295616691 91371188228250682943425037)
              ·
                refine ⟨34264195585594006103784389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91371188228250682943425037 34264195585594006103784389)
                ·
                  refine ⟨6424536672298876144459573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34264195585594006103784389 6424536672298876144459573)
                  ·
                    refine ⟨602300313028019638543085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6424536672298876144459573 602300313028019638543085)
                    ·
                      rfl

theorem cell23_3518927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 5].length) (baseStart_3518927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518927 prefixEnd_3518927 := by exact prefixLift 3518927
  have htrace : WordTrace (prefixWord ++ tailWord_3518927) baseStart_3518927 baseEnd_3518927 := by
    simpa [prefixWord, tailWord_3518927, baseEnd_3518927] using wordTrace_append hprefix tailTrace_3518927
  have hstable : (prefixWord ++ tailWord_3518927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518927).length < 2 ^ (prefixWord ++ tailWord_3518927).sum := by decide
  have hdescent : baseEnd_3518927 < baseStart_3518927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518937 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 7]
def baseStart_3518937 : Nat := 118140960795 + 3518937 * 2 ^ 59
def prefixEnd_3518937 : Nat := 4983230072969 + 3 ^ 40 * 3518937 * 2
def baseEnd_3518937 : Nat := 1806906073890603876504209

theorem tailTrace_3518937 : CollatzResearch.WordTrace tailWord_3518937 prefixEnd_3518937 1806906073890603876504209 := by
  unfold tailWord_3518937
  simp only [CollatzResearch.WordTrace]
  refine ⟨128346176452499710437723065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85564117634999806958482043 128346176452499710437723065)
  ·
    refine ⟨96259632339374782828292299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128346176452499710437723065 96259632339374782828292299)
    ·
      refine ⟨144389448509062174242438449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96259632339374782828292299 144389448509062174242438449)
      ·
        refine ⟨108292086381796630681828837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144389448509062174242438449 108292086381796630681828837)
        ·
          refine ⟨20304766196586868252842907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108292086381796630681828837 20304766196586868252842907)
          ·
            refine ⟨30457149294880302379264361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20304766196586868252842907 30457149294880302379264361)
            ·
              refine ⟨22842861971160226784448271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30457149294880302379264361 22842861971160226784448271)
              ·
                refine ⟨34264292956740340176672407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22842861971160226784448271 34264292956740340176672407)
                ·
                  refine ⟨51396439435110510265008611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34264292956740340176672407 51396439435110510265008611)
                  ·
                    refine ⟨77094659152665765397512917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51396439435110510265008611 77094659152665765397512917)
                    ·
                      refine ⟨1806906073890603876504209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77094659152665765397512917 1806906073890603876504209)
                      ·
                        rfl

theorem cell23_3518937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_3518937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518937 prefixEnd_3518937 := by exact prefixLift 3518937
  have htrace : WordTrace (prefixWord ++ tailWord_3518937) baseStart_3518937 baseEnd_3518937 := by
    simpa [prefixWord, tailWord_3518937, baseEnd_3518937] using wordTrace_append hprefix tailTrace_3518937
  have hstable : (prefixWord ++ tailWord_3518937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518937).length < 2 ^ (prefixWord ++ tailWord_3518937).sum := by decide
  have hdescent : baseEnd_3518937 < baseStart_3518937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518965 : List Nat := [1, 3, 5, 1, 2, 2, 1, 3, 5]
def baseStart_3518965 : Nat := 118140960795 + 3518965 * 2 ^ 59
def prefixEnd_3518965 : Nat := 4983230072969 + 3 ^ 40 * 3518965 * 2
def baseEnd_3518965 : Nat := 200768939038769974106009

theorem tailTrace_3518965 : CollatzResearch.WordTrace tailWord_3518965 prefixEnd_3518965 200768939038769974106009 := by
  unfold tailWord_3518965
  simp only [CollatzResearch.WordTrace]
  refine ⟨128347197696398271219742349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85564798464265514146494899 128347197696398271219742349)
  ·
    refine ⟨48130199136149351707403381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128347197696398271219742349 48130199136149351707403381)
    ·
      refine ⟨4512206169014001722569067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48130199136149351707403381 4512206169014001722569067)
      ·
        refine ⟨6768309253521002583853601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4512206169014001722569067 6768309253521002583853601)
        ·
          refine ⟨5076231940140751937890201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6768309253521002583853601 5076231940140751937890201)
          ·
            refine ⟨3807173955105563953417651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5076231940140751937890201 3807173955105563953417651)
            ·
              refine ⟨5710760932658345930126477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3807173955105563953417651 5710760932658345930126477)
              ·
                refine ⟨2141535349746879723797429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5710760932658345930126477 2141535349746879723797429)
                ·
                  refine ⟨200768939038769974106009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2141535349746879723797429 200768939038769974106009)
                  ·
                    rfl

theorem cell23_3518965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 5].length) (baseStart_3518965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518965 prefixEnd_3518965 := by exact prefixLift 3518965
  have htrace : WordTrace (prefixWord ++ tailWord_3518965) baseStart_3518965 baseEnd_3518965 := by
    simpa [prefixWord, tailWord_3518965, baseEnd_3518965] using wordTrace_append hprefix tailTrace_3518965
  have hstable : (prefixWord ++ tailWord_3518965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518965).length < 2 ^ (prefixWord ++ tailWord_3518965).sum := by decide
  have hdescent : baseEnd_3518965 < baseStart_3518965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518978 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_3518978 : Nat := 118140960795 + 3518978 * 2 ^ 59
def prefixEnd_3518978 : Nat := 4983230072969 + 3 ^ 40 * 3518978 * 2
def baseEnd_3518978 : Nat := 602309042199146072030507

theorem tailTrace_3518978 : CollatzResearch.WordTrace tailWord_3518978 prefixEnd_3518978 602309042199146072030507 := by
  unfold tailWord_3518978
  simp only [CollatzResearch.WordTrace]
  refine ⟨32086917961337793609991397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85565114563567449626643725 32086917961337793609991397)
  ·
    refine ⟨6016297117750836301873387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32086917961337793609991397 6016297117750836301873387)
    ·
      refine ⟨9024445676626254452810081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6016297117750836301873387 9024445676626254452810081)
      ·
        refine ⟨6768334257469690839607561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9024445676626254452810081 6768334257469690839607561)
        ·
          refine ⟨5076250693102268129705671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6768334257469690839607561 5076250693102268129705671)
          ·
            refine ⟨7614376039653402194558507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5076250693102268129705671 7614376039653402194558507)
            ·
              refine ⟨11421564059480103291837761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7614376039653402194558507 11421564059480103291837761)
              ·
                refine ⟨8566173044610077468878321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11421564059480103291837761 8566173044610077468878321)
                ·
                  refine ⟨6424629783457558101658741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8566173044610077468878321 6424629783457558101658741)
                  ·
                    refine ⟨602309042199146072030507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6424629783457558101658741 602309042199146072030507)
                    ·
                      rfl

theorem cell23_3518978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_3518978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3518978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3518978 prefixEnd_3518978 := by exact prefixLift 3518978
  have htrace : WordTrace (prefixWord ++ tailWord_3518978) baseStart_3518978 baseEnd_3518978 := by
    simpa [prefixWord, tailWord_3518978, baseEnd_3518978] using wordTrace_append hprefix tailTrace_3518978
  have hstable : (prefixWord ++ tailWord_3518978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518978).length < 2 ^ (prefixWord ++ tailWord_3518978).sum := by decide
  have hdescent : baseEnd_3518978 < baseStart_3518978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519015 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3519015 : Nat := 118140960795 + 3519015 * 2 ^ 59
def prefixEnd_3519015 : Nat := 4983230072969 + 3 ^ 40 * 3519015 * 2
def baseEnd_3519015 : Nat := 1806946125381654571328851

theorem tailTrace_3519015 : CollatzResearch.WordTrace tailWord_3519015 prefixEnd_3519015 1806946125381654571328851 := by
  unfold tailWord_3519015
  simp only [CollatzResearch.WordTrace]
  refine ⟨128349021346217129759062499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85566014230811419839374999 128349021346217129759062499)
  ·
    refine ⟨192523532019325694638593749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128349021346217129759062499 192523532019325694638593749)
    ·
      refine ⟨4512270281702945968092041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 192523532019325694638593749 4512270281702945968092041)
      ·
        refine ⟨3384202711277209476069031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4512270281702945968092041 3384202711277209476069031)
        ·
          refine ⟨5076304066915814214103547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3384202711277209476069031 5076304066915814214103547)
          ·
            refine ⟨7614456100373721321155321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5076304066915814214103547 7614456100373721321155321)
            ·
              refine ⟨5710842075280290990866491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7614456100373721321155321 5710842075280290990866491)
              ·
                refine ⟨8566263112920436486299737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5710842075280290990866491 8566263112920436486299737)
                ·
                  refine ⟨6424697334690327364724803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8566263112920436486299737 6424697334690327364724803)
                  ·
                    refine ⟨9637046002035491047087205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6424697334690327364724803 9637046002035491047087205)
                    ·
                      refine ⟨1806946125381654571328851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9637046002035491047087205 1806946125381654571328851)
                      ·
                        rfl

theorem cell23_3519015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3519015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519015 prefixEnd_3519015 := by exact prefixLift 3519015
  have htrace : WordTrace (prefixWord ++ tailWord_3519015) baseStart_3519015 baseEnd_3519015 := by
    simpa [prefixWord, tailWord_3519015, baseEnd_3519015] using wordTrace_append hprefix tailTrace_3519015
  have hstable : (prefixWord ++ tailWord_3519015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519015).length < 2 ^ (prefixWord ++ tailWord_3519015).sum := by decide
  have hdescent : baseEnd_3519015 < baseStart_3519015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519018 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_3519018 : Nat := 118140960795 + 3519018 * 2 ^ 59
def prefixEnd_3519018 : Nat := 4983230072969 + 3 ^ 40 * 3519018 * 2
def baseEnd_3519018 : Nat := 1806947665823618059591337

theorem tailTrace_3519018 : CollatzResearch.WordTrace tailWord_3519018 prefixEnd_3519018 1806947665823618059591337 := by
  unfold tailWord_3519018
  simp only [CollatzResearch.WordTrace]
  refine ⟨32087282691301565317855427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85566087176804174180947805 32087282691301565317855427)
  ·
    refine ⟨48130924036952347976783141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32087282691301565317855427 48130924036952347976783141)
    ·
      refine ⟨9024548256928565245646839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48130924036952347976783141 9024548256928565245646839)
      ·
        refine ⟨13536822385392847868470259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9024548256928565245646839 13536822385392847868470259)
        ·
          refine ⟨20305233578089271802705389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13536822385392847868470259 20305233578089271802705389)
          ·
            refine ⟨7614462591783476926014521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20305233578089271802705389 7614462591783476926014521)
            ·
              refine ⟨5710846943837607694510891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7614462591783476926014521 5710846943837607694510891)
              ·
                refine ⟨8566270415756411541766337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5710846943837607694510891 8566270415756411541766337)
                ·
                  refine ⟨6424702811817308656324753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8566270415756411541766337 6424702811817308656324753)
                  ·
                    refine ⟨4818527108862981492243565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6424702811817308656324753 4818527108862981492243565)
                    ·
                      refine ⟨1806947665823618059591337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4818527108862981492243565 1806947665823618059591337)
                      ·
                        rfl

theorem cell23_3519018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_3519018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519018 prefixEnd_3519018 := by exact prefixLift 3519018
  have htrace : WordTrace (prefixWord ++ tailWord_3519018) baseStart_3519018 baseEnd_3519018 := by
    simpa [prefixWord, tailWord_3519018, baseEnd_3519018] using wordTrace_append hprefix tailTrace_3519018
  have hstable : (prefixWord ++ tailWord_3519018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519018).length < 2 ^ (prefixWord ++ tailWord_3519018).sum := by decide
  have hdescent : baseEnd_3519018 < baseStart_3519018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519064 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 1, 6]
def baseStart_3519064 : Nat := 118140960795 + 3519064 * 2 ^ 59
def prefixEnd_3519064 : Nat := 4983230072969 + 3 ^ 40 * 3519064 * 2
def baseEnd_3519064 : Nat := 602323761977908293205375

theorem tailTrace_3519064 : CollatzResearch.WordTrace tailWord_3519064 prefixEnd_3519064 602323761977908293205375 := by
  unfold tailWord_3519064
  simp only [CollatzResearch.WordTrace]
  refine ⟨64175404261519805563798123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85567205682026407418397497 64175404261519805563798123)
  ·
    refine ⟨96263106392279708345697185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64175404261519805563798123 96263106392279708345697185)
    ·
      refine ⟨72197329794209781259272889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96263106392279708345697185 72197329794209781259272889)
      ·
        refine ⟨54147997345657335944454667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72197329794209781259272889 54147997345657335944454667)
        ·
          refine ⟨81221996018486003916682001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54147997345657335944454667 81221996018486003916682001)
          ·
            refine ⟨60916497013864502937511501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81221996018486003916682001 60916497013864502937511501)
            ·
              refine ⟨22843686380199188601566813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60916497013864502937511501 22843686380199188601566813)
              ·
                refine ⟨8566382392574695725587555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22843686380199188601566813 8566382392574695725587555)
                ·
                  refine ⟨12849573588862043588381333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8566382392574695725587555 12849573588862043588381333)
                  ·
                    refine ⟨602323761977908293205375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12849573588862043588381333 602323761977908293205375)
                    ·
                      rfl

theorem cell23_3519064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_3519064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519064 prefixEnd_3519064 := by exact prefixLift 3519064
  have htrace : WordTrace (prefixWord ++ tailWord_3519064) baseStart_3519064 baseEnd_3519064 := by
    simpa [prefixWord, tailWord_3519064, baseEnd_3519064] using wordTrace_append hprefix tailTrace_3519064
  have hstable : (prefixWord ++ tailWord_3519064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519064).length < 2 ^ (prefixWord ++ tailWord_3519064).sum := by decide
  have hdescent : baseEnd_3519064 < baseStart_3519064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519085 : List Nat := [1, 5, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_3519085 : Nat := 118140960795 + 3519085 * 2 ^ 59
def prefixEnd_3519085 : Nat := 4983230072969 + 3 ^ 40 * 3519085 * 2
def baseEnd_3519085 : Nat := 602327356342489765817843

theorem tailTrace_3519085 : CollatzResearch.WordTrace tailWord_3519085 prefixEnd_3519085 602327356342489765817843 := by
  unfold tailWord_3519085
  simp only [CollatzResearch.WordTrace]
  refine ⟨128351574455963531714110709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85567716303975687809407139 128351574455963531714110709)
  ·
    refine ⟨12032960105246581098197879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128351574455963531714110709 12032960105246581098197879)
    ·
      refine ⟨18049440157869871647296819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12032960105246581098197879 18049440157869871647296819)
      ·
        refine ⟨27074160236804807470945229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18049440157869871647296819 27074160236804807470945229)
        ·
          refine ⟨10152810088801802801604461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27074160236804807470945229 10152810088801802801604461)
          ·
            refine ⟨3807303783300676050601673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10152810088801802801604461 3807303783300676050601673)
            ·
              refine ⟨2855477837475507037951255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3807303783300676050601673 2855477837475507037951255)
              ·
                refine ⟨4283216756213260556926883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855477837475507037951255 4283216756213260556926883)
                ·
                  refine ⟨6424825134319890835390325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4283216756213260556926883 6424825134319890835390325)
                  ·
                    refine ⟨602327356342489765817843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6424825134319890835390325 602327356342489765817843)
                    ·
                      rfl

theorem cell23_3519085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_3519085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519085 prefixEnd_3519085 := by exact prefixLift 3519085
  have htrace : WordTrace (prefixWord ++ tailWord_3519085) baseStart_3519085 baseEnd_3519085 := by
    simpa [prefixWord, tailWord_3519085, baseEnd_3519085] using wordTrace_append hprefix tailTrace_3519085
  have hstable : (prefixWord ++ tailWord_3519085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519085).length < 2 ^ (prefixWord ++ tailWord_3519085).sum := by decide
  have hdescent : baseEnd_3519085 < baseStart_3519085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519088 : List Nat := [2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 4]
def baseStart_3519088 : Nat := 118140960795 + 3519088 * 2 ^ 59
def prefixEnd_3519088 : Nat := 4983230072969 + 3 ^ 40 * 3519088 * 2
def baseEnd_3519088 : Nat := 1806983609469432785716015

theorem tailTrace_3519088 : CollatzResearch.WordTrace tailWord_3519088 prefixEnd_3519088 1806983609469432785716015 := by
  unfold tailWord_3519088
  simp only [CollatzResearch.WordTrace]
  refine ⟨64175841937476331613234959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85567789249968442150979945 64175841937476331613234959)
  ·
    refine ⟨96263762906214497419852439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64175841937476331613234959 96263762906214497419852439)
    ·
      refine ⟨144395644359321746129778659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96263762906214497419852439 144395644359321746129778659)
      ·
        refine ⟨216593466538982619194667989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144395644359321746129778659 216593466538982619194667989)
        ·
          refine ⟨5076409372007405137375031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 216593466538982619194667989 5076409372007405137375031)
          ·
            refine ⟨7614614058011107706062547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5076409372007405137375031 7614614058011107706062547)
            ·
              refine ⟨11421921087016661559093821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7614614058011107706062547 11421921087016661559093821)
              ·
                refine ⟨4283220407631248084660183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11421921087016661559093821 4283220407631248084660183)
                ·
                  refine ⟨6424830611446872126990275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4283220407631248084660183 6424830611446872126990275)
                  ·
                    refine ⟨9637245917170308190485413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6424830611446872126990275 9637245917170308190485413)
                    ·
                      refine ⟨1806983609469432785716015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9637245917170308190485413 1806983609469432785716015)
                      ·
                        rfl

theorem cell23_3519088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 4].length) (baseStart_3519088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519088 prefixEnd_3519088 := by exact prefixLift 3519088
  have htrace : WordTrace (prefixWord ++ tailWord_3519088) baseStart_3519088 baseEnd_3519088 := by
    simpa [prefixWord, tailWord_3519088, baseEnd_3519088] using wordTrace_append hprefix tailTrace_3519088
  have hstable : (prefixWord ++ tailWord_3519088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519088).length < 2 ^ (prefixWord ++ tailWord_3519088).sum := by decide
  have hdescent : baseEnd_3519088 < baseStart_3519088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519105 : List Nat := [1, 2, 4, 2, 1, 1, 4, 1, 3, 2, 2]
def baseStart_3519105 : Nat := 118140960795 + 3519105 * 2 ^ 59
def prefixEnd_3519105 : Nat := 4983230072969 + 3 ^ 40 * 3519105 * 2
def baseEnd_3519105 : Nat := 1806992338640559219203437

theorem tailTrace_3519105 : CollatzResearch.WordTrace tailWord_3519105 prefixEnd_3519105 1806992338640559219203437 := by
  unfold tailWord_3519105
  simp only [CollatzResearch.WordTrace]
  refine ⟨128352303915891075129838769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85568202610594050086559179 128352303915891075129838769)
  ·
    refine ⟨96264227936918306347379077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128352303915891075129838769 96264227936918306347379077)
    ·
      refine ⟨18049542738172182440133577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96264227936918306347379077 18049542738172182440133577)
      ·
        refine ⟨13537157053629136830100183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18049542738172182440133577 13537157053629136830100183)
        ·
          refine ⟨20305735580443705245150275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13537157053629136830100183 20305735580443705245150275)
          ·
            refine ⟨30458603370665557867725413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20305735580443705245150275 30458603370665557867725413)
            ·
              refine ⟨5710988131999792100198515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30458603370665557867725413 5710988131999792100198515)
              ·
                refine ⟨8566482197999688150297773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5710988131999792100198515 8566482197999688150297773)
                ·
                  refine ⟨3212430824249883056361665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8566482197999688150297773 3212430824249883056361665)
                  ·
                    refine ⟨2409323118187412292271249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3212430824249883056361665 2409323118187412292271249)
                    ·
                      refine ⟨1806992338640559219203437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409323118187412292271249 1806992338640559219203437)
                      ·
                        rfl

theorem cell23_3519105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_3519105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519105 prefixEnd_3519105 := by exact prefixLift 3519105
  have htrace : WordTrace (prefixWord ++ tailWord_3519105) baseStart_3519105 baseEnd_3519105 := by
    simpa [prefixWord, tailWord_3519105, baseEnd_3519105] using wordTrace_append hprefix tailTrace_3519105
  have hstable : (prefixWord ++ tailWord_3519105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519105).length < 2 ^ (prefixWord ++ tailWord_3519105).sum := by decide
  have hdescent : baseEnd_3519105 < baseStart_3519105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519172 : List Nat := [2, 3, 3, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_3519172 : Nat := 118140960795 + 3519172 * 2 ^ 59
def prefixEnd_3519172 : Nat := 4983230072969 + 3 ^ 40 * 3519172 * 2
def baseEnd_3519172 : Nat := 1807026741844410457065629

theorem tailTrace_3519172 : CollatzResearch.WordTrace tailWord_3519172 prefixEnd_3519172 1807026741844410457065629 := by
  unfold tailWord_3519172
  simp only [CollatzResearch.WordTrace]
  refine ⟨64177373803324172786263885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85569831737765563715018513 64177373803324172786263885)
  ·
    refine ⟨24066515176246564794848957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64177373803324172786263885 24066515176246564794848957)
    ·
      refine ⟨9024943191092461798068359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24066515176246564794848957 9024943191092461798068359)
      ·
        refine ⟨13537414786638692697102539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9024943191092461798068359 13537414786638692697102539)
        ·
          refine ⟨20306122179958039045653809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13537414786638692697102539 20306122179958039045653809)
          ·
            refine ⟨15229591634968529284240357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20306122179958039045653809 15229591634968529284240357)
            ·
              refine ⟨2855548431556599240795067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15229591634968529284240357 2855548431556599240795067)
              ·
                refine ⟨4283322647334898861192601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855548431556599240795067 4283322647334898861192601)
                ·
                  refine ⟨3212491985501174145894451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4283322647334898861192601 3212491985501174145894451)
                  ·
                    refine ⟨4818737978251761218841677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3212491985501174145894451 4818737978251761218841677)
                    ·
                      refine ⟨1807026741844410457065629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4818737978251761218841677 1807026741844410457065629)
                      ·
                        rfl

theorem cell23_3519172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_3519172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519172 prefixEnd_3519172 := by exact prefixLift 3519172
  have htrace : WordTrace (prefixWord ++ tailWord_3519172) baseStart_3519172 baseEnd_3519172 := by
    simpa [prefixWord, tailWord_3519172, baseEnd_3519172] using wordTrace_append hprefix tailTrace_3519172
  have hstable : (prefixWord ++ tailWord_3519172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519172).length < 2 ^ (prefixWord ++ tailWord_3519172).sum := by decide
  have hdescent : baseEnd_3519172 < baseStart_3519172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519182 : List Nat := [4, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2]
def baseStart_3519182 : Nat := 118140960795 + 3519182 * 2 ^ 59
def prefixEnd_3519182 : Nat := 4983230072969 + 3 ^ 40 * 3519182 * 2
def baseEnd_3519182 : Nat := 1807031876650955417940583

theorem tailTrace_3519182 : CollatzResearch.WordTrace tailWord_3519182 prefixEnd_3519182 1807031876650955417940583 := by
  unfold tailWord_3519182
  simp only [CollatzResearch.WordTrace]
  refine ⟨16044389042076514660048975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85570074891074744853594533 16044389042076514660048975)
  ·
    refine ⟨24066583563114771990073463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16044389042076514660048975 24066583563114771990073463)
    ·
      refine ⟨36099875344672157985110195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24066583563114771990073463 36099875344672157985110195)
      ·
        refine ⟨54149813017008236977665293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36099875344672157985110195 54149813017008236977665293)
        ·
          refine ⟨20306179881378088866624485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54149813017008236977665293 20306179881378088866624485)
          ·
            refine ⟨3807408727758391662492091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20306179881378088866624485 3807408727758391662492091)
            ·
              refine ⟨5711113091637587493738137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3807408727758391662492091 5711113091637587493738137)
              ·
                refine ⟨4283334818728190620303603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5711113091637587493738137 4283334818728190620303603)
                ·
                  refine ⟨6425002228092285930455405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4283334818728190620303603 6425002228092285930455405)
                  ·
                    refine ⟨2409375835534607223920777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6425002228092285930455405 2409375835534607223920777)
                    ·
                      refine ⟨1807031876650955417940583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409375835534607223920777 1807031876650955417940583)
                      ·
                        rfl

theorem cell23_3519182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_3519182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519182 prefixEnd_3519182 := by exact prefixLift 3519182
  have htrace : WordTrace (prefixWord ++ tailWord_3519182) baseStart_3519182 baseEnd_3519182 := by
    simpa [prefixWord, tailWord_3519182, baseEnd_3519182] using wordTrace_append hprefix tailTrace_3519182
  have hstable : (prefixWord ++ tailWord_3519182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519182).length < 2 ^ (prefixWord ++ tailWord_3519182).sum := by decide
  have hdescent : baseEnd_3519182 < baseStart_3519182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519211 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 3]
def baseStart_3519211 : Nat := 118140960795 + 3519211 * 2 ^ 59
def prefixEnd_3519211 : Nat := 4983230072969 + 3 ^ 40 * 3519211 * 2
def baseEnd_3519211 : Nat := 1807046767589935804477949

theorem tailTrace_3519211 : CollatzResearch.WordTrace tailWord_3519211 prefixEnd_3519211 1807046767589935804477949 := by
  unfold tailWord_3519211
  simp only [CollatzResearch.WordTrace]
  refine ⟨128356170053507055233197487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85570780035671370155464991 128356170053507055233197487)
  ·
    refine ⟨192534255080260582849796231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128356170053507055233197487 192534255080260582849796231)
    ·
      refine ⟨288801382620390874274694347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192534255080260582849796231 288801382620390874274694347)
      ·
        refine ⟨433202073930586311412041521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288801382620390874274694347 433202073930586311412041521)
        ·
          refine ⟨324901555447939733559031141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433202073930586311412041521 324901555447939733559031141)
          ·
            refine ⟨60919041646488700042318339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 324901555447939733559031141 60919041646488700042318339)
            ·
              refine ⟨91378562469733050063477509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60919041646488700042318339 91378562469733050063477509)
              ·
                refine ⟨17133480463074946886902033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91378562469733050063477509 17133480463074946886902033)
                ·
                  refine ⟨12850110347306210165176525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17133480463074946886902033 12850110347306210165176525)
                  ·
                    refine ⟨4818791380239828811941197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12850110347306210165176525 4818791380239828811941197)
                    ·
                      refine ⟨1807046767589935804477949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4818791380239828811941197 1807046767589935804477949)
                      ·
                        rfl

theorem cell23_3519211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 3, 3].length) (baseStart_3519211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519211 prefixEnd_3519211 := by exact prefixLift 3519211
  have htrace : WordTrace (prefixWord ++ tailWord_3519211) baseStart_3519211 baseEnd_3519211 := by
    simpa [prefixWord, tailWord_3519211, baseEnd_3519211] using wordTrace_append hprefix tailTrace_3519211
  have hstable : (prefixWord ++ tailWord_3519211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519211).length < 2 ^ (prefixWord ++ tailWord_3519211).sum := by decide
  have hdescent : baseEnd_3519211 < baseStart_3519211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519228 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 2, 3, 3]
def baseStart_3519228 : Nat := 118140960795 + 3519228 * 2 ^ 59
def prefixEnd_3519228 : Nat := 4983230072969 + 3 ^ 40 * 3519228 * 2
def baseEnd_3519228 : Nat := 1807055496761062237965371

theorem tailTrace_3519228 : CollatzResearch.WordTrace tailWord_3519228 prefixEnd_3519228 1807055496761062237965371 := by
  unfold tailWord_3519228
  simp only [CollatzResearch.WordTrace]
  refine ⟨64178395047222733568283169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85571193396296978091044225 64178395047222733568283169)
  ·
    refine ⟨48133796285417050176212377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64178395047222733568283169 48133796285417050176212377)
    ·
      refine ⟨36100347214062787632159283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48133796285417050176212377 36100347214062787632159283)
      ·
        refine ⟨54150520821094181448238925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36100347214062787632159283 54150520821094181448238925)
        ·
          refine ⟨20306445307910318043089597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54150520821094181448238925 20306445307910318043089597)
          ·
            refine ⟨7614916990466369266158599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20306445307910318043089597 7614916990466369266158599)
            ·
              refine ⟨11422375485699553899237899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7614916990466369266158599 11422375485699553899237899)
              ·
                refine ⟨17133563228549330848856849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11422375485699553899237899 17133563228549330848856849)
                ·
                  refine ⟨12850172421411998136642637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17133563228549330848856849 12850172421411998136642637)
                  ·
                    refine ⟨4818814658029499301240989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12850172421411998136642637 4818814658029499301240989)
                    ·
                      refine ⟨1807055496761062237965371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4818814658029499301240989 1807055496761062237965371)
                      ·
                        rfl

theorem cell23_3519228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_3519228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519228 prefixEnd_3519228 := by exact prefixLift 3519228
  have htrace : WordTrace (prefixWord ++ tailWord_3519228) baseStart_3519228 baseEnd_3519228 := by
    simpa [prefixWord, tailWord_3519228, baseEnd_3519228] using wordTrace_append hprefix tailTrace_3519228
  have hstable : (prefixWord ++ tailWord_3519228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519228).length < 2 ^ (prefixWord ++ tailWord_3519228).sum := by decide
  have hdescent : baseEnd_3519228 < baseStart_3519228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519251 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 4]
def baseStart_3519251 : Nat := 118140960795 + 3519251 * 2 ^ 59
def prefixEnd_3519251 : Nat := 4983230072969 + 3 ^ 40 * 3519251 * 2
def baseEnd_3519251 : Nat := 1807067306816115647977765

theorem tailTrace_3519251 : CollatzResearch.WordTrace tailWord_3519251 prefixEnd_3519251 1807067306816115647977765 := by
  unfold tailWord_3519251
  simp only [CollatzResearch.WordTrace]
  refine ⟨128357628973362142064653607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85571752648908094709769071 128357628973362142064653607)
  ·
    refine ⟨192536443460043213096980411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128357628973362142064653607 192536443460043213096980411)
    ·
      refine ⟨288804665190064819645470617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192536443460043213096980411 288804665190064819645470617)
      ·
        refine ⟨216603498892548614734102963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288804665190064819645470617 216603498892548614734102963)
        ·
          refine ⟨324905248338822922101154445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216603498892548614734102963 324905248338822922101154445)
          ·
            refine ⟨121839468127058595787932917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324905248338822922101154445 121839468127058595787932917)
            ·
              refine ⟨11422450136911743355118711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121839468127058595787932917 11422450136911743355118711)
              ·
                refine ⟨17133675205367615032678067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11422450136911743355118711 17133675205367615032678067)
                ·
                  refine ⟨25700512808051422549017101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17133675205367615032678067 25700512808051422549017101)
                  ·
                    refine ⟨9637692303019283455881413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25700512808051422549017101 9637692303019283455881413)
                    ·
                      refine ⟨1807067306816115647977765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9637692303019283455881413 1807067306816115647977765)
                      ·
                        rfl

theorem cell23_3519251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_3519251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519251 prefixEnd_3519251 := by exact prefixLift 3519251
  have htrace : WordTrace (prefixWord ++ tailWord_3519251) baseStart_3519251 baseEnd_3519251 := by
    simpa [prefixWord, tailWord_3519251, baseEnd_3519251] using wordTrace_append hprefix tailTrace_3519251
  have hstable : (prefixWord ++ tailWord_3519251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519251).length < 2 ^ (prefixWord ++ tailWord_3519251).sum := by decide
  have hdescent : baseEnd_3519251 < baseStart_3519251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519281 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 2, 1, 6]
def baseStart_3519281 : Nat := 118140960795 + 3519281 * 2 ^ 59
def prefixEnd_3519281 : Nat := 4983230072969 + 3 ^ 40 * 3519281 * 2
def baseEnd_3519281 : Nat := 1807082711235750530602627

theorem tailTrace_3519281 : CollatzResearch.WordTrace tailWord_3519281 prefixEnd_3519281 1807082711235750530602627 := by
  unfold tailWord_3519281
  simp only [CollatzResearch.WordTrace]
  refine ⟨128358723163253457188245697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85572482108835638125497131 128358723163253457188245697)
  ·
    refine ⟨96269042372440092891184273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128358723163253457188245697 96269042372440092891184273)
    ·
      refine ⟨72201781779330069668388205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96269042372440092891184273 72201781779330069668388205)
      ·
        refine ⟨27075668167248776125645577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72201781779330069668388205 27075668167248776125645577)
        ·
          refine ⟨20306751125436582094234183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27075668167248776125645577 20306751125436582094234183)
          ·
            refine ⟨30460126688154873141351275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20306751125436582094234183 30460126688154873141351275)
            ·
              refine ⟨45690190032232309712026913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30460126688154873141351275 45690190032232309712026913)
              ·
                refine ⟨34267642524174232284020185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45690190032232309712026913 34267642524174232284020185)
                ·
                  refine ⟨25700731893130674213015139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34267642524174232284020185 25700731893130674213015139)
                  ·
                    refine ⟨38551097839696011319522709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25700731893130674213015139 38551097839696011319522709)
                    ·
                      refine ⟨1807082711235750530602627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38551097839696011319522709 1807082711235750530602627)
                      ·
                        rfl

theorem cell23_3519281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_3519281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519281 prefixEnd_3519281 := by exact prefixLift 3519281
  have htrace : WordTrace (prefixWord ++ tailWord_3519281) baseStart_3519281 baseEnd_3519281 := by
    simpa [prefixWord, tailWord_3519281, baseEnd_3519281] using wordTrace_append hprefix tailTrace_3519281
  have hstable : (prefixWord ++ tailWord_3519281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519281).length < 2 ^ (prefixWord ++ tailWord_3519281).sum := by decide
  have hdescent : baseEnd_3519281 < baseStart_3519281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519285 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 2, 4, 2]
def baseStart_3519285 : Nat := 118140960795 + 3519285 * 2 ^ 59
def prefixEnd_3519285 : Nat := 4983230072969 + 3 ^ 40 * 3519285 * 2
def baseEnd_3519285 : Nat := 1807084765158368514952609

theorem tailTrace_3519285 : CollatzResearch.WordTrace tailWord_3519285 prefixEnd_3519285 1807084765158368514952609 := by
  unfold tailWord_3519285
  simp only [CollatzResearch.WordTrace]
  refine ⟨128358869055238965871391309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85572579370159310580927539 128358869055238965871391309)
  ·
    refine ⟨48134575895714612201771741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128358869055238965871391309 48134575895714612201771741)
    ·
      refine ⟨18050465960892979575664403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48134575895714612201771741 18050465960892979575664403)
      ·
        refine ⟨27075698941339469363496605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18050465960892979575664403 27075698941339469363496605)
        ·
          refine ⟨10153387103002301011311227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27075698941339469363496605 10153387103002301011311227)
          ·
            refine ⟨15230080654503451516966841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10153387103002301011311227 15230080654503451516966841)
            ·
              refine ⟨11422560490877588637725131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15230080654503451516966841 11422560490877588637725131)
              ·
                refine ⟨17133840736316382956587697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11422560490877588637725131 17133840736316382956587697)
                ·
                  refine ⟨12850380552237287217440773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17133840736316382956587697 12850380552237287217440773)
                  ·
                    refine ⟨2409446353544491353270145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12850380552237287217440773 2409446353544491353270145)
                    ·
                      refine ⟨1807084765158368514952609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409446353544491353270145 1807084765158368514952609)
                      ·
                        rfl

theorem cell23_3519285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_3519285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519285 prefixEnd_3519285 := by exact prefixLift 3519285
  have htrace : WordTrace (prefixWord ++ tailWord_3519285) baseStart_3519285 baseEnd_3519285 := by
    simpa [prefixWord, tailWord_3519285, baseEnd_3519285] using wordTrace_append hprefix tailTrace_3519285
  have hstable : (prefixWord ++ tailWord_3519285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519285).length < 2 ^ (prefixWord ++ tailWord_3519285).sum := by decide
  have hdescent : baseEnd_3519285 < baseStart_3519285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519351 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 5, 6]
def baseStart_3519351 : Nat := 118140960795 + 3519351 * 2 ^ 59
def prefixEnd_3519351 : Nat := 4983230072969 + 3 ^ 40 * 3519351 * 2
def baseEnd_3519351 : Nat := 602372884960521752242435

theorem tailTrace_3519351 : CollatzResearch.WordTrace tailWord_3519351 prefixEnd_3519351 602372884960521752242435 := by
  unfold tailWord_3519351
  simp only [CollatzResearch.WordTrace]
  refine ⟨128361276272999859143293907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85574184181999906095529271 128361276272999859143293907)
  ·
    refine ⟨192541914409499788714940861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128361276272999859143293907 192541914409499788714940861)
    ·
      refine ⟨72203217903562420768102823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192541914409499788714940861 72203217903562420768102823)
      ·
        refine ⟨108304826855343631152154235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72203217903562420768102823 108304826855343631152154235)
        ·
          refine ⟨162457240283015446728231353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108304826855343631152154235 162457240283015446728231353)
          ·
            refine ⟨121842930212261585046173515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162457240283015446728231353 121842930212261585046173515)
            ·
              refine ⟨182764395318392377569260273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121842930212261585046173515 182764395318392377569260273)
              ·
                refine ⟨137073296488794283176945205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182764395318392377569260273 137073296488794283176945205)
                ·
                  refine ⟨12850621545824464047838613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137073296488794283176945205 12850621545824464047838613)
                  ·
                    refine ⟨602372884960521752242435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12850621545824464047838613 602372884960521752242435)
                    ·
                      rfl

theorem cell23_3519351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_3519351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519351 prefixEnd_3519351 := by exact prefixLift 3519351
  have htrace : WordTrace (prefixWord ++ tailWord_3519351) baseStart_3519351 baseEnd_3519351 := by
    simpa [prefixWord, tailWord_3519351, baseEnd_3519351] using wordTrace_append hprefix tailTrace_3519351
  have hstable : (prefixWord ++ tailWord_3519351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519351).length < 2 ^ (prefixWord ++ tailWord_3519351).sum := by decide
  have hdescent : baseEnd_3519351 < baseStart_3519351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519368 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 3, 6]
def baseStart_3519368 : Nat := 118140960795 + 3519368 * 2 ^ 59
def prefixEnd_3519368 : Nat := 4983230072969 + 3 ^ 40 * 3519368 * 2
def baseEnd_3519368 : Nat := 602375794684230563404909

theorem tailTrace_3519368 : CollatzResearch.WordTrace tailWord_3519368 prefixEnd_3519368 602375794684230563404909 := by
  unfold tailWord_3519368
  simp only [CollatzResearch.WordTrace]
  refine ⟨64180948156969135523331379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85574597542625514031108505 64180948156969135523331379)
  ·
    refine ⟨96271422235453703284997069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64180948156969135523331379 96271422235453703284997069)
    ·
      refine ⟨36101783338295138731873901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96271422235453703284997069 36101783338295138731873901)
      ·
        refine ⟨13538168751860677024452713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36101783338295138731873901 13538168751860677024452713)
        ·
          refine ⟨10153626563895507768339535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13538168751860677024452713 10153626563895507768339535)
          ·
            refine ⟨15230439845843261652509303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10153626563895507768339535 15230439845843261652509303)
            ·
              refine ⟨22845659768764892478763955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15230439845843261652509303 22845659768764892478763955)
              ·
                refine ⟨34268489653147338718145933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22845659768764892478763955 34268489653147338718145933)
                ·
                  refine ⟨12850683619930252019304725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34268489653147338718145933 12850683619930252019304725)
                  ·
                    refine ⟨602375794684230563404909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12850683619930252019304725 602375794684230563404909)
                    ·
                      rfl

theorem cell23_3519368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_3519368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519368 prefixEnd_3519368 := by exact prefixLift 3519368
  have htrace : WordTrace (prefixWord ++ tailWord_3519368) baseStart_3519368 baseEnd_3519368 := by
    simpa [prefixWord, tailWord_3519368, baseEnd_3519368] using wordTrace_append hprefix tailTrace_3519368
  have hstable : (prefixWord ++ tailWord_3519368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519368).length < 2 ^ (prefixWord ++ tailWord_3519368).sum := by decide
  have hdescent : baseEnd_3519368 < baseStart_3519368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519381 : List Nat := [1, 3, 2, 1, 1, 15]
def baseStart_3519381 : Nat := 118140960795 + 3519381 * 2 ^ 59
def prefixEnd_3519381 : Nat := 4983230072969 + 3 ^ 40 * 3519381 * 2
def baseEnd_3519381 : Nat := 7436765676136626087869

theorem tailTrace_3519381 : CollatzResearch.WordTrace tailWord_3519381 prefixEnd_3519381 7436765676136626087869 := by
  unfold tailWord_3519381
  simp only [CollatzResearch.WordTrace]
  refine ⟨128362370462891174266885997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85574913641927449511257331 128362370462891174266885997)
  ·
    refine ⟨48135888923584190350082249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128362370462891174266885997 48135888923584190350082249)
    ·
      refine ⟨36101916692688142762561687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48135888923584190350082249 36101916692688142762561687)
      ·
        refine ⟨54152875039032214143842531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36101916692688142762561687 54152875039032214143842531)
        ·
          refine ⟨81229312558548321215763797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54152875039032214143842531 81229312558548321215763797)
          ·
            refine ⟨7436765676136626087869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 81229312558548321215763797 7436765676136626087869)
            ·
              rfl

theorem cell23_3519381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 15].length) (baseStart_3519381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519381 prefixEnd_3519381 := by exact prefixLift 3519381
  have htrace : WordTrace (prefixWord ++ tailWord_3519381) baseStart_3519381 baseEnd_3519381 := by
    simpa [prefixWord, tailWord_3519381, baseEnd_3519381] using wordTrace_append hprefix tailTrace_3519381
  have hstable : (prefixWord ++ tailWord_3519381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519381).length < 2 ^ (prefixWord ++ tailWord_3519381).sum := by decide
  have hdescent : baseEnd_3519381 < baseStart_3519381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519409 : List Nat := [1, 2, 2, 4, 3, 1, 1, 2, 3, 2, 2]
def baseStart_3519409 : Nat := 118140960795 + 3519409 * 2 ^ 59
def prefixEnd_3519409 : Nat := 4983230072969 + 3 ^ 40 * 3519409 * 2
def baseEnd_3519409 : Nat := 1807148436759526029802039

theorem tailTrace_3519409 : CollatzResearch.WordTrace tailWord_3519409 prefixEnd_3519409 1807148436759526029802039 := by
  unfold tailWord_3519409
  simp only [CollatzResearch.WordTrace]
  refine ⟨128363391706789735048905281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85575594471193156699270187 128363391706789735048905281)
  ·
    refine ⟨96272543780092301286678961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128363391706789735048905281 96272543780092301286678961)
    ·
      refine ⟨72204407835069225965009221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96272543780092301286678961 72204407835069225965009221)
      ·
        refine ⟨13538326469075479868439229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72204407835069225965009221 13538326469075479868439229)
        ·
          refine ⟨5076872425903304950664711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13538326469075479868439229 5076872425903304950664711)
          ·
            refine ⟨7615308638854957425997067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5076872425903304950664711 7615308638854957425997067)
            ·
              refine ⟨11422962958282436138995601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7615308638854957425997067 11422962958282436138995601)
              ·
                refine ⟨8567222218711827104246701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11422962958282436138995601 8567222218711827104246701)
                ·
                  refine ⟨3212708332016935164092513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8567222218711827104246701 3212708332016935164092513)
                  ·
                    refine ⟨2409531249012701373069385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3212708332016935164092513 2409531249012701373069385)
                    ·
                      refine ⟨1807148436759526029802039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409531249012701373069385 1807148436759526029802039)
                      ·
                        rfl

theorem cell23_3519409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_3519409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519409 prefixEnd_3519409 := by exact prefixLift 3519409
  have htrace : WordTrace (prefixWord ++ tailWord_3519409) baseStart_3519409 baseEnd_3519409 := by
    simpa [prefixWord, tailWord_3519409, baseEnd_3519409] using wordTrace_append hprefix tailTrace_3519409
  have hstable : (prefixWord ++ tailWord_3519409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519409).length < 2 ^ (prefixWord ++ tailWord_3519409).sum := by decide
  have hdescent : baseEnd_3519409 < baseStart_3519409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519459 : List Nat := [1, 1, 1, 6, 1, 1, 5, 1, 2, 1, 3]
def baseStart_3519459 : Nat := 118140960795 + 3519459 * 2 ^ 59
def prefixEnd_3519459 : Nat := 4983230072969 + 3 ^ 40 * 3519459 * 2
def baseEnd_3519459 : Nat := 1807174110792250834176809

theorem tailTrace_3519459 : CollatzResearch.WordTrace tailWord_3519459 prefixEnd_3519459 1807174110792250834176809 := by
  unfold tailWord_3519459
  simp only [CollatzResearch.WordTrace]
  refine ⟨128365215356608593588225431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85576810237739062392150287 128365215356608593588225431)
  ·
    refine ⟨192547823034912890382338147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128365215356608593588225431 192547823034912890382338147)
    ·
      refine ⟨288821734552369335573507221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192547823034912890382338147 288821734552369335573507221)
      ·
        refine ⟨13538518807142312605008151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 288821734552369335573507221 13538518807142312605008151)
        ·
          refine ⟨20307778210713468907512227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13538518807142312605008151 20307778210713468907512227)
          ·
            refine ⟨30461667316070203361268341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20307778210713468907512227 30461667316070203361268341)
            ·
              refine ⟨2855781310881581565118907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30461667316070203361268341 2855781310881581565118907)
              ·
                refine ⟨4283671966322372347678361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855781310881581565118907 4283671966322372347678361)
                ·
                  refine ⟨3212753974741779260758771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4283671966322372347678361 3212753974741779260758771)
                  ·
                    refine ⟨4819130962112668891138157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3212753974741779260758771 4819130962112668891138157)
                    ·
                      refine ⟨1807174110792250834176809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4819130962112668891138157 1807174110792250834176809)
                      ·
                        rfl

theorem cell23_3519459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_3519459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519459 prefixEnd_3519459 := by exact prefixLift 3519459
  have htrace : WordTrace (prefixWord ++ tailWord_3519459) baseStart_3519459 baseEnd_3519459 := by
    simpa [prefixWord, tailWord_3519459, baseEnd_3519459] using wordTrace_append hprefix tailTrace_3519459
  have hstable : (prefixWord ++ tailWord_3519459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519459).length < 2 ^ (prefixWord ++ tailWord_3519459).sum := by decide
  have hdescent : baseEnd_3519459 < baseStart_3519459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519477 : List Nat := [1, 3, 5, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_3519477 : Nat := 118140960795 + 3519477 * 2 ^ 59
def prefixEnd_3519477 : Nat := 4983230072969 + 3 ^ 40 * 3519477 * 2
def baseEnd_3519477 : Nat := 1807183353444031763751727

theorem tailTrace_3519477 : CollatzResearch.WordTrace tailWord_3519477 prefixEnd_3519477 1807183353444031763751727 := by
  unfold tailWord_3519477
  simp only [CollatzResearch.WordTrace]
  refine ⟨128365871870543382662380685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85577247913695588441587123 128365871870543382662380685)
  ·
    refine ⟨48137201951453768498392757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128365871870543382662380685 48137201951453768498392757)
    ·
      refine ⟨4512862682948790796724321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48137201951453768498392757 4512862682948790796724321)
      ·
        refine ⟨3384647012211593097543241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4512862682948790796724321 3384647012211593097543241)
        ·
          refine ⟨2538485259158694823157431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3384647012211593097543241 2538485259158694823157431)
          ·
            refine ⟨3807727888738042234736147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2538485259158694823157431 3807727888738042234736147)
            ·
              refine ⟨5711591833107063352104221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3807727888738042234736147 5711591833107063352104221)
              ·
                refine ⟨2141846937415148757039083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5711591833107063352104221 2141846937415148757039083)
                ·
                  refine ⟨3212770406122723135558625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2141846937415148757039083 3212770406122723135558625)
                  ·
                    refine ⟨2409577804592042351668969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3212770406122723135558625 2409577804592042351668969)
                    ·
                      refine ⟨1807183353444031763751727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409577804592042351668969 1807183353444031763751727)
                      ·
                        rfl

theorem cell23_3519477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_3519477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519477 prefixEnd_3519477 := by exact prefixLift 3519477
  have htrace : WordTrace (prefixWord ++ tailWord_3519477) baseStart_3519477 baseEnd_3519477 := by
    simpa [prefixWord, tailWord_3519477, baseEnd_3519477] using wordTrace_append hprefix tailTrace_3519477
  have hstable : (prefixWord ++ tailWord_3519477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519477).length < 2 ^ (prefixWord ++ tailWord_3519477).sum := by decide
  have hdescent : baseEnd_3519477 < baseStart_3519477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519505 : List Nat := [1, 2, 2, 1, 1, 2, 1, 8, 5]
def baseStart_3519505 : Nat := 118140960795 + 3519505 * 2 ^ 59
def prefixEnd_3519505 : Nat := 4983230072969 + 3 ^ 40 * 3519505 * 2
def baseEnd_3519505 : Nat := 200799747878039739355733

theorem tailTrace_3519505 : CollatzResearch.WordTrace tailWord_3519505 prefixEnd_3519505 200799747878039739355733 := by
  unfold tailWord_3519505
  simp only [CollatzResearch.WordTrace]
  refine ⟨128366893114441943444399969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85577928742961295629599979 128366893114441943444399969)
  ·
    refine ⟨96275169835831457583299977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128366893114441943444399969 96275169835831457583299977)
    ·
      refine ⟨72206377376873593187474983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96275169835831457583299977 72206377376873593187474983)
      ·
        refine ⟨108309566065310389781212475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72206377376873593187474983 108309566065310389781212475)
        ·
          refine ⟨162464349097965584671818713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108309566065310389781212475 162464349097965584671818713)
          ·
            refine ⟨121848261823474188503864035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162464349097965584671818713 121848261823474188503864035)
            ·
              refine ⟨182772392735211282755796053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121848261823474188503864035 182772392735211282755796053)
              ·
                refine ⟨2141863977365757219794485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 182772392735211282755796053 2141863977365757219794485)
                ·
                  refine ⟨200799747878039739355733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2141863977365757219794485 200799747878039739355733)
                  ·
                    rfl

theorem cell23_3519505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 5].length) (baseStart_3519505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519505 prefixEnd_3519505 := by exact prefixLift 3519505
  have htrace : WordTrace (prefixWord ++ tailWord_3519505) baseStart_3519505 baseEnd_3519505 := by
    simpa [prefixWord, tailWord_3519505, baseEnd_3519505] using wordTrace_append hprefix tailTrace_3519505
  have hstable : (prefixWord ++ tailWord_3519505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519505).length < 2 ^ (prefixWord ++ tailWord_3519505).sum := by decide
  have hdescent : baseEnd_3519505 < baseStart_3519505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519516 : List Nat := [2, 2, 3, 1, 4, 1, 1, 3, 2, 2, 2]
def baseStart_3519516 : Nat := 118140960795 + 3519516 * 2 ^ 59
def prefixEnd_3519516 : Nat := 4983230072969 + 3 ^ 40 * 3519516 * 2
def baseEnd_3519516 : Nat := 1807203379189557111164047

theorem tailTrace_3519516 : CollatzResearch.WordTrace tailWord_3519516 prefixEnd_3519516 1807203379189557111164047 := by
  unfold tailWord_3519516
  simp only [CollatzResearch.WordTrace]
  refine ⟨64183647158701046161525201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85578196211601394882033601 64183647158701046161525201)
  ·
    refine ⟨48137735369025784621143901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64183647158701046161525201 48137735369025784621143901)
    ·
      refine ⟨18051650763384669232928963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48137735369025784621143901 18051650763384669232928963)
      ·
        refine ⟨27077476145077003849393445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18051650763384669232928963 27077476145077003849393445)
        ·
          refine ⟨5077026777201938221761271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27077476145077003849393445 5077026777201938221761271)
          ·
            refine ⟨7615540165802907332641907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5077026777201938221761271 7615540165802907332641907)
            ·
              refine ⟨11423310248704360998962861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7615540165802907332641907 11423310248704360998962861)
              ·
                refine ⟨4283741343264135374611073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11423310248704360998962861 4283741343264135374611073)
                ·
                  refine ⟨3212806007448101530958305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4283741343264135374611073 3212806007448101530958305)
                  ·
                    refine ⟨2409604505586076148218729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3212806007448101530958305 2409604505586076148218729)
                    ·
                      refine ⟨1807203379189557111164047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409604505586076148218729 1807203379189557111164047)
                      ·
                        rfl

theorem cell23_3519516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_3519516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519516 prefixEnd_3519516 := by exact prefixLift 3519516
  have htrace : WordTrace (prefixWord ++ tailWord_3519516) baseStart_3519516 baseEnd_3519516 := by
    simpa [prefixWord, tailWord_3519516, baseEnd_3519516] using wordTrace_append hprefix tailTrace_3519516
  have hstable : (prefixWord ++ tailWord_3519516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519516).length < 2 ^ (prefixWord ++ tailWord_3519516).sum := by decide
  have hdescent : baseEnd_3519516 < baseStart_3519516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519545 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3519545 : Nat := 118140960795 + 3519545 * 2 ^ 59
def prefixEnd_3519545 : Nat := 4983230072969 + 3 ^ 40 * 3519545 * 2
def baseEnd_3519545 : Nat := 1807218270128537497701413

theorem tailTrace_3519545 : CollatzResearch.WordTrace tailWord_3519545 prefixEnd_3519545 1807218270128537497701413 := by
  unfold tailWord_3519545
  simp only [CollatzResearch.WordTrace]
  refine ⟨128368352034297030275856089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85578901356198020183904059 128368352034297030275856089)
  ·
    refine ⟨96276264025722772706892067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128368352034297030275856089 96276264025722772706892067)
    ·
      refine ⟨144414396038584159060338101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96276264025722772706892067 144414396038584159060338101)
      ·
        refine ⟨13538849628617264911906697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144414396038584159060338101 13538849628617264911906697)
        ·
          refine ⟨10154137221462948683930023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13538849628617264911906697 10154137221462948683930023)
          ·
            refine ⟨15231205832194423025895035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10154137221462948683930023 15231205832194423025895035)
            ·
              refine ⟨22846808748291634538842553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15231205832194423025895035 22846808748291634538842553)
              ·
                refine ⟨17135106561218725904131915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22846808748291634538842553 17135106561218725904131915)
                ·
                  refine ⟨25702659841828088856197873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17135106561218725904131915 25702659841828088856197873)
                  ·
                    refine ⟨19276994881371066642148405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25702659841828088856197873 19276994881371066642148405)
                    ·
                      refine ⟨1807218270128537497701413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19276994881371066642148405 1807218270128537497701413)
                      ·
                        rfl

theorem cell23_3519545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3519545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519545 prefixEnd_3519545 := by exact prefixLift 3519545
  have htrace : WordTrace (prefixWord ++ tailWord_3519545) baseStart_3519545 baseEnd_3519545 := by
    simpa [prefixWord, tailWord_3519545, baseEnd_3519545] using wordTrace_append hprefix tailTrace_3519545
  have hstable : (prefixWord ++ tailWord_3519545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519545).length < 2 ^ (prefixWord ++ tailWord_3519545).sum := by decide
  have hdescent : baseEnd_3519545 < baseStart_3519545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519555 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 4]
def baseStart_3519555 : Nat := 118140960795 + 3519555 * 2 ^ 59
def prefixEnd_3519555 : Nat := 4983230072969 + 3 ^ 40 * 3519555 * 2
def baseEnd_3519555 : Nat := 1807223404935082458576367

theorem tailTrace_3519555 : CollatzResearch.WordTrace tailWord_3519555 prefixEnd_3519555 1807223404935082458576367 := by
  unfold tailWord_3519555
  simp only [CollatzResearch.WordTrace]
  refine ⟨128368716764260801983720119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85579144509507201322480079 128368716764260801983720119)
  ·
    refine ⟨192553075146391202975580179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128368716764260801983720119 192553075146391202975580179)
    ·
      refine ⟨288829612719586804463370269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192553075146391202975580179 288829612719586804463370269)
      ·
        refine ⟨108311104769845051673763851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288829612719586804463370269 108311104769845051673763851)
        ·
          refine ⟨162466657154767577510645777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108311104769845051673763851 162466657154767577510645777)
          ·
            refine ⟨121849992866075683132984333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162466657154767577510645777 121849992866075683132984333)
            ·
              refine ⟨45693747324778381174869125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121849992866075683132984333 45693747324778381174869125)
              ·
                refine ⟨8567577623395946470287961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45693747324778381174869125 8567577623395946470287961)
                ·
                  refine ⟨6425683217546959852715971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8567577623395946470287961 6425683217546959852715971)
                  ·
                    refine ⟨9638524826320439779073957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6425683217546959852715971 9638524826320439779073957)
                    ·
                      refine ⟨1807223404935082458576367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9638524826320439779073957 1807223404935082458576367)
                      ·
                        rfl

theorem cell23_3519555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_3519555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519555 prefixEnd_3519555 := by exact prefixLift 3519555
  have htrace : WordTrace (prefixWord ++ tailWord_3519555) baseStart_3519555 baseEnd_3519555 := by
    simpa [prefixWord, tailWord_3519555, baseEnd_3519555] using wordTrace_append hprefix tailTrace_3519555
  have hstable : (prefixWord ++ tailWord_3519555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519555).length < 2 ^ (prefixWord ++ tailWord_3519555).sum := by decide
  have hdescent : baseEnd_3519555 < baseStart_3519555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519572 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 1, 6, 2]
def baseStart_3519572 : Nat := 118140960795 + 3519572 * 2 ^ 59
def prefixEnd_3519572 : Nat := 4983230072969 + 3 ^ 40 * 3519572 * 2
def baseEnd_3519572 : Nat := 1807232134106208892063789

theorem tailTrace_3519572 : CollatzResearch.WordTrace tailWord_3519572 prefixEnd_3519572 1807232134106208892063789 := by
  unfold tailWord_3519572
  simp only [CollatzResearch.WordTrace]
  refine ⟨64184668402599606943544485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85579557870132809258059313 64184668402599606943544485)
  ·
    refine ⟨12034625325487426301914591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64184668402599606943544485 12034625325487426301914591)
    ·
      refine ⟨18051937988231139452871887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12034625325487426301914591 18051937988231139452871887)
      ·
        refine ⟨27077906982346709179307831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18051937988231139452871887 27077906982346709179307831)
        ·
          refine ⟨40616860473520063768961747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27077906982346709179307831 40616860473520063768961747)
          ·
            refine ⟨60925290710280095653442621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40616860473520063768961747 60925290710280095653442621)
            ·
              refine ⟨22846984016355035870040983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60925290710280095653442621 22846984016355035870040983)
              ·
                refine ⟨34270476024532553805061475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22846984016355035870040983 34270476024532553805061475)
                ·
                  refine ⟨51405714036798830707592213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34270476024532553805061475 51405714036798830707592213)
                  ·
                    refine ⟨2409642845474945189418385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51405714036798830707592213 2409642845474945189418385)
                    ·
                      refine ⟨1807232134106208892063789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409642845474945189418385 1807232134106208892063789)
                      ·
                        rfl

theorem cell23_3519572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_3519572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519572 prefixEnd_3519572 := by exact prefixLift 3519572
  have htrace : WordTrace (prefixWord ++ tailWord_3519572) baseStart_3519572 baseEnd_3519572 := by
    simpa [prefixWord, tailWord_3519572, baseEnd_3519572] using wordTrace_append hprefix tailTrace_3519572
  have hstable : (prefixWord ++ tailWord_3519572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519572).length < 2 ^ (prefixWord ++ tailWord_3519572).sum := by decide
  have hdescent : baseEnd_3519572 < baseStart_3519572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519575 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 3]
def baseStart_3519575 : Nat := 118140960795 + 3519575 * 2 ^ 59
def prefixEnd_3519575 : Nat := 4983230072969 + 3 ^ 40 * 3519575 * 2
def baseEnd_3519575 : Nat := 1807233674548172380326275

theorem tailTrace_3519575 : CollatzResearch.WordTrace tailWord_3519575 prefixEnd_3519575 1807233674548172380326275 := by
  unfold tailWord_3519575
  simp only [CollatzResearch.WordTrace]
  refine ⟨128369446224188345399448179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85579630816125563599632119 128369446224188345399448179)
  ·
    refine ⟨192554169336282518099172269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128369446224188345399448179 192554169336282518099172269)
    ·
      refine ⟨72207813501105944287189601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192554169336282518099172269 72207813501105944287189601)
      ·
        refine ⟨54155860125829458215392201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72207813501105944287189601 54155860125829458215392201)
        ·
          refine ⟨40616895094372093661544151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54155860125829458215392201 40616895094372093661544151)
          ·
            refine ⟨60925342641558140492316227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40616895094372093661544151 60925342641558140492316227)
            ·
              refine ⟨91388013962337210738474341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60925342641558140492316227 91388013962337210738474341)
              ·
                refine ⟨17135252617938227013463939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91388013962337210738474341 17135252617938227013463939)
                ·
                  refine ⟨25702878926907340520195909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17135252617938227013463939 25702878926907340520195909)
                  ·
                    refine ⟨4819289798795126347536733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25702878926907340520195909 4819289798795126347536733)
                    ·
                      refine ⟨1807233674548172380326275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4819289798795126347536733 1807233674548172380326275)
                      ·
                        rfl

theorem cell23_3519575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_3519575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519575 prefixEnd_3519575 := by exact prefixLift 3519575
  have htrace : WordTrace (prefixWord ++ tailWord_3519575) baseStart_3519575 baseEnd_3519575 := by
    simpa [prefixWord, tailWord_3519575, baseEnd_3519575] using wordTrace_append hprefix tailTrace_3519575
  have hstable : (prefixWord ++ tailWord_3519575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519575).length < 2 ^ (prefixWord ++ tailWord_3519575).sum := by decide
  have hdescent : baseEnd_3519575 < baseStart_3519575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519599 : List Nat := [1, 1, 2, 1, 3, 3, 4, 3, 1, 4]
def baseStart_3519599 : Nat := 118140960795 + 3519599 * 2 ^ 59
def prefixEnd_3519599 : Nat := 4983230072969 + 3 ^ 40 * 3519599 * 2
def baseEnd_3519599 : Nat := 602415332694626762142055

theorem tailTrace_3519599 : CollatzResearch.WordTrace tailWord_3519599 prefixEnd_3519599 602415332694626762142055 := by
  unfold tailWord_3519599
  simp only [CollatzResearch.WordTrace]
  refine ⟨128370321576101397498321851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85580214384067598332214567 128370321576101397498321851)
  ·
    refine ⟨192555482364152096247482777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128370321576101397498321851 192555482364152096247482777)
    ·
      refine ⟨144416611773114072185612083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192555482364152096247482777 144416611773114072185612083)
      ·
        refine ⟨216624917659671108278418125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144416611773114072185612083 216624917659671108278418125)
        ·
          refine ⟨81234344122376665604406797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216624917659671108278418125 81234344122376665604406797)
          ·
            refine ⟨30462879045891249601652549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81234344122376665604406797 30462879045891249601652549)
            ·
              refine ⟨5711789821104609300309853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30462879045891249601652549 5711789821104609300309853)
              ·
                refine ⟨2141921182914228487616195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5711789821104609300309853 2141921182914228487616195)
                ·
                  refine ⟨3212881774371342731424293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2141921182914228487616195 3212881774371342731424293)
                  ·
                    refine ⟨602415332694626762142055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3212881774371342731424293 602415332694626762142055)
                    ·
                      rfl

theorem cell23_3519599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 1, 4].length) (baseStart_3519599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519599 prefixEnd_3519599 := by exact prefixLift 3519599
  have htrace : WordTrace (prefixWord ++ tailWord_3519599) baseStart_3519599 baseEnd_3519599 := by
    simpa [prefixWord, tailWord_3519599, baseEnd_3519599] using wordTrace_append hprefix tailTrace_3519599
  have hstable : (prefixWord ++ tailWord_3519599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519599).length < 2 ^ (prefixWord ++ tailWord_3519599).sum := by decide
  have hdescent : baseEnd_3519599 < baseStart_3519599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519632 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 6, 3, 2]
def baseStart_3519632 : Nat := 118140960795 + 3519632 * 2 ^ 59
def prefixEnd_3519632 : Nat := 4983230072969 + 3 ^ 40 * 3519632 * 2
def baseEnd_3519632 : Nat := 1807262942945478657313513

theorem tailTrace_3519632 : CollatzResearch.WordTrace tailWord_3519632 prefixEnd_3519632 1807262942945478657313513 := by
  unfold tailWord_3519632
  simp only [CollatzResearch.WordTrace]
  refine ⟨64185762592490922067136575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85581016789987896089515433 64185762592490922067136575)
  ·
    refine ⟨96278643888736383100704863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64185762592490922067136575 96278643888736383100704863)
    ·
      refine ⟨144417965833104574651057295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96278643888736383100704863 144417965833104574651057295)
      ·
        refine ⟨216626948749656861976585943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144417965833104574651057295 216626948749656861976585943)
        ·
          refine ⟨324940423124485292964878915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216626948749656861976585943 324940423124485292964878915)
          ·
            refine ⟨487410634686727939447318373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324940423124485292964878915 487410634686727939447318373)
            ·
              refine ⟨91389494003761488646372195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 487410634686727939447318373 91389494003761488646372195)
              ·
                refine ⟨137084241005642232969558293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91389494003761488646372195 137084241005642232969558293)
                ·
                  refine ⟨6425823797139479670448045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137084241005642232969558293 6425823797139479670448045)
                  ·
                    refine ⟨2409683923927304876418017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6425823797139479670448045 2409683923927304876418017)
                    ·
                      refine ⟨1807262942945478657313513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409683923927304876418017 1807262942945478657313513)
                      ·
                        rfl

theorem cell23_3519632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 6, 3, 2].length) (baseStart_3519632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519632 prefixEnd_3519632 := by exact prefixLift 3519632
  have htrace : WordTrace (prefixWord ++ tailWord_3519632) baseStart_3519632 baseEnd_3519632 := by
    simpa [prefixWord, tailWord_3519632, baseEnd_3519632] using wordTrace_append hprefix tailTrace_3519632
  have hstable : (prefixWord ++ tailWord_3519632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519632).length < 2 ^ (prefixWord ++ tailWord_3519632).sum := by decide
  have hdescent : baseEnd_3519632 < baseStart_3519632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519639 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 3, 1, 3]
def baseStart_3519639 : Nat := 118140960795 + 3519639 * 2 ^ 59
def prefixEnd_3519639 : Nat := 4983230072969 + 3 ^ 40 * 3519639 * 2
def baseEnd_3519639 : Nat := 1807266537310060129925981

theorem tailTrace_3519639 : CollatzResearch.WordTrace tailWord_3519639 prefixEnd_3519639 1807266537310060129925981 := by
  unfold tailWord_3519639
  simp only [CollatzResearch.WordTrace]
  refine ⟨128371780495956484329777971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85581186997304322886518647 128371780495956484329777971)
  ·
    refine ⟨192557670743934726494666957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128371780495956484329777971 192557670743934726494666957)
    ·
      refine ⟨72209126528975522435500109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192557670743934726494666957 72209126528975522435500109)
      ·
        refine ⟨27078422448365820913312541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72209126528975522435500109 27078422448365820913312541)
        ·
          refine ⟨10154408418137182842492203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27078422448365820913312541 10154408418137182842492203)
          ·
            refine ⟨15231612627205774263738305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10154408418137182842492203 15231612627205774263738305)
            ·
              refine ⟨11423709470404330697803729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15231612627205774263738305 11423709470404330697803729)
              ·
                refine ⟨8567782102803248023352797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11423709470404330697803729 8567782102803248023352797)
                ·
                  refine ⟨3212918288551218008757299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8567782102803248023352797 3212918288551218008757299)
                  ·
                    refine ⟨4819377432826827013135949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3212918288551218008757299 4819377432826827013135949)
                    ·
                      refine ⟨1807266537310060129925981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4819377432826827013135949 1807266537310060129925981)
                      ·
                        rfl

theorem cell23_3519639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_3519639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519639 prefixEnd_3519639 := by exact prefixLift 3519639
  have htrace : WordTrace (prefixWord ++ tailWord_3519639) baseStart_3519639 baseEnd_3519639 := by
    simpa [prefixWord, tailWord_3519639, baseEnd_3519639] using wordTrace_append hprefix tailTrace_3519639
  have hstable : (prefixWord ++ tailWord_3519639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519639).length < 2 ^ (prefixWord ++ tailWord_3519639).sum := by decide
  have hdescent : baseEnd_3519639 < baseStart_3519639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519649 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 2, 3, 2]
def baseStart_3519649 : Nat := 118140960795 + 3519649 * 2 ^ 59
def prefixEnd_3519649 : Nat := 4983230072969 + 3 ^ 40 * 3519649 * 2
def baseEnd_3519649 : Nat := 1807271672116605090800935

theorem tailTrace_3519649 : CollatzResearch.WordTrace tailWord_3519649 prefixEnd_3519649 1807271672116605090800935 := by
  unfold tailWord_3519649
  simp only [CollatzResearch.WordTrace]
  refine ⟨128372145225920256037642001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85581430150613504025094667 128372145225920256037642001)
  ·
    refine ⟨96279108919440192028231501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128372145225920256037642001 96279108919440192028231501)
    ·
      refine ⟨36104665844790072010586813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96279108919440192028231501 36104665844790072010586813)
      ·
        refine ⟨13539249691796277003970055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36104665844790072010586813 13539249691796277003970055)
        ·
          refine ⟨20308874537694415505955083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13539249691796277003970055 20308874537694415505955083)
          ·
            refine ⟨30463311806541623258932625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20308874537694415505955083 30463311806541623258932625)
            ·
              refine ⟨22847483854906217444199469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30463311806541623258932625 22847483854906217444199469)
              ·
                refine ⟨8567806445589831541574801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22847483854906217444199469 8567806445589831541574801)
                ·
                  refine ⟨6425854834192373656181101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8567806445589831541574801 6425854834192373656181101)
                  ·
                    refine ⟨2409695562822140121067913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6425854834192373656181101 2409695562822140121067913)
                    ·
                      refine ⟨1807271672116605090800935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409695562822140121067913 1807271672116605090800935)
                      ·
                        rfl

theorem cell23_3519649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_3519649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519649 prefixEnd_3519649 := by exact prefixLift 3519649
  have htrace : WordTrace (prefixWord ++ tailWord_3519649) baseStart_3519649 baseEnd_3519649 := by
    simpa [prefixWord, tailWord_3519649, baseEnd_3519649] using wordTrace_append hprefix tailTrace_3519649
  have hstable : (prefixWord ++ tailWord_3519649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519649).length < 2 ^ (prefixWord ++ tailWord_3519649).sum := by decide
  have hdescent : baseEnd_3519649 < baseStart_3519649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519650 : List Nat := [3, 3, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_3519650 : Nat := 118140960795 + 3519650 * 2 ^ 59
def prefixEnd_3519650 : Nat := 4983230072969 + 3 ^ 40 * 3519650 * 2
def baseEnd_3519650 : Nat := 602424061865753195629477

theorem tailTrace_3519650 : CollatzResearch.WordTrace tailWord_3519650 prefixEnd_3519650 602424061865753195629477 := by
  unfold tailWord_3519650
  simp only [CollatzResearch.WordTrace]
  refine ⟨32093045424729158302107101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85581454465944422138952269 32093045424729158302107101)
  ·
    refine ⟨12034892034273434363290163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32093045424729158302107101 12034892034273434363290163)
    ·
      refine ⟨18052338051410151544935245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12034892034273434363290163 18052338051410151544935245)
      ·
        refine ⟨6769626769278806829350717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18052338051410151544935245 6769626769278806829350717)
        ·
          refine ⟨2538610038479552561006519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6769626769278806829350717 2538610038479552561006519)
          ·
            refine ⟨3807915057719328841509779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2538610038479552561006519 3807915057719328841509779)
            ·
              refine ⟨5711872586578993262264669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3807915057719328841509779 5711872586578993262264669)
              ·
                refine ⟨2141952219967122473349251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5711872586578993262264669 2141952219967122473349251)
                ·
                  refine ⟨3212928329950683710023877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2141952219967122473349251 3212928329950683710023877)
                  ·
                    refine ⟨602424061865753195629477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3212928329950683710023877 602424061865753195629477)
                    ·
                      rfl

theorem cell23_3519650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_3519650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519650 prefixEnd_3519650 := by exact prefixLift 3519650
  have htrace : WordTrace (prefixWord ++ tailWord_3519650) baseStart_3519650 baseEnd_3519650 := by
    simpa [prefixWord, tailWord_3519650, baseEnd_3519650] using wordTrace_append hprefix tailTrace_3519650
  have hstable : (prefixWord ++ tailWord_3519650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519650).length < 2 ^ (prefixWord ++ tailWord_3519650).sum := by decide
  have hdescent : baseEnd_3519650 < baseStart_3519650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519673 : List Nat := [1, 2, 1, 4, 1, 4, 3, 2, 1, 1, 3]
def baseStart_3519673 : Nat := 118140960795 + 3519673 * 2 ^ 59
def prefixEnd_3519673 : Nat := 4983230072969 + 3 ^ 40 * 3519673 * 2
def baseEnd_3519673 : Nat := 1807283995652312996900825

theorem tailTrace_3519673 : CollatzResearch.WordTrace tailWord_3519673 prefixEnd_3519673 1807283995652312996900825 := by
  unfold tailWord_3519673
  simp only [CollatzResearch.WordTrace]
  refine ⟨128373020577833308136515673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85582013718555538757677115 128373020577833308136515673)
  ·
    refine ⟨96279765433374981102386755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128373020577833308136515673 96279765433374981102386755)
    ·
      refine ⟨144419648150062471653580133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96279765433374981102386755 144419648150062471653580133)
      ·
        refine ⟨27078684028136713435046275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144419648150062471653580133 27078684028136713435046275)
        ·
          refine ⟨40618026042205070152569413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27078684028136713435046275 40618026042205070152569413)
          ·
            refine ⟨7615879882913450653606765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40618026042205070152569413 7615879882913450653606765)
            ·
              refine ⟨2855954956092543995102537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7615879882913450653606765 2855954956092543995102537)
              ·
                refine ⟨2141966217069407996326903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2855954956092543995102537 2141966217069407996326903)
                ·
                  refine ⟨3212949325604111994490355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2141966217069407996326903 3212949325604111994490355)
                  ·
                    refine ⟨4819423988406167991735533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3212949325604111994490355 4819423988406167991735533)
                    ·
                      refine ⟨1807283995652312996900825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4819423988406167991735533 1807283995652312996900825)
                      ·
                        rfl

theorem cell23_3519673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_3519673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519673 prefixEnd_3519673 := by exact prefixLift 3519673
  have htrace : WordTrace (prefixWord ++ tailWord_3519673) baseStart_3519673 baseEnd_3519673 := by
    simpa [prefixWord, tailWord_3519673, baseEnd_3519673] using wordTrace_append hprefix tailTrace_3519673
  have hstable : (prefixWord ++ tailWord_3519673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519673).length < 2 ^ (prefixWord ++ tailWord_3519673).sum := by decide
  have hdescent : baseEnd_3519673 < baseStart_3519673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519675 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 4]
def baseStart_3519675 : Nat := 118140960795 + 3519675 * 2 ^ 59
def prefixEnd_3519675 : Nat := 4983230072969 + 3 ^ 40 * 3519675 * 2
def baseEnd_3519675 : Nat := 1807285022613621989075815

theorem tailTrace_3519675 : CollatzResearch.WordTrace tailWord_3519675 prefixEnd_3519675 1807285022613621989075815 := by
  unfold tailWord_3519675
  simp only [CollatzResearch.WordTrace]
  refine ⟨128373093523826062478088479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85582062349217374985392319 128373093523826062478088479)
  ·
    refine ⟨192559640285739093717132719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128373093523826062478088479 192559640285739093717132719)
    ·
      refine ⟨288839460428608640575699079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192559640285739093717132719 288839460428608640575699079)
      ·
        refine ⟨433259190642912960863548619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288839460428608640575699079 433259190642912960863548619)
        ·
          refine ⟨649888785964369441295322929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433259190642912960863548619 649888785964369441295322929)
          ·
            refine ⟨487416589473277080971492197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649888785964369441295322929 487416589473277080971492197)
            ·
              refine ⟨91390610526239452682154787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 487416589473277080971492197 91390610526239452682154787)
              ·
                refine ⟨137085915789359179023232181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91390610526239452682154787 137085915789359179023232181)
                ·
                  refine ⟨12851804605252423033428017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137085915789359179023232181 12851804605252423033428017)
                  ·
                    refine ⟨9638853453939317275071013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12851804605252423033428017 9638853453939317275071013)
                    ·
                      refine ⟨1807285022613621989075815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9638853453939317275071013 1807285022613621989075815)
                      ·
                        rfl

theorem cell23_3519675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 4].length) (baseStart_3519675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519675 prefixEnd_3519675 := by exact prefixLift 3519675
  have htrace : WordTrace (prefixWord ++ tailWord_3519675) baseStart_3519675 baseEnd_3519675 := by
    simpa [prefixWord, tailWord_3519675, baseEnd_3519675] using wordTrace_append hprefix tailTrace_3519675
  have hstable : (prefixWord ++ tailWord_3519675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519675).length < 2 ^ (prefixWord ++ tailWord_3519675).sum := by decide
  have hdescent : baseEnd_3519675 < baseStart_3519675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519712 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 3]
def baseStart_3519712 : Nat := 118140960795 + 3519712 * 2 ^ 59
def prefixEnd_3519712 : Nat := 4983230072969 + 3 ^ 40 * 3519712 * 2
def baseEnd_3519712 : Nat := 1807304021397838344313145

theorem tailTrace_3519712 : CollatzResearch.WordTrace tailWord_3519712 prefixEnd_3519712 1807304021397838344313145 := by
  unfold tailWord_3519712
  simp only [CollatzResearch.WordTrace]
  refine ⟨64187221512346008898592695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85582962016461345198123593 64187221512346008898592695)
  ·
    refine ⟨96280832268519013347889043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64187221512346008898592695 96280832268519013347889043)
    ·
      refine ⟨144421248402778520021833565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96280832268519013347889043 144421248402778520021833565)
      ·
        refine ⟨54157968151041945008187587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144421248402778520021833565 54157968151041945008187587)
        ·
          refine ⟨81236952226562917512281381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54157968151041945008187587 81236952226562917512281381)
          ·
            refine ⟨15231928542480547033552759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81236952226562917512281381 15231928542480547033552759)
            ·
              refine ⟨22847892813720820550329139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15231928542480547033552759 22847892813720820550329139)
              ·
                refine ⟨34271839220581230825493709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22847892813720820550329139 34271839220581230825493709)
                ·
                  refine ⟨12851939707717961559560141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34271839220581230825493709 12851939707717961559560141)
                  ·
                    refine ⟨4819477390394235584835053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12851939707717961559560141 4819477390394235584835053)
                    ·
                      refine ⟨1807304021397838344313145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4819477390394235584835053 1807304021397838344313145)
                      ·
                        rfl

theorem cell23_3519712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_3519712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519712 prefixEnd_3519712 := by exact prefixLift 3519712
  have htrace : WordTrace (prefixWord ++ tailWord_3519712) baseStart_3519712 baseEnd_3519712 := by
    simpa [prefixWord, tailWord_3519712, baseEnd_3519712] using wordTrace_append hprefix tailTrace_3519712
  have hstable : (prefixWord ++ tailWord_3519712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519712).length < 2 ^ (prefixWord ++ tailWord_3519712).sum := by decide
  have hdescent : baseEnd_3519712 < baseStart_3519712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519730 : List Nat := [3, 2, 1, 3, 3, 1, 1, 4, 1, 2, 2]
def baseStart_3519730 : Nat := 118140960795 + 3519730 * 2 ^ 59
def prefixEnd_3519730 : Nat := 4983230072969 + 3 ^ 40 * 3519730 * 2
def baseEnd_3519730 : Nat := 1807313264049619273888063

theorem tailTrace_3519730 : CollatzResearch.WordTrace tailWord_3519730 prefixEnd_3519730 1807313264049619273888063 := by
  unfold tailWord_3519730
  simp only [CollatzResearch.WordTrace]
  refine ⟨32093774884656701717835161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85583399692417871247560429 32093774884656701717835161)
  ·
    refine ⟨24070331163492526288376371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32093774884656701717835161 24070331163492526288376371)
    ·
      refine ⟨36105496745238789432564557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24070331163492526288376371 36105496745238789432564557)
      ·
        refine ⟨13539561279464546037211709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36105496745238789432564557 13539561279464546037211709)
        ·
          refine ⟨5077335479799204763954391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13539561279464546037211709 5077335479799204763954391)
          ·
            refine ⟨7616003219698807145931587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5077335479799204763954391 7616003219698807145931587)
            ·
              refine ⟨11424004829548210718897381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7616003219698807145931587 11424004829548210718897381)
              ·
                refine ⟨2142000905540289509793259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11424004829548210718897381 2142000905540289509793259)
                ·
                  refine ⟨3213001358310434264689889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142000905540289509793259 3213001358310434264689889)
                  ·
                    refine ⟨2409751018732825698517417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3213001358310434264689889 2409751018732825698517417)
                    ·
                      refine ⟨1807313264049619273888063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409751018732825698517417 1807313264049619273888063)
                      ·
                        rfl

theorem cell23_3519730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_3519730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519730 prefixEnd_3519730 := by exact prefixLift 3519730
  have htrace : WordTrace (prefixWord ++ tailWord_3519730) baseStart_3519730 baseEnd_3519730 := by
    simpa [prefixWord, tailWord_3519730, baseEnd_3519730] using wordTrace_append hprefix tailTrace_3519730
  have hstable : (prefixWord ++ tailWord_3519730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519730).length < 2 ^ (prefixWord ++ tailWord_3519730).sum := by decide
  have hdescent : baseEnd_3519730 < baseStart_3519730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519772 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_3519772 : Nat := 118140960795 + 3519772 * 2 ^ 59
def prefixEnd_3519772 : Nat := 4983230072969 + 3 ^ 40 * 3519772 * 2
def baseEnd_3519772 : Nat := 1807334830237108109562869

theorem tailTrace_3519772 : CollatzResearch.WordTrace tailWord_3519772 prefixEnd_3519772 1807334830237108109562869 := by
  unfold tailWord_3519772
  simp only [CollatzResearch.WordTrace]
  refine ⟨64188315702237324022184785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85584420936316432029579713 64188315702237324022184785)
  ·
    refine ⟨48141236776677993016638589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64188315702237324022184785 48141236776677993016638589)
    ·
      refine ⟨18052963791254247381239471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48141236776677993016638589 18052963791254247381239471)
      ·
        refine ⟨27079445686881371071859207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18052963791254247381239471 27079445686881371071859207)
        ·
          refine ⟨40619168530322056607788811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27079445686881371071859207 40619168530322056607788811)
          ·
            refine ⟨60928752795483084911683217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40619168530322056607788811 60928752795483084911683217)
            ·
              refine ⟨45696564596612313683762413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60928752795483084911683217 45696564596612313683762413)
              ·
                refine ⟨17136211723729617631410905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45696564596612313683762413 17136211723729617631410905)
                ·
                  refine ⟨12852158792797213223558179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17136211723729617631410905 12852158792797213223558179)
                  ·
                    refine ⟨19278238189195819835337269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12852158792797213223558179 19278238189195819835337269)
                    ·
                      refine ⟨1807334830237108109562869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19278238189195819835337269 1807334830237108109562869)
                      ·
                        rfl

theorem cell23_3519772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_3519772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519772 prefixEnd_3519772 := by exact prefixLift 3519772
  have htrace : WordTrace (prefixWord ++ tailWord_3519772) baseStart_3519772 baseEnd_3519772 := by
    simpa [prefixWord, tailWord_3519772, baseEnd_3519772] using wordTrace_append hprefix tailTrace_3519772
  have hstable : (prefixWord ++ tailWord_3519772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519772).length < 2 ^ (prefixWord ++ tailWord_3519772).sum := by decide
  have hdescent : baseEnd_3519772 < baseStart_3519772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519773 : List Nat := [1, 4, 2, 3, 1, 2, 1, 3, 1, 3, 2]
def baseStart_3519773 : Nat := 118140960795 + 3519773 * 2 ^ 59
def prefixEnd_3519773 : Nat := 4983230072969 + 3 ^ 40 * 3519773 * 2
def baseEnd_3519773 : Nat := 1807335343717762605650365

theorem tailTrace_3519773 : CollatzResearch.WordTrace tailWord_3519773 prefixEnd_3519773 1807335343717762605650365 := by
  unfold tailWord_3519773
  simp only [CollatzResearch.WordTrace]
  refine ⟨128376667877471025215155973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85584445251647350143437315 128376667877471025215155973)
  ·
    refine ⟨24070625227025817227841745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128376667877471025215155973 24070625227025817227841745)
    ·
      refine ⟨18052968920269362920881309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24070625227025817227841745 18052968920269362920881309)
      ·
        refine ⟨6769863345101011095330491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18052968920269362920881309 6769863345101011095330491)
        ·
          refine ⟨10154795017651516642995737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6769863345101011095330491 10154795017651516642995737)
          ·
            refine ⟨7616096263238637482246803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10154795017651516642995737 7616096263238637482246803)
            ·
              refine ⟨11424144394857956223370205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7616096263238637482246803 11424144394857956223370205)
              ·
                refine ⟨4284054148071733583763827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11424144394857956223370205 4284054148071733583763827)
                ·
                  refine ⟨6426081222107600375645741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4284054148071733583763827 6426081222107600375645741)
                  ·
                    refine ⟨2409780458290350140867153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6426081222107600375645741 2409780458290350140867153)
                    ·
                      refine ⟨1807335343717762605650365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409780458290350140867153 1807335343717762605650365)
                      ·
                        rfl

theorem cell23_3519773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_3519773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519773 prefixEnd_3519773 := by exact prefixLift 3519773
  have htrace : WordTrace (prefixWord ++ tailWord_3519773) baseStart_3519773 baseEnd_3519773 := by
    simpa [prefixWord, tailWord_3519773, baseEnd_3519773] using wordTrace_append hprefix tailTrace_3519773
  have hstable : (prefixWord ++ tailWord_3519773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519773).length < 2 ^ (prefixWord ++ tailWord_3519773).sum := by decide
  have hdescent : baseEnd_3519773 < baseStart_3519773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519792 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 7]
def baseStart_3519792 : Nat := 118140960795 + 3519792 * 2 ^ 59
def prefixEnd_3519792 : Nat := 4983230072969 + 3 ^ 40 * 3519792 * 2
def baseEnd_3519792 : Nat := 200816122205577559034753

theorem tailTrace_3519792 : CollatzResearch.WordTrace tailWord_3519792 prefixEnd_3519792 200816122205577559034753 := by
  unfold tailWord_3519792
  simp only [CollatzResearch.WordTrace]
  refine ⟨64188680432201095730048815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85584907242934794306731753 64188680432201095730048815)
  ·
    refine ⟨96283020648301643595073223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64188680432201095730048815 96283020648301643595073223)
    ·
      refine ⟨144424530972452465392609835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96283020648301643595073223 144424530972452465392609835)
      ·
        refine ⟨216636796458678698088914753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144424530972452465392609835 216636796458678698088914753)
        ·
          refine ⟨162477597344009023566686065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216636796458678698088914753 162477597344009023566686065)
          ·
            refine ⟨121858198008006767675014549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162477597344009023566686065 121858198008006767675014549)
            ·
              refine ⟨5712103031625317234766307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121858198008006767675014549 5712103031625317234766307)
              ·
                refine ⟨8568154547437975852149461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5712103031625317234766307 8568154547437975852149461)
                ·
                  refine ⟨200816122205577559034753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8568154547437975852149461 200816122205577559034753)
                  ·
                    rfl

theorem cell23_3519792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 7].length) (baseStart_3519792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519792 prefixEnd_3519792 := by exact prefixLift 3519792
  have htrace : WordTrace (prefixWord ++ tailWord_3519792) baseStart_3519792 baseEnd_3519792 := by
    simpa [prefixWord, tailWord_3519792, baseEnd_3519792] using wordTrace_append hprefix tailTrace_3519792
  have hstable : (prefixWord ++ tailWord_3519792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519792).length < 2 ^ (prefixWord ++ tailWord_3519792).sum := by decide
  have hdescent : baseEnd_3519792 < baseStart_3519792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519809 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 7]
def baseStart_3519809 : Nat := 118140960795 + 3519809 * 2 ^ 59
def prefixEnd_3519809 : Nat := 4983230072969 + 3 ^ 40 * 3519809 * 2
def baseEnd_3519809 : Nat := 200817092113480496088911

theorem tailTrace_3519809 : CollatzResearch.WordTrace tailWord_3519809 prefixEnd_3519809 200817092113480496088911 := by
  unfold tailWord_3519809
  simp only [CollatzResearch.WordTrace]
  refine ⟨128377980905340603363466481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85585320603560402242310987 128377980905340603363466481)
  ·
    refine ⟨96283485679005452522599861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128377980905340603363466481 96283485679005452522599861)
    ·
      refine ⟨9026576782406761173993737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96283485679005452522599861 9026576782406761173993737)
      ·
        refine ⟨6769932586805070880495303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9026576782406761173993737 6769932586805070880495303)
        ·
          refine ⟨10154898880207606320742955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6769932586805070880495303 10154898880207606320742955)
          ·
            refine ⟨15232348320311409481114433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10154898880207606320742955 15232348320311409481114433)
            ·
              refine ⟨11424261240233557110835825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15232348320311409481114433 11424261240233557110835825)
              ·
                refine ⟨8568195930175167833126869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11424261240233557110835825 8568195930175167833126869)
                ·
                  refine ⟨200817092113480496088911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8568195930175167833126869 200817092113480496088911)
                  ·
                    rfl

theorem cell23_3519809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 7].length) (baseStart_3519809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519809 prefixEnd_3519809 := by exact prefixLift 3519809
  have htrace : WordTrace (prefixWord ++ tailWord_3519809) baseStart_3519809 baseEnd_3519809 := by
    simpa [prefixWord, tailWord_3519809, baseEnd_3519809] using wordTrace_append hprefix tailTrace_3519809
  have hstable : (prefixWord ++ tailWord_3519809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519809).length < 2 ^ (prefixWord ++ tailWord_3519809).sum := by decide
  have hdescent : baseEnd_3519809 < baseStart_3519809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519822 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 1, 7]
def baseStart_3519822 : Nat := 118140960795 + 3519822 * 2 ^ 59
def prefixEnd_3519822 : Nat := 4983230072969 + 3 ^ 40 * 3519822 * 2
def baseEnd_3519822 : Nat := 602453501423277637979213

theorem tailTrace_3519822 : CollatzResearch.WordTrace tailWord_3519822 prefixEnd_3519822 602453501423277637979213 := by
  unfold tailWord_3519822
  simp only [CollatzResearch.WordTrace]
  refine ⟨16047306881786688322961215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85585636702862337722459813 16047306881786688322961215)
  ·
    refine ⟨24070960322680032484441823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16047306881786688322961215 24070960322680032484441823)
    ·
      refine ⟨36106440484020048726662735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24070960322680032484441823 36106440484020048726662735)
      ·
        refine ⟨54159660726030073089994103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36106440484020048726662735 54159660726030073089994103)
        ·
          refine ⟨81239491089045109634991155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54159660726030073089994103 81239491089045109634991155)
          ·
            refine ⟨121859236633567664452486733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81239491089045109634991155 121859236633567664452486733)
            ·
              refine ⟨45697213737587874169682525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121859236633567664452486733 45697213737587874169682525)
              ·
                refine ⟨17136455151595452813630947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45697213737587874169682525 17136455151595452813630947)
                ·
                  refine ⟨25704682727393179220446421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17136455151595452813630947 25704682727393179220446421)
                  ·
                    refine ⟨602453501423277637979213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25704682727393179220446421 602453501423277637979213)
                    ·
                      rfl

theorem cell23_3519822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_3519822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519822 prefixEnd_3519822 := by exact prefixLift 3519822
  have htrace : WordTrace (prefixWord ++ tailWord_3519822) baseStart_3519822 baseEnd_3519822 := by
    simpa [prefixWord, tailWord_3519822, baseEnd_3519822] using wordTrace_append hprefix tailTrace_3519822
  have hstable : (prefixWord ++ tailWord_3519822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519822).length < 2 ^ (prefixWord ++ tailWord_3519822).sum := by decide
  have hdescent : baseEnd_3519822 < baseStart_3519822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519832 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 1, 2, 5]
def baseStart_3519832 : Nat := 118140960795 + 3519832 * 2 ^ 59
def prefixEnd_3519832 : Nat := 4983230072969 + 3 ^ 40 * 3519832 * 2
def baseEnd_3519832 : Nat := 1807365639076377874812593

theorem tailTrace_3519832 : CollatzResearch.WordTrace tailWord_3519832 prefixEnd_3519832 1807365639076377874812593 := by
  unfold tailWord_3519832
  simp only [CollatzResearch.WordTrace]
  refine ⟨64189409892128639145776875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85585879856171518861035833 64189409892128639145776875)
  ·
    refine ⟨96284114838192958718665313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64189409892128639145776875 96284114838192958718665313)
    ·
      refine ⟨72213086128644719038998985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96284114838192958718665313 72213086128644719038998985)
      ·
        refine ⟨54159814596483539279249239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72213086128644719038998985 54159814596483539279249239)
        ·
          refine ⟨81239721894725308918873859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54159814596483539279249239 81239721894725308918873859)
          ·
            refine ⟨121859582842087963378310789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81239721894725308918873859 121859582842087963378310789)
            ·
              refine ⟨22848671782891493133433273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121859582842087963378310789 22848671782891493133433273)
              ·
                refine ⟨17136503837168619850074955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22848671782891493133433273 17136503837168619850074955)
                ·
                  refine ⟨25704755755752929775112433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17136503837168619850074955 25704755755752929775112433)
                  ·
                    refine ⟨19278566816814697331334325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25704755755752929775112433 19278566816814697331334325)
                    ·
                      refine ⟨1807365639076377874812593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19278566816814697331334325 1807365639076377874812593)
                      ·
                        rfl

theorem cell23_3519832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_3519832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519832 prefixEnd_3519832 := by exact prefixLift 3519832
  have htrace : WordTrace (prefixWord ++ tailWord_3519832) baseStart_3519832 baseEnd_3519832 := by
    simpa [prefixWord, tailWord_3519832, baseEnd_3519832] using wordTrace_append hprefix tailTrace_3519832
  have hstable : (prefixWord ++ tailWord_3519832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519832).length < 2 ^ (prefixWord ++ tailWord_3519832).sum := by decide
  have hdescent : baseEnd_3519832 < baseStart_3519832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519854 : List Nat := [4, 1, 2, 4, 1, 2, 2, 1, 2, 2, 2]
def baseStart_3519854 : Nat := 118140960795 + 3519854 * 2 ^ 59
def prefixEnd_3519854 : Nat := 4983230072969 + 3 ^ 40 * 3519854 * 2
def baseEnd_3519854 : Nat := 1807376935650776788737493

theorem tailTrace_3519854 : CollatzResearch.WordTrace tailWord_3519854 prefixEnd_3519854 1807376935650776788737493 := by
  unfold tailWord_3519854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16047452773772197006106827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85586414793451717365903077 16047452773772197006106827)
  ·
    refine ⟨24071179160658295509160241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16047452773772197006106827 24071179160658295509160241)
    ·
      refine ⟨18053384370493721631870181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24071179160658295509160241 18053384370493721631870181)
      ·
        refine ⟨3385009569467572805975659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18053384370493721631870181 3385009569467572805975659)
        ·
          refine ⟨5077514354201359208963489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3385009569467572805975659 5077514354201359208963489)
          ·
            refine ⟨3808135765651019406722617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5077514354201359208963489 3808135765651019406722617)
            ·
              refine ⟨2856101824238264555041963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3808135765651019406722617 2856101824238264555041963)
              ·
                refine ⟨4284152736357396832562945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2856101824238264555041963 4284152736357396832562945)
                ·
                  refine ⟨3213114552268047624422209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4284152736357396832562945 3213114552268047624422209)
                  ·
                    refine ⟨2409835914201035718316657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3213114552268047624422209 2409835914201035718316657)
                    ·
                      refine ⟨1807376935650776788737493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409835914201035718316657 1807376935650776788737493)
                      ·
                        rfl

theorem cell23_3519854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_3519854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519854 prefixEnd_3519854 := by exact prefixLift 3519854
  have htrace : WordTrace (prefixWord ++ tailWord_3519854) baseStart_3519854 baseEnd_3519854 := by
    simpa [prefixWord, tailWord_3519854, baseEnd_3519854] using wordTrace_append hprefix tailTrace_3519854
  have hstable : (prefixWord ++ tailWord_3519854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519854).length < 2 ^ (prefixWord ++ tailWord_3519854).sum := by decide
  have hdescent : baseEnd_3519854 < baseStart_3519854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519869 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 5, 4]
def baseStart_3519869 : Nat := 118140960795 + 3519869 * 2 ^ 59
def prefixEnd_3519869 : Nat := 4983230072969 + 3 ^ 40 * 3519869 * 2
def baseEnd_3519869 : Nat := 602461545953531410016641

theorem tailTrace_3519869 : CollatzResearch.WordTrace tailWord_3519869 prefixEnd_3519869 602461545953531410016641 := by
  unfold tailWord_3519869
  simp only [CollatzResearch.WordTrace]
  refine ⟨128380169285123233610650661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85586779523415489073767107 128380169285123233610650661)
  ·
    refine ⟨24071281740960606301996999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128380169285123233610650661 24071281740960606301996999)
    ·
      refine ⟨36106922611440909452995499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24071281740960606301996999 36106922611440909452995499)
      ·
        refine ⟨54160383917161364179493249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36106922611440909452995499 54160383917161364179493249)
        ·
          refine ⟨40620287937871023134619937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54160383917161364179493249 40620287937871023134619937)
          ·
            refine ⟨30465215953403267350964953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40620287937871023134619937 30465215953403267350964953)
            ·
              refine ⟨22848911965052450513223715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30465215953403267350964953 22848911965052450513223715)
              ·
                refine ⟨34273367947578675769835573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22848911965052450513223715 34273367947578675769835573)
                ·
                  refine ⟨3213128245085500853422085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34273367947578675769835573 3213128245085500853422085)
                  ·
                    refine ⟨602461545953531410016641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3213128245085500853422085 602461545953531410016641)
                    ·
                      rfl

theorem cell23_3519869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_3519869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519869 prefixEnd_3519869 := by exact prefixLift 3519869
  have htrace : WordTrace (prefixWord ++ tailWord_3519869) baseStart_3519869 baseEnd_3519869 := by
    simpa [prefixWord, tailWord_3519869, baseEnd_3519869] using wordTrace_append hprefix tailTrace_3519869
  have hstable : (prefixWord ++ tailWord_3519869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519869).length < 2 ^ (prefixWord ++ tailWord_3519869).sum := by decide
  have hdescent : baseEnd_3519869 < baseStart_3519869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519872 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 4]
def baseStart_3519872 : Nat := 118140960795 + 3519872 * 2 ^ 59
def prefixEnd_3519872 : Nat := 4983230072969 + 3 ^ 40 * 3519872 * 2
def baseEnd_3519872 : Nat := 1807386178302557718312409

theorem tailTrace_3519872 : CollatzResearch.WordTrace tailWord_3519872 prefixEnd_3519872 1807386178302557718312409 := by
  unfold tailWord_3519872
  simp only [CollatzResearch.WordTrace]
  refine ⟨64190139352056182561504935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85586852469408243415339913 64190139352056182561504935)
  ·
    refine ⟨96285209028084273842257403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64190139352056182561504935 96285209028084273842257403)
    ·
      refine ⟨144427813542126410763386105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96285209028084273842257403 144427813542126410763386105)
      ·
        refine ⟨108320860156594808072539579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144427813542126410763386105 108320860156594808072539579)
        ·
          refine ⟨162481290234892212108809369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108320860156594808072539579 162481290234892212108809369)
          ·
            refine ⟨121860967676169159081607027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162481290234892212108809369 121860967676169159081607027)
            ·
              refine ⟨182791451514253738622410541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121860967676169159081607027 182791451514253738622410541)
              ·
                refine ⟨68546794317845151983403953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182791451514253738622410541 68546794317845151983403953)
                ·
                  refine ⟨51410095738383863987552965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68546794317845151983403953 51410095738383863987552965)
                  ·
                    refine ⟨9639392950946974497666181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51410095738383863987552965 9639392950946974497666181)
                    ·
                      refine ⟨1807386178302557718312409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9639392950946974497666181 1807386178302557718312409)
                      ·
                        rfl

theorem cell23_3519872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_3519872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519872 prefixEnd_3519872 := by exact prefixLift 3519872
  have htrace : WordTrace (prefixWord ++ tailWord_3519872) baseStart_3519872 baseEnd_3519872 := by
    simpa [prefixWord, tailWord_3519872, baseEnd_3519872] using wordTrace_append hprefix tailTrace_3519872
  have hstable : (prefixWord ++ tailWord_3519872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519872).length < 2 ^ (prefixWord ++ tailWord_3519872).sum := by decide
  have hdescent : baseEnd_3519872 < baseStart_3519872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519876 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_3519876 : Nat := 118140960795 + 3519876 * 2 ^ 59
def prefixEnd_3519876 : Nat := 4983230072969 + 3 ^ 40 * 3519876 * 2
def baseEnd_3519876 : Nat := 1807388232225175702662391

theorem tailTrace_3519876 : CollatzResearch.WordTrace tailWord_3519876 prefixEnd_3519876 1807388232225175702662391 := by
  unfold tailWord_3519876
  simp only [CollatzResearch.WordTrace]
  refine ⟨64190212298048936903077741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85586949730731915870770321 64190212298048936903077741)
  ·
    refine ⟨24071329611768351338654153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64190212298048936903077741 24071329611768351338654153)
    ·
      refine ⟨18053497208826263503990615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24071329611768351338654153 18053497208826263503990615)
      ·
        refine ⟨27080245813239395255985923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18053497208826263503990615 27080245813239395255985923)
        ·
          refine ⟨40620368719859092883978885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27080245813239395255985923 40620368719859092883978885)
          ·
            refine ⟨7616319134973579915746041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40620368719859092883978885 7616319134973579915746041)
            ·
              refine ⟨5712239351230184936809531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7616319134973579915746041 5712239351230184936809531)
              ·
                refine ⟨8568359026845277405214297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5712239351230184936809531 8568359026845277405214297)
                ·
                  refine ⟨6426269270133958053910723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8568359026845277405214297 6426269270133958053910723)
                  ·
                    refine ⟨9639403905200937080866085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6426269270133958053910723 9639403905200937080866085)
                    ·
                      refine ⟨1807388232225175702662391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9639403905200937080866085 1807388232225175702662391)
                      ·
                        rfl

theorem cell23_3519876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_3519876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519876 prefixEnd_3519876 := by exact prefixLift 3519876
  have htrace : WordTrace (prefixWord ++ tailWord_3519876) baseStart_3519876 baseEnd_3519876 := by
    simpa [prefixWord, tailWord_3519876, baseEnd_3519876] using wordTrace_append hprefix tailTrace_3519876
  have hstable : (prefixWord ++ tailWord_3519876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519876).length < 2 ^ (prefixWord ++ tailWord_3519876).sum := by decide
  have hdescent : baseEnd_3519876 < baseStart_3519876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519903 : List Nat := [1, 1, 2, 5, 1, 3, 1, 4, 1, 4]
def baseStart_3519903 : Nat := 118140960795 + 3519903 * 2 ^ 59
def prefixEnd_3519903 : Nat := 4983230072969 + 3 ^ 40 * 3519903 * 2
def baseEnd_3519903 : Nat := 602467365400949032341589

theorem tailTrace_3519903 : CollatzResearch.WordTrace tailWord_3519903 prefixEnd_3519903 602467365400949032341589 := by
  unfold tailWord_3519903
  simp only [CollatzResearch.WordTrace]
  refine ⟨128381409367000057417388363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85587606244666704944925575 128381409367000057417388363)
  ·
    refine ⟨192572114050500086126082545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128381409367000057417388363 192572114050500086126082545)
    ·
      refine ⟨144429085537875064594561909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192572114050500086126082545 144429085537875064594561909)
      ·
        refine ⟨13540226769175787305740179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144429085537875064594561909 13540226769175787305740179)
        ·
          refine ⟨20310340153763680958610269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13540226769175787305740179 20310340153763680958610269)
          ·
            refine ⟨7616377557661380359478851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20310340153763680958610269 7616377557661380359478851)
            ·
              refine ⟨11424566336492070539218277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7616377557661380359478851 11424566336492070539218277)
              ·
                refine ⟨2142106188092263226103427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11424566336492070539218277 2142106188092263226103427)
                ·
                  refine ⟨3213159282138394839155141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142106188092263226103427 3213159282138394839155141)
                  ·
                    refine ⟨602467365400949032341589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3213159282138394839155141 602467365400949032341589)
                    ·
                      rfl

theorem cell23_3519903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 1, 4].length) (baseStart_3519903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519903 prefixEnd_3519903 := by exact prefixLift 3519903
  have htrace : WordTrace (prefixWord ++ tailWord_3519903) baseStart_3519903 baseEnd_3519903 := by
    simpa [prefixWord, tailWord_3519903, baseEnd_3519903] using wordTrace_append hprefix tailTrace_3519903
  have hstable : (prefixWord ++ tailWord_3519903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519903).length < 2 ^ (prefixWord ++ tailWord_3519903).sum := by decide
  have hdescent : baseEnd_3519903 < baseStart_3519903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519946 : List Nat := [3, 1, 2, 1, 2, 4, 1, 3, 1, 5]
def baseStart_3519946 : Nat := 118140960795 + 3519946 * 2 ^ 59
def prefixEnd_3519946 : Nat := 4983230072969 + 3 ^ 40 * 3519946 * 2
def baseEnd_3519946 : Nat := 602474725290330142929023

theorem tailTrace_3519946 : CollatzResearch.WordTrace tailWord_3519946 prefixEnd_3519946 602474725290330142929023 := by
  unfold tailWord_3519946
  simp only [CollatzResearch.WordTrace]
  refine ⟨32095744426461068940300923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85588651803896183840802461 32095744426461068940300923)
  ·
    refine ⟨48143616639691603410451385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32095744426461068940300923 48143616639691603410451385)
    ·
      refine ⟨36107712479768702557838539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48143616639691603410451385 36107712479768702557838539)
      ·
        refine ⟨54161568719653053836757809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36107712479768702557838539 54161568719653053836757809)
        ·
          refine ⟨40621176539739790377568357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54161568719653053836757809 40621176539739790377568357)
          ·
            refine ⟨7616470601201210695794067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40621176539739790377568357 7616470601201210695794067)
            ·
              refine ⟨11424705901801816043691101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7616470601201210695794067 11424705901801816043691101)
              ·
                refine ⟨4284264713175681016384163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11424705901801816043691101 4284264713175681016384163)
                ·
                  refine ⟨6426397069763521524576245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4284264713175681016384163 6426397069763521524576245)
                  ·
                    refine ⟨602474725290330142929023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6426397069763521524576245 602474725290330142929023)
                    ·
                      rfl

theorem cell23_3519946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_3519946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519946 prefixEnd_3519946 := by exact prefixLift 3519946
  have htrace : WordTrace (prefixWord ++ tailWord_3519946) baseStart_3519946 baseEnd_3519946 := by
    simpa [prefixWord, tailWord_3519946, baseEnd_3519946] using wordTrace_append hprefix tailTrace_3519946
  have hstable : (prefixWord ++ tailWord_3519946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519946).length < 2 ^ (prefixWord ++ tailWord_3519946).sum := by decide
  have hdescent : baseEnd_3519946 < baseStart_3519946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519969 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_3519969 : Nat := 118140960795 + 3519969 * 2 ^ 59
def prefixEnd_3519969 : Nat := 4983230072969 + 3 ^ 40 * 3519969 * 2
def baseEnd_3519969 : Nat := 1807435985926043838799463

theorem tailTrace_3519969 : CollatzResearch.WordTrace tailWord_3519969 prefixEnd_3519969 1807435985926043838799463 := by
  unfold tailWord_3519969
  simp only [CollatzResearch.WordTrace]
  refine ⟨128383816584760950689290961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85589211056507300459527307 128383816584760950689290961)
  ·
    refine ⟨96287862438570713016968221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128383816584760950689290961 96287862438570713016968221)
    ·
      refine ⟨36107948414464017381363083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96287862438570713016968221 36107948414464017381363083)
      ·
        refine ⟨54161922621696026072044625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36107948414464017381363083 54161922621696026072044625)
        ·
          refine ⟨40621441966272019554033469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54161922621696026072044625 40621441966272019554033469)
          ·
            refine ⟨15233040737352007332762551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40621441966272019554033469 15233040737352007332762551)
            ·
              refine ⟨22849561106028010999143827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15233040737352007332762551 22849561106028010999143827)
              ·
                refine ⟨34274341659042016498715741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22849561106028010999143827 34274341659042016498715741)
                ·
                  refine ⟨12852878122140756187018403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34274341659042016498715741 12852878122140756187018403)
                  ·
                    refine ⟨19279317183211134280527605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12852878122140756187018403 19279317183211134280527605)
                    ·
                      refine ⟨1807435985926043838799463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19279317183211134280527605 1807435985926043838799463)
                      ·
                        rfl

theorem cell23_3519969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_3519969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519969 prefixEnd_3519969 := by exact prefixLift 3519969
  have htrace : WordTrace (prefixWord ++ tailWord_3519969) baseStart_3519969 baseEnd_3519969 := by
    simpa [prefixWord, tailWord_3519969, baseEnd_3519969] using wordTrace_append hprefix tailTrace_3519969
  have hstable : (prefixWord ++ tailWord_3519969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519969).length < 2 ^ (prefixWord ++ tailWord_3519969).sum := by decide
  have hdescent : baseEnd_3519969 < baseStart_3519969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519979 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 4]
def baseStart_3519979 : Nat := 118140960795 + 3519979 * 2 ^ 59
def prefixEnd_3519979 : Nat := 4983230072969 + 3 ^ 40 * 3519979 * 2
def baseEnd_3519979 : Nat := 1807441120732588799674417

theorem tailTrace_3519979 : CollatzResearch.WordTrace tailWord_3519979 prefixEnd_3519979 1807441120732588799674417 := by
  unfold tailWord_3519979
  simp only [CollatzResearch.WordTrace]
  refine ⟨128384181314724722397154991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85589454209816481598103327 128384181314724722397154991)
  ·
    refine ⟨192576271972087083595732487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128384181314724722397154991 192576271972087083595732487)
    ·
      refine ⟨288864407958130625393598731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192576271972087083595732487 288864407958130625393598731)
      ·
        refine ⟨433296611937195938090398097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288864407958130625393598731 433296611937195938090398097)
        ·
          refine ⟨324972458952896953567798573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433296611937195938090398097 324972458952896953567798573)
          ·
            refine ⟨121864672107336357587924465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324972458952896953567798573 121864672107336357587924465)
            ·
              refine ⟨91398504080502268190943349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121864672107336357587924465 91398504080502268190943349)
              ·
                refine ⟨8568609757547087642900939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91398504080502268190943349 8568609757547087642900939)
                ·
                  refine ⟨12852914636320631464351409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8568609757547087642900939 12852914636320631464351409)
                  ·
                    refine ⟨9639685977240473598263557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12852914636320631464351409 9639685977240473598263557)
                    ·
                      refine ⟨1807441120732588799674417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9639685977240473598263557 1807441120732588799674417)
                      ·
                        rfl

theorem cell23_3519979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 4].length) (baseStart_3519979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519979 prefixEnd_3519979 := by exact prefixLift 3519979
  have htrace : WordTrace (prefixWord ++ tailWord_3519979) baseStart_3519979 baseEnd_3519979 := by
    simpa [prefixWord, tailWord_3519979, baseEnd_3519979] using wordTrace_append hprefix tailTrace_3519979
  have hstable : (prefixWord ++ tailWord_3519979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519979).length < 2 ^ (prefixWord ++ tailWord_3519979).sum := by decide
  have hdescent : baseEnd_3519979 < baseStart_3519979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519983 : List Nat := [1, 1, 2, 1, 4, 1, 4, 2, 3, 2, 2]
def baseStart_3519983 : Nat := 118140960795 + 3519983 * 2 ^ 59
def prefixEnd_3519983 : Nat := 4983230072969 + 3 ^ 40 * 3519983 * 2
def baseEnd_3519983 : Nat := 1807443174655206784024399

theorem tailTrace_3519983 : CollatzResearch.WordTrace tailWord_3519983 prefixEnd_3519983 1807443174655206784024399 := by
  unfold tailWord_3519983
  simp only [CollatzResearch.WordTrace]
  refine ⟨128384327206710231080300603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85589551471140154053533735 128384327206710231080300603)
  ·
    refine ⟨192576490810065346620450905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128384327206710231080300603 192576490810065346620450905)
    ·
      refine ⟨144432368107549009965338179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192576490810065346620450905 144432368107549009965338179)
      ·
        refine ⟨216648552161323514948007269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144432368107549009965338179 216648552161323514948007269)
        ·
          refine ⟨40621603530248159052751363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216648552161323514948007269 40621603530248159052751363)
          ·
            refine ⟨60932405295372238579127045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40621603530248159052751363 60932405295372238579127045)
            ·
              refine ⟨11424825992882294733586321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60932405295372238579127045 11424825992882294733586321)
              ·
                refine ⟨8568619494661721050189741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11424825992882294733586321 8568619494661721050189741)
                ·
                  refine ⟨3213232310498145393821153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8568619494661721050189741 3213232310498145393821153)
                  ·
                    refine ⟨2409924232873609045365865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3213232310498145393821153 2409924232873609045365865)
                    ·
                      refine ⟨1807443174655206784024399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409924232873609045365865 1807443174655206784024399)
                      ·
                        rfl

theorem cell23_3519983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 2, 2].length) (baseStart_3519983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3519983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3519983 prefixEnd_3519983 := by exact prefixLift 3519983
  have htrace : WordTrace (prefixWord ++ tailWord_3519983) baseStart_3519983 baseEnd_3519983 := by
    simpa [prefixWord, tailWord_3519983, baseEnd_3519983] using wordTrace_append hprefix tailTrace_3519983
  have hstable : (prefixWord ++ tailWord_3519983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519983).length < 2 ^ (prefixWord ++ tailWord_3519983).sum := by decide
  have hdescent : baseEnd_3519983 < baseStart_3519983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520017 : List Nat := [1, 2, 2, 1, 1, 2, 7, 2, 1, 2, 2]
def baseStart_3520017 : Nat := 118140960795 + 3520017 * 2 ^ 59
def prefixEnd_3520017 : Nat := 4983230072969 + 3 ^ 40 * 3520017 * 2
def baseEnd_3520017 : Nat := 1807460632997459650999243

theorem tailTrace_3520017 : CollatzResearch.WordTrace tailWord_3520017 prefixEnd_3520017 1807460632997459650999243 := by
  unfold tailWord_3520017
  simp only [CollatzResearch.WordTrace]
  refine ⟨128385567288587054887038305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85590378192391369924692203 128385567288587054887038305)
  ·
    refine ⟨96289175466440291165278729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128385567288587054887038305 96289175466440291165278729)
    ·
      refine ⟨72216881599830218373959047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96289175466440291165278729 72216881599830218373959047)
      ·
        refine ⟨108325322399745327560938571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72216881599830218373959047 108325322399745327560938571)
        ·
          refine ⟨162487983599617991341407857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108325322399745327560938571 162487983599617991341407857)
          ·
            refine ⟨121865987699713493506055893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162487983599617991341407857 121865987699713493506055893)
            ·
              refine ⟨2856234086712035004048185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 121865987699713493506055893 2856234086712035004048185)
              ·
                refine ⟨2142175565034026253036139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2856234086712035004048185 2142175565034026253036139)
                ·
                  refine ⟨3213263347551039379554209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142175565034026253036139 3213263347551039379554209)
                  ·
                    refine ⟨2409947510663279534665657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3213263347551039379554209 2409947510663279534665657)
                    ·
                      refine ⟨1807460632997459650999243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409947510663279534665657 1807460632997459650999243)
                      ·
                        rfl

theorem cell23_3520017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 1, 2, 2].length) (baseStart_3520017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520017 prefixEnd_3520017 := by exact prefixLift 3520017
  have htrace : WordTrace (prefixWord ++ tailWord_3520017) baseStart_3520017 baseEnd_3520017 := by
    simpa [prefixWord, tailWord_3520017, baseEnd_3520017] using wordTrace_append hprefix tailTrace_3520017
  have hstable : (prefixWord ++ tailWord_3520017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520017).length < 2 ^ (prefixWord ++ tailWord_3520017).sum := by decide
  have hdescent : baseEnd_3520017 < baseStart_3520017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520026 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2]
def baseStart_3520026 : Nat := 118140960795 + 3520026 * 2 ^ 59
def prefixEnd_3520026 : Nat := 4983230072969 + 3 ^ 40 * 3520026 * 2
def baseEnd_3520026 : Nat := 1807465254323350115786701

theorem tailTrace_3520026 : CollatzResearch.WordTrace tailWord_3520026 prefixEnd_3520026 1807465254323350115786701 := by
  unfold tailWord_3520026
  simp only [CollatzResearch.WordTrace]
  refine ⟨32096473886388612356028983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85590597030369632949410621 32096473886388612356028983)
  ·
    refine ⟨48144710829582918534043475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32096473886388612356028983 48144710829582918534043475)
    ·
      refine ⟨72217066244374377801065213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48144710829582918534043475 72217066244374377801065213)
      ·
        refine ⟨27081399841640391675399455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72217066244374377801065213 27081399841640391675399455)
        ·
          refine ⟨40622099762460587513099183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27081399841640391675399455 40622099762460587513099183)
          ·
            refine ⟨60933149643690881269648775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40622099762460587513099183 60933149643690881269648775)
            ·
              refine ⟨91399724465536321904473163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60933149643690881269648775 91399724465536321904473163)
              ·
                refine ⟨137099586698304482856709745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91399724465536321904473163 137099586698304482856709745)
                ·
                  refine ⟨102824690023728362142532309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137099586698304482856709745 102824690023728362142532309)
                  ·
                    refine ⟨2409953672431133487715601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 102824690023728362142532309 2409953672431133487715601)
                    ·
                      refine ⟨1807465254323350115786701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409953672431133487715601 1807465254323350115786701)
                      ·
                        rfl

theorem cell23_3520026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_3520026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520026 prefixEnd_3520026 := by exact prefixLift 3520026
  have htrace : WordTrace (prefixWord ++ tailWord_3520026) baseStart_3520026 baseEnd_3520026 := by
    simpa [prefixWord, tailWord_3520026, baseEnd_3520026] using wordTrace_append hprefix tailTrace_3520026
  have hstable : (prefixWord ++ tailWord_3520026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520026).length < 2 ^ (prefixWord ++ tailWord_3520026).sum := by decide
  have hdescent : baseEnd_3520026 < baseStart_3520026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520049 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 4, 6]
def baseStart_3520049 : Nat := 118140960795 + 3520049 * 2 ^ 59
def prefixEnd_3520049 : Nat := 4983230072969 + 3 ^ 40 * 3520049 * 2
def baseEnd_3520049 : Nat := 602492354792801175266365

theorem tailTrace_3520049 : CollatzResearch.WordTrace tailWord_3520049 prefixEnd_3520049 602492354792801175266365 := by
  unfold tailWord_3520049
  simp only [CollatzResearch.WordTrace]
  refine ⟨128386734424471124352203201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85591156282980749568135467 128386734424471124352203201)
  ·
    refine ⟨96290050818353343264152401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128386734424471124352203201 96290050818353343264152401)
    ·
      refine ⟨72217538113765007448114301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96290050818353343264152401 72217538113765007448114301)
      ·
        refine ⟨27081576792661877793042863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72217538113765007448114301 27081576792661877793042863)
        ·
          refine ⟨40622365188992816689564295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27081576792661877793042863 40622365188992816689564295)
          ·
            refine ⟨60933547783489225034346443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40622365188992816689564295 60933547783489225034346443)
            ·
              refine ⟨91400321675233837551519665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60933547783489225034346443 91400321675233837551519665)
              ·
                refine ⟨68550241256425378163639749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91400321675233837551519665 68550241256425378163639749)
                ·
                  refine ⟨12853170235579758405682453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68550241256425378163639749 12853170235579758405682453)
                  ·
                    refine ⟨602492354792801175266365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12853170235579758405682453 602492354792801175266365)
                    ·
                      rfl

theorem cell23_3520049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_3520049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520049 prefixEnd_3520049 := by exact prefixLift 3520049
  have htrace : WordTrace (prefixWord ++ tailWord_3520049) baseStart_3520049 baseEnd_3520049 := by
    simpa [prefixWord, tailWord_3520049, baseEnd_3520049] using wordTrace_append hprefix tailTrace_3520049
  have hstable : (prefixWord ++ tailWord_3520049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520049).length < 2 ^ (prefixWord ++ tailWord_3520049).sum := by decide
  have hdescent : baseEnd_3520049 < baseStart_3520049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520073 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 4, 2, 2]
def baseStart_3520073 : Nat := 118140960795 + 3520073 * 2 ^ 59
def prefixEnd_3520073 : Nat := 4983230072969 + 3 ^ 40 * 3520073 * 2
def baseEnd_3520073 : Nat := 1807489387914111431898985

theorem tailTrace_3520073 : CollatzResearch.WordTrace tailWord_3520073 prefixEnd_3520073 1807489387914111431898985 := by
  unfold tailWord_3520073
  simp only [CollatzResearch.WordTrace]
  refine ⟨128387609776384176451076873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85591739850922784300717915 128387609776384176451076873)
  ·
    refine ⟨96290707332288132338307655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128387609776384176451076873 96290707332288132338307655)
    ·
      refine ⟨144436060998432198507461483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96290707332288132338307655 144436060998432198507461483)
      ·
        refine ⟨216654091497648297761192225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144436060998432198507461483 216654091497648297761192225)
        ·
          refine ⟨162490568623236223320894169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216654091497648297761192225 162490568623236223320894169)
          ·
            refine ⟨121867926467427167490670627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162490568623236223320894169 121867926467427167490670627)
            ·
              refine ⟨182801889701140751236005941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121867926467427167490670627 182801889701140751236005941)
              ·
                refine ⟨17137677159481945428375557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182801889701140751236005941 17137677159481945428375557)
                ·
                  refine ⟨3213314467402864767820417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17137677159481945428375557 3213314467402864767820417)
                  ·
                    refine ⟨2409985850552148575865313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3213314467402864767820417 2409985850552148575865313)
                    ·
                      refine ⟨1807489387914111431898985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2409985850552148575865313 1807489387914111431898985)
                      ·
                        rfl

theorem cell23_3520073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 2, 2].length) (baseStart_3520073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520073 prefixEnd_3520073 := by exact prefixLift 3520073
  have htrace : WordTrace (prefixWord ++ tailWord_3520073) baseStart_3520073 baseEnd_3520073 := by
    simpa [prefixWord, tailWord_3520073, baseEnd_3520073] using wordTrace_append hprefix tailTrace_3520073
  have hstable : (prefixWord ++ tailWord_3520073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520073).length < 2 ^ (prefixWord ++ tailWord_3520073).sum := by decide
  have hdescent : baseEnd_3520073 < baseStart_3520073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520076 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 2, 4, 3]
def baseStart_3520076 : Nat := 118140960795 + 3520076 * 2 ^ 59
def prefixEnd_3520076 : Nat := 4983230072969 + 3 ^ 40 * 3520076 * 2
def baseEnd_3520076 : Nat := 1807490928356074920161471

theorem tailTrace_3520076 : CollatzResearch.WordTrace tailWord_3520076 prefixEnd_3520076 1807490928356074920161471 := by
  unfold tailWord_3520076
  simp only [CollatzResearch.WordTrace]
  refine ⟨64193859597686653981718041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85591812796915538642290721 64193859597686653981718041)
  ·
    refine ⟨48145394698264990486288531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64193859597686653981718041 48145394698264990486288531)
    ·
      refine ⟨72218092047397485729432797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48145394698264990486288531 72218092047397485729432797)
      ·
        refine ⟨27081784517774057148537299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72218092047397485729432797 27081784517774057148537299)
        ·
          refine ⟨40622676776661085722805949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27081784517774057148537299 40622676776661085722805949)
          ·
            refine ⟨15233503791247907146052231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40622676776661085722805949 15233503791247907146052231)
            ·
              refine ⟨22850255686871860719078347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15233503791247907146052231 22850255686871860719078347)
              ·
                refine ⟨34275383530307791078617521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22850255686871860719078347 34275383530307791078617521)
                ·
                  refine ⟨25706537647730843308963141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34275383530307791078617521 25706537647730843308963141)
                  ·
                    refine ⟨4819975808949533120430589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25706537647730843308963141 4819975808949533120430589)
                    ·
                      refine ⟨1807490928356074920161471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4819975808949533120430589 1807490928356074920161471)
                      ·
                        rfl

theorem cell23_3520076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_3520076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520076 prefixEnd_3520076 := by exact prefixLift 3520076
  have htrace : WordTrace (prefixWord ++ tailWord_3520076) baseStart_3520076 baseEnd_3520076 := by
    simpa [prefixWord, tailWord_3520076, baseEnd_3520076] using wordTrace_append hprefix tailTrace_3520076
  have hstable : (prefixWord ++ tailWord_3520076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520076).length < 2 ^ (prefixWord ++ tailWord_3520076).sum := by decide
  have hdescent : baseEnd_3520076 < baseStart_3520076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520079 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 7]
def baseStart_3520079 : Nat := 118140960795 + 3520079 * 2 ^ 59
def prefixEnd_3520079 : Nat := 4983230072969 + 3 ^ 40 * 3520079 * 2
def baseEnd_3520079 : Nat := 200832496533115378713773

theorem tailTrace_3520079 : CollatzResearch.WordTrace tailWord_3520079 prefixEnd_3520079 200832496533115378713773 := by
  unfold tailWord_3520079
  simp only [CollatzResearch.WordTrace]
  refine ⟨128387828614362439475795291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85591885742908292983863527 128387828614362439475795291)
  ·
    refine ⟨192581742921543659213692937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128387828614362439475795291 192581742921543659213692937)
    ·
      refine ⟨144436307191157744410269703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192581742921543659213692937 144436307191157744410269703)
      ·
        refine ⟨216654460786736616615404555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144436307191157744410269703 216654460786736616615404555)
        ·
          refine ⟨324981691180104924923106833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216654460786736616615404555 324981691180104924923106833)
          ·
            refine ⟨243736268385078693692330125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324981691180104924923106833 243736268385078693692330125)
            ·
              refine ⟨91401100644404510134623797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243736268385078693692330125 91401100644404510134623797)
              ·
                refine ⟨8568853185412922825120981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91401100644404510134623797 8568853185412922825120981)
                ·
                  refine ⟨200832496533115378713773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8568853185412922825120981 200832496533115378713773)
                  ·
                    rfl

theorem cell23_3520079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 7].length) (baseStart_3520079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520079 prefixEnd_3520079 := by exact prefixLift 3520079
  have htrace : WordTrace (prefixWord ++ tailWord_3520079) baseStart_3520079 baseEnd_3520079 := by
    simpa [prefixWord, tailWord_3520079, baseEnd_3520079] using wordTrace_append hprefix tailTrace_3520079
  have hstable : (prefixWord ++ tailWord_3520079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520079).length < 2 ^ (prefixWord ++ tailWord_3520079).sum := by decide
  have hdescent : baseEnd_3520079 < baseStart_3520079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520183 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 3]
def baseStart_3520183 : Nat := 118140960795 + 3520183 * 2 ^ 59
def prefixEnd_3520183 : Nat := 4983230072969 + 3 ^ 40 * 3520183 * 2
def baseEnd_3520183 : Nat := 1807545870786106001523479

theorem tailTrace_3520183 : CollatzResearch.WordTrace tailWord_3520183 prefixEnd_3520183 1807545870786106001523479 := by
  unfold tailWord_3520183
  simp only [CollatzResearch.WordTrace]
  refine ⟨128391621805985665237581203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85594414537323776825054135 128391621805985665237581203)
  ·
    refine ⟨192587432708978497856371805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128391621805985665237581203 192587432708978497856371805)
    ·
      refine ⟨72220287265866936696139427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192587432708978497856371805 72220287265866936696139427)
      ·
        refine ⟨108330430898800405044209141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72220287265866936696139427 108330430898800405044209141)
        ·
          refine ⟨10155977896762537972894607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108330430898800405044209141 10155977896762537972894607)
          ·
            refine ⟨15233966845143806959341911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10155977896762537972894607 15233966845143806959341911)
            ·
              refine ⟨22850950267715710439012867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15233966845143806959341911 22850950267715710439012867)
              ·
                refine ⟨34276425401573565658519301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22850950267715710439012867 34276425401573565658519301)
                ·
                  refine ⟨6426829762795043560972369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34276425401573565658519301 6426829762795043560972369)
                  ·
                    refine ⟨4820122322096282670729277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6426829762795043560972369 4820122322096282670729277)
                    ·
                      refine ⟨1807545870786106001523479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4820122322096282670729277 1807545870786106001523479)
                      ·
                        rfl

theorem cell23_3520183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_3520183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520183 prefixEnd_3520183 := by exact prefixLift 3520183
  have htrace : WordTrace (prefixWord ++ tailWord_3520183) baseStart_3520183 baseEnd_3520183 := by
    simpa [prefixWord, tailWord_3520183, baseEnd_3520183] using wordTrace_append hprefix tailTrace_3520183
  have hstable : (prefixWord ++ tailWord_3520183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520183).length < 2 ^ (prefixWord ++ tailWord_3520183).sum := by decide
  have hdescent : baseEnd_3520183 < baseStart_3520183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520186 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 8]
def baseStart_3520186 : Nat := 118140960795 + 3520186 * 2 ^ 59
def prefixEnd_3520186 : Nat := 4983230072969 + 3 ^ 40 * 3520186 * 2
def baseEnd_3520186 : Nat := 200838601247563276642885

theorem tailTrace_3520186 : CollatzResearch.WordTrace tailWord_3520186 prefixEnd_3520186 200838601247563276642885 := by
  unfold tailWord_3520186
  simp only [CollatzResearch.WordTrace]
  refine ⟨32097932806243699187485103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85594487483316531166626941 32097932806243699187485103)
  ·
    refine ⟨48146899209365548781227655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32097932806243699187485103 48146899209365548781227655)
    ·
      refine ⟨72220348814048323171841483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48146899209365548781227655 72220348814048323171841483)
      ·
        refine ⟨108330523221072484757762225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72220348814048323171841483 108330523221072484757762225)
        ·
          refine ⟨81247892415804363568321669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108330523221072484757762225 81247892415804363568321669)
          ·
            refine ⟨15233979827963318169060313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81247892415804363568321669 15233979827963318169060313)
            ·
              refine ⟨11425484870972488626795235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15233979827963318169060313 11425484870972488626795235)
              ·
                refine ⟨17138227306458732940192853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11425484870972488626795235 17138227306458732940192853)
                ·
                  refine ⟨200838601247563276642885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17138227306458732940192853 200838601247563276642885)
                  ·
                    rfl

theorem cell23_3520186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 8].length) (baseStart_3520186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520186 prefixEnd_3520186 := by exact prefixLift 3520186
  have htrace : WordTrace (prefixWord ++ tailWord_3520186) baseStart_3520186 baseEnd_3520186 := by
    simpa [prefixWord, tailWord_3520186, baseEnd_3520186] using wordTrace_append hprefix tailTrace_3520186
  have hstable : (prefixWord ++ tailWord_3520186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520186).length < 2 ^ (prefixWord ++ tailWord_3520186).sum := by decide
  have hdescent : baseEnd_3520186 < baseStart_3520186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520190 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_3520190 : Nat := 118140960795 + 3520190 * 2 ^ 59
def prefixEnd_3520190 : Nat := 4983230072969 + 3 ^ 40 * 3520190 * 2
def baseEnd_3520190 : Nat := 602516488383562491378649

theorem tailTrace_3520190 : CollatzResearch.WordTrace tailWord_3520190 prefixEnd_3520190 602516488383562491378649 := by
  unfold tailWord_3520190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16048984639620038179135753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85594584744640203622057349 16048984639620038179135753)
  ·
    refine ⟨12036738479715028634351815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16048984639620038179135753 12036738479715028634351815)
    ·
      refine ⟨18055107719572542951527723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12036738479715028634351815 18055107719572542951527723)
      ·
        refine ⟨27082661579358814427291585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18055107719572542951527723 27082661579358814427291585)
        ·
          refine ⟨20311996184519110820468689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27082661579358814427291585 20311996184519110820468689)
          ·
            refine ⟨15233997138389333115351517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20311996184519110820468689 15233997138389333115351517)
            ·
              refine ⟨5712748926895999918256819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15233997138389333115351517 5712748926895999918256819)
              ·
                refine ⟨8569123390343999877385229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5712748926895999918256819 8569123390343999877385229)
                ·
                  refine ⟨3213421271378999954019461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8569123390343999877385229 3213421271378999954019461)
                  ·
                    refine ⟨602516488383562491378649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3213421271378999954019461 602516488383562491378649)
                    ·
                      rfl

theorem cell23_3520190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_3520190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520190 prefixEnd_3520190 := by exact prefixLift 3520190
  have htrace : WordTrace (prefixWord ++ tailWord_3520190) baseStart_3520190 baseEnd_3520190 := by
    simpa [prefixWord, tailWord_3520190, baseEnd_3520190] using wordTrace_append hprefix tailTrace_3520190
  have hstable : (prefixWord ++ tailWord_3520190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520190).length < 2 ^ (prefixWord ++ tailWord_3520190).sum := by decide
  have hdescent : baseEnd_3520190 < baseStart_3520190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520214 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3520214 : Nat := 118140960795 + 3520214 * 2 ^ 59
def prefixEnd_3520214 : Nat := 4983230072969 + 3 ^ 40 * 3520214 * 2
def baseEnd_3520214 : Nat := 1807561788686395380235837

theorem tailTrace_3520214 : CollatzResearch.WordTrace tailWord_3520214 prefixEnd_3520214 1807561788686395380235837 := by
  unfold tailWord_3520214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8024547029304584845747481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85595168312582238354639797 8024547029304584845747481)
  ·
    refine ⟨6018410271978438634310611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8024547029304584845747481 6018410271978438634310611)
    ·
      refine ⟨9027615407967657951465917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6018410271978438634310611 9027615407967657951465917)
      ·
        refine ⟨3385355777987871731799719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9027615407967657951465917 3385355777987871731799719)
        ·
          refine ⟨5078033666981807597699579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3385355777987871731799719 5078033666981807597699579)
          ·
            refine ⟨7617050500472711396549369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5078033666981807597699579 7617050500472711396549369)
            ·
              refine ⟨5712787875354533547412027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7617050500472711396549369 5712787875354533547412027)
              ·
                refine ⟨8569181813031800321118041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5712787875354533547412027 8569181813031800321118041)
                ·
                  refine ⟨6426886359773850240838531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8569181813031800321118041 6426886359773850240838531)
                  ·
                    refine ⟨9640329539660775361257797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6426886359773850240838531 9640329539660775361257797)
                    ·
                      refine ⟨1807561788686395380235837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9640329539660775361257797 1807561788686395380235837)
                      ·
                        rfl

theorem cell23_3520214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3520214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520214 prefixEnd_3520214 := by exact prefixLift 3520214
  have htrace : WordTrace (prefixWord ++ tailWord_3520214) baseStart_3520214 baseEnd_3520214 := by
    simpa [prefixWord, tailWord_3520214, baseEnd_3520214] using wordTrace_append hprefix tailTrace_3520214
  have hstable : (prefixWord ++ tailWord_3520214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520214).length < 2 ^ (prefixWord ++ tailWord_3520214).sum := by decide
  have hdescent : baseEnd_3520214 < baseStart_3520214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520274 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_3520274 : Nat := 118140960795 + 3520274 * 2 ^ 59
def prefixEnd_3520274 : Nat := 4983230072969 + 3 ^ 40 * 3520274 * 2
def baseEnd_3520274 : Nat := 1807592597525665145485561

theorem tailTrace_3520274 : CollatzResearch.WordTrace tailWord_3520274 prefixEnd_3520274 1807592597525665145485561 := by
  unfold tailWord_3520274
  simp only [CollatzResearch.WordTrace]
  refine ⟨32098735212163996944785969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85596627232437325186095917 32098735212163996944785969)
  ·
    refine ⟨24074051409122997708589477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32098735212163996944785969 24074051409122997708589477)
    ·
      refine ⟨4513884639210562070360527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24074051409122997708589477 4513884639210562070360527)
      ·
        refine ⟨6770826958815843105540791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4513884639210562070360527 6770826958815843105540791)
        ·
          refine ⟨10156240438223764658311187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6770826958815843105540791 10156240438223764658311187)
          ·
            refine ⟨15234360657335646987466781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10156240438223764658311187 15234360657335646987466781)
            ·
              refine ⟨5712885246500867620300043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15234360657335646987466781 5712885246500867620300043)
              ·
                refine ⟨8569327869751301430450065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5712885246500867620300043 8569327869751301430450065)
                ·
                  refine ⟨6426995902313476072837549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8569327869751301430450065 6426995902313476072837549)
                  ·
                    refine ⟨2410123463367553527314081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6426995902313476072837549 2410123463367553527314081)
                    ·
                      refine ⟨1807592597525665145485561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2410123463367553527314081 1807592597525665145485561)
                      ·
                        rfl

theorem cell23_3520274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_3520274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520274 prefixEnd_3520274 := by exact prefixLift 3520274
  have htrace : WordTrace (prefixWord ++ tailWord_3520274) baseStart_3520274 baseEnd_3520274 := by
    simpa [prefixWord, tailWord_3520274, baseEnd_3520274] using wordTrace_append hprefix tailTrace_3520274
  have hstable : (prefixWord ++ tailWord_3520274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520274).length < 2 ^ (prefixWord ++ tailWord_3520274).sum := by decide
  have hdescent : baseEnd_3520274 < baseStart_3520274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520317 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 1, 2, 4]
def baseStart_3520317 : Nat := 118140960795 + 3520317 * 2 ^ 59
def prefixEnd_3520317 : Nat := 4983230072969 + 3 ^ 40 * 3520317 * 2
def baseEnd_3520317 : Nat := 1807614677193808477247863

theorem tailTrace_3520317 : CollatzResearch.WordTrace tailWord_3520317 prefixEnd_3520317 1807614677193808477247863 := by
  unfold tailWord_3520317
  simp only [CollatzResearch.WordTrace]
  refine ⟨128396509187500206122959205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85597672791666804081972803 128396509187500206122959205)
  ·
    refine ⟨24074345472656288648054851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128396509187500206122959205 24074345472656288648054851)
    ·
      refine ⟨36111518208984432972082277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24074345472656288648054851 36111518208984432972082277)
      ·
        refine ⟨6770909664184581182265427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36111518208984432972082277 6770909664184581182265427)
        ·
          refine ⟨10156364496276871773398141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6770909664184581182265427 10156364496276871773398141)
          ·
            refine ⟨3808636686103826915024303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10156364496276871773398141 3808636686103826915024303)
            ·
              refine ⟨5712955029155740372536455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3808636686103826915024303 5712955029155740372536455)
              ·
                refine ⟨8569432543733610558804683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5712955029155740372536455 8569432543733610558804683)
                ·
                  refine ⟨12854148815600415838207025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8569432543733610558804683 12854148815600415838207025)
                  ·
                    refine ⟨9640611611700311878655269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12854148815600415838207025 9640611611700311878655269)
                    ·
                      refine ⟨1807614677193808477247863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9640611611700311878655269 1807614677193808477247863)
                      ·
                        rfl

theorem cell23_3520317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_3520317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520317 prefixEnd_3520317 := by exact prefixLift 3520317
  have htrace : WordTrace (prefixWord ++ tailWord_3520317) baseStart_3520317 baseEnd_3520317 := by
    simpa [prefixWord, tailWord_3520317, baseEnd_3520317] using wordTrace_append hprefix tailTrace_3520317
  have hstable : (prefixWord ++ tailWord_3520317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520317).length < 2 ^ (prefixWord ++ tailWord_3520317).sum := by decide
  have hdescent : baseEnd_3520317 < baseStart_3520317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520363 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 3]
def baseStart_3520363 : Nat := 118140960795 + 3520363 * 2 ^ 59
def prefixEnd_3520363 : Nat := 4983230072969 + 3 ^ 40 * 3520363 * 2
def baseEnd_3520363 : Nat := 1807638297303915297272651

theorem tailTrace_3520363 : CollatzResearch.WordTrace tailWord_3520363 prefixEnd_3520363 1807638297303915297272651 := by
  unfold tailWord_3520363
  simp only [CollatzResearch.WordTrace]
  refine ⟨128398186945333555979133743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85598791296889037319422495 128398186945333555979133743)
  ·
    refine ⟨192597280418000333968700615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128398186945333555979133743 192597280418000333968700615)
    ·
      refine ⟨288895920627000500953050923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192597280418000333968700615 288895920627000500953050923)
      ·
        refine ⟨433343880940500751429576385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288895920627000500953050923 433343880940500751429576385)
        ·
          refine ⟨325007910705375563572182289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433343880940500751429576385 325007910705375563572182289)
          ·
            refine ⟨243755933029031672679136717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325007910705375563572182289 243755933029031672679136717)
            ·
              refine ⟨91408474885886877254676269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243755933029031672679136717 91408474885886877254676269)
              ·
                refine ⟨34278178082207578970503601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91408474885886877254676269 34278178082207578970503601)
                ·
                  refine ⟨25708633561655684227877701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34278178082207578970503601 25708633561655684227877701)
                  ·
                    refine ⟨4820368792810440792727069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25708633561655684227877701 4820368792810440792727069)
                    ·
                      refine ⟨1807638297303915297272651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4820368792810440792727069 1807638297303915297272651)
                      ·
                        rfl

theorem cell23_3520363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 3].length) (baseStart_3520363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520363 prefixEnd_3520363 := by exact prefixLift 3520363
  have htrace : WordTrace (prefixWord ++ tailWord_3520363) baseStart_3520363 baseEnd_3520363 := by
    simpa [prefixWord, tailWord_3520363, baseEnd_3520363] using wordTrace_append hprefix tailTrace_3520363
  have hstable : (prefixWord ++ tailWord_3520363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520363).length < 2 ^ (prefixWord ++ tailWord_3520363).sum := by decide
  have hdescent : baseEnd_3520363 < baseStart_3520363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520394 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 1, 4, 2]
def baseStart_3520394 : Nat := 118140960795 + 3520394 * 2 ^ 59
def prefixEnd_3520394 : Nat := 4983230072969 + 3 ^ 40 * 3520394 * 2
def baseEnd_3520394 : Nat := 1807654215204204675985009

theorem tailTrace_3520394 : CollatzResearch.WordTrace tailWord_3520394 prefixEnd_3520394 1807654215204204675985009 := by
  unfold tailWord_3520394
  simp only [CollatzResearch.WordTrace]
  refine ⟨32099829402055312068378059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85599545072147498849008157 32099829402055312068378059)
  ·
    refine ⟨48149744103082968102567089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32099829402055312068378059 48149744103082968102567089)
    ·
      refine ⟨36112308077312226076925317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48149744103082968102567089 36112308077312226076925317)
      ·
        refine ⟨6771057764496042389423497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36112308077312226076925317 6771057764496042389423497)
        ·
          refine ⟨5078293323372031792067623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6771057764496042389423497 5078293323372031792067623)
          ·
            refine ⟨7617439985058047688101435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5078293323372031792067623 7617439985058047688101435)
            ·
              refine ⟨11426159977587071532152153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7617439985058047688101435 11426159977587071532152153)
              ·
                refine ⟨8569619983190303649114115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11426159977587071532152153 8569619983190303649114115)
                ·
                  refine ⟨12854429974785455473671173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8569619983190303649114115 12854429974785455473671173)
                  ·
                    refine ⟨2410205620272272901313345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12854429974785455473671173 2410205620272272901313345)
                    ·
                      refine ⟨1807654215204204675985009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2410205620272272901313345 1807654215204204675985009)
                      ·
                        rfl

theorem cell23_3520394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_3520394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520394 prefixEnd_3520394 := by exact prefixLift 3520394
  have htrace : WordTrace (prefixWord ++ tailWord_3520394) baseStart_3520394 baseEnd_3520394 := by
    simpa [prefixWord, tailWord_3520394, baseEnd_3520394] using wordTrace_append hprefix tailTrace_3520394
  have hstable : (prefixWord ++ tailWord_3520394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520394).length < 2 ^ (prefixWord ++ tailWord_3520394).sum := by decide
  have hdescent : baseEnd_3520394 < baseStart_3520394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520398 : List Nat := [4, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2]
def baseStart_3520398 : Nat := 118140960795 + 3520398 * 2 ^ 59
def prefixEnd_3520398 : Nat := 4983230072969 + 3 ^ 40 * 3520398 * 2
def baseEnd_3520398 : Nat := 1807656269126822660334991

theorem tailTrace_3520398 : CollatzResearch.WordTrace tailWord_3520398 prefixEnd_3520398 1807656269126822660334991 := by
  unfold tailWord_3520398
  simp only [CollatzResearch.WordTrace]
  refine ⟨16049932937525844619582231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85599642333471171304438565 16049932937525844619582231)
  ·
    refine ⟨24074899406288766929373347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16049932937525844619582231 24074899406288766929373347)
    ·
      refine ⟨36112349109433150394060021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24074899406288766929373347 36112349109433150394060021)
      ·
        refine ⟨3385532729009357849443127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36112349109433150394060021 3385532729009357849443127)
        ·
          refine ⟨5078299093514036774164691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3385532729009357849443127 5078299093514036774164691)
          ·
            refine ⟨7617448640271055161247037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5078299093514036774164691 7617448640271055161247037)
            ·
              refine ⟨2856543240101645685467639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7617448640271055161247037 2856543240101645685467639)
              ·
                refine ⟨4284814860152468528201459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2856543240101645685467639 4284814860152468528201459)
                ·
                  refine ⟨6427222290228702792302189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4284814860152468528201459 6427222290228702792302189)
                  ·
                    refine ⟨2410208358835763547113321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6427222290228702792302189 2410208358835763547113321)
                    ·
                      refine ⟨1807656269126822660334991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2410208358835763547113321 1807656269126822660334991)
                      ·
                        rfl

theorem cell23_3520398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_3520398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520398 prefixEnd_3520398 := by exact prefixLift 3520398
  have htrace : WordTrace (prefixWord ++ tailWord_3520398) baseStart_3520398 baseEnd_3520398 := by
    simpa [prefixWord, tailWord_3520398, baseEnd_3520398] using wordTrace_append hprefix tailTrace_3520398
  have hstable : (prefixWord ++ tailWord_3520398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520398).length < 2 ^ (prefixWord ++ tailWord_3520398).sum := by decide
  have hdescent : baseEnd_3520398 < baseStart_3520398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520424 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3520424 : Nat := 118140960795 + 3520424 * 2 ^ 59
def prefixEnd_3520424 : Nat := 4983230072969 + 3 ^ 40 * 3520424 * 2
def baseEnd_3520424 : Nat := 1807669619623839558609871

theorem tailTrace_3520424 : CollatzResearch.WordTrace tailWord_3520424 prefixEnd_3520424 1807669619623839558609871 := by
  unfold tailWord_3520424
  simp only [CollatzResearch.WordTrace]
  refine ⟨64200205899056281698552163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85600274532075042264736217 64200205899056281698552163)
  ·
    refine ⟨96300308848584422547828245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64200205899056281698552163 96300308848584422547828245)
    ·
      refine ⟨4514076977277394806929449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 96300308848584422547828245 4514076977277394806929449)
      ·
        refine ⟨3385557732958046105197087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4514076977277394806929449 3385557732958046105197087)
        ·
          refine ⟨5078336599437069157795631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3385557732958046105197087 5078336599437069157795631)
          ·
            refine ⟨7617504899155603736693447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5078336599437069157795631 7617504899155603736693447)
            ·
              refine ⟨11426257348733405605040171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7617504899155603736693447 11426257348733405605040171)
              ·
                refine ⟨17139386023100108407560257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11426257348733405605040171 17139386023100108407560257)
                ·
                  refine ⟨12854539517325081305670193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17139386023100108407560257 12854539517325081305670193)
                  ·
                    refine ⟨9640904637993810979252645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12854539517325081305670193 9640904637993810979252645)
                    ·
                      refine ⟨1807669619623839558609871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9640904637993810979252645 1807669619623839558609871)
                      ·
                        rfl

theorem cell23_3520424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3520424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520424 prefixEnd_3520424 := by exact prefixLift 3520424
  have htrace : WordTrace (prefixWord ++ tailWord_3520424) baseStart_3520424 baseEnd_3520424 := by
    simpa [prefixWord, tailWord_3520424, baseEnd_3520424] using wordTrace_append hprefix tailTrace_3520424
  have hstable : (prefixWord ++ tailWord_3520424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520424).length < 2 ^ (prefixWord ++ tailWord_3520424).sum := by decide
  have hdescent : baseEnd_3520424 < baseStart_3520424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520453 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 2, 3, 5]
def baseStart_3520453 : Nat := 118140960795 + 3520453 * 2 ^ 59
def prefixEnd_3520453 : Nat := 4983230072969 + 3 ^ 40 * 3520453 * 2
def baseEnd_3520453 : Nat := 1807684510562819945147237

theorem tailTrace_3520453 : CollatzResearch.WordTrace tailWord_3520453 prefixEnd_3520453 1807684510562819945147237 := by
  unfold tailWord_3520453
  simp only [CollatzResearch.WordTrace]
  refine ⟨128401469515007501349910013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85600979676671667566606675 128401469515007501349910013)
  ·
    refine ⟨48150551068127813006216255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128401469515007501349910013 48150551068127813006216255)
    ·
      refine ⟨72225826602191719509324383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48150551068127813006216255 72225826602191719509324383)
      ·
        refine ⟨108338739903287579263986575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72225826602191719509324383 108338739903287579263986575)
        ·
          refine ⟨162508109854931368895979863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108338739903287579263986575 162508109854931368895979863)
          ·
            refine ⟨243762164782397053343969795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162508109854931368895979863 243762164782397053343969795)
            ·
              refine ⟨365643247173595580015954693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243762164782397053343969795 365643247173595580015954693)
              ·
                refine ⟨68558108845049171252991505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 365643247173595580015954693 68558108845049171252991505)
                ·
                  refine ⟨51418581633786878439743629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68558108845049171252991505 51418581633786878439743629)
                  ·
                    refine ⟨19281968112670079414903861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51418581633786878439743629 19281968112670079414903861)
                    ·
                      refine ⟨1807684510562819945147237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19281968112670079414903861 1807684510562819945147237)
                      ·
                        rfl

theorem cell23_3520453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_3520453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520453 prefixEnd_3520453 := by exact prefixLift 3520453
  have htrace : WordTrace (prefixWord ++ tailWord_3520453) baseStart_3520453 baseEnd_3520453 := by
    simpa [prefixWord, tailWord_3520453, baseEnd_3520453] using wordTrace_append hprefix tailTrace_3520453
  have hstable : (prefixWord ++ tailWord_3520453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520453).length < 2 ^ (prefixWord ++ tailWord_3520453).sum := by decide
  have hdescent : baseEnd_3520453 < baseStart_3520453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520463 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 6]
def baseStart_3520463 : Nat := 118140960795 + 3520463 * 2 ^ 59
def prefixEnd_3520463 : Nat := 4983230072969 + 3 ^ 40 * 3520463 * 2
def baseEnd_3520463 : Nat := 1807689645369364906022191

theorem tailTrace_3520463 : CollatzResearch.WordTrace tailWord_3520463 prefixEnd_3520463 1807689645369364906022191 := by
  unfold tailWord_3520463
  simp only [CollatzResearch.WordTrace]
  refine ⟨128401834244971273057774043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85601222829980848705182695 128401834244971273057774043)
  ·
    refine ⟨192602751367456909586661065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128401834244971273057774043 192602751367456909586661065)
    ·
      refine ⟨144452063525592682189995799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192602751367456909586661065 144452063525592682189995799)
      ·
        refine ⟨216678095288389023284993699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144452063525592682189995799 216678095288389023284993699)
        ·
          refine ⟨325017142932583534927490549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216678095288389023284993699 325017142932583534927490549)
          ·
            refine ⟨30470357149929706399452239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 325017142932583534927490549 30470357149929706399452239)
            ·
              refine ⟨45705535724894559599178359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30470357149929706399452239 45705535724894559599178359)
              ·
                refine ⟨68558303587341839398767539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45705535724894559599178359 68558303587341839398767539)
                ·
                  refine ⟨102837455381012759098151309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68558303587341839398767539 102837455381012759098151309)
                  ·
                    refine ⟨38564045767879784661806741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102837455381012759098151309 38564045767879784661806741)
                    ·
                      refine ⟨1807689645369364906022191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38564045767879784661806741 1807689645369364906022191)
                      ·
                        rfl

theorem cell23_3520463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_3520463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520463 prefixEnd_3520463 := by exact prefixLift 3520463
  have htrace : WordTrace (prefixWord ++ tailWord_3520463) baseStart_3520463 baseEnd_3520463 := by
    simpa [prefixWord, tailWord_3520463, baseEnd_3520463] using wordTrace_append hprefix tailTrace_3520463
  have hstable : (prefixWord ++ tailWord_3520463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520463).length < 2 ^ (prefixWord ++ tailWord_3520463).sum := by decide
  have hdescent : baseEnd_3520463 < baseStart_3520463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520503 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 4, 9]
def baseStart_3520503 : Nat := 118140960795 + 3520503 * 2 ^ 59
def prefixEnd_3520503 : Nat := 4983230072969 + 3 ^ 40 * 3520503 * 2
def baseEnd_3520503 : Nat := 602570061531848249840669

theorem tailTrace_3520503 : CollatzResearch.WordTrace tailWord_3520503 prefixEnd_3520503 602570061531848249840669 := by
  unfold tailWord_3520503
  simp only [CollatzResearch.WordTrace]
  refine ⟨128403293164826359889230163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85602195443217573259486775 128403293164826359889230163)
  ·
    refine ⟨192604939747239539833845245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128403293164826359889230163 192604939747239539833845245)
    ·
      refine ⟨72226852405214827437691967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192604939747239539833845245 72226852405214827437691967)
      ·
        refine ⟨108340278607822241156537951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72226852405214827437691967 108340278607822241156537951)
        ·
          refine ⟨162510417911733361734806927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108340278607822241156537951 162510417911733361734806927)
          ·
            refine ⟨243765626867600042602210391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162510417911733361734806927 243765626867600042602210391)
            ·
              refine ⟨365648440301400063903315587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243765626867600042602210391 365648440301400063903315587)
              ·
                refine ⟨548472660452100095854973381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365648440301400063903315587 548472660452100095854973381)
                ·
                  refine ⟨102838623834768767972807509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 548472660452100095854973381 102838623834768767972807509)
                  ·
                    refine ⟨602570061531848249840669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 102838623834768767972807509 602570061531848249840669)
                    ·
                      rfl

theorem cell23_3520503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_3520503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520503 prefixEnd_3520503 := by exact prefixLift 3520503
  have htrace : WordTrace (prefixWord ++ tailWord_3520503) baseStart_3520503 baseEnd_3520503 := by
    simpa [prefixWord, tailWord_3520503, baseEnd_3520503] using wordTrace_append hprefix tailTrace_3520503
  have hstable : (prefixWord ++ tailWord_3520503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520503).length < 2 ^ (prefixWord ++ tailWord_3520503).sum := by decide
  have hdescent : baseEnd_3520503 < baseStart_3520503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520554 : List Nat := [3, 1, 4, 1, 2, 1, 3, 2, 1, 5]
def baseStart_3520554 : Nat := 118140960795 + 3520554 * 2 ^ 59
def prefixEnd_3520554 : Nat := 4983230072969 + 3 ^ 40 * 3520554 * 2
def baseEnd_3520554 : Nat := 602578790702974683328091

theorem tailTrace_3520554 : CollatzResearch.WordTrace tailWord_3520554 prefixEnd_3520554 602578790702974683328091 := by
  unfold tailWord_3520554
  simp only [CollatzResearch.WordTrace]
  refine ⟨32101288321910398899834179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85603435525094397066224477 32101288321910398899834179)
  ·
    refine ⟨48151932482865598349751269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32101288321910398899834179 48151932482865598349751269)
    ·
      refine ⟨9028487340537299690578363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48151932482865598349751269 9028487340537299690578363)
      ·
        refine ⟨13542731010805949535867545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9028487340537299690578363 13542731010805949535867545)
        ·
          refine ⟨10157048258104462151900659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13542731010805949535867545 10157048258104462151900659)
          ·
            refine ⟨15235572387156693227850989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10157048258104462151900659 15235572387156693227850989)
            ·
              refine ⟨5713339645183759960444121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15235572387156693227850989 5713339645183759960444121)
              ·
                refine ⟨4285004733887819970333091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5713339645183759960444121 4285004733887819970333091)
                ·
                  refine ⟨6427507100831729955499637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4285004733887819970333091 6427507100831729955499637)
                  ·
                    refine ⟨602578790702974683328091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6427507100831729955499637 602578790702974683328091)
                    ·
                      rfl

theorem cell23_3520554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_3520554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520554 prefixEnd_3520554 := by exact prefixLift 3520554
  have htrace : WordTrace (prefixWord ++ tailWord_3520554) baseStart_3520554 baseEnd_3520554 := by
    simpa [prefixWord, tailWord_3520554, baseEnd_3520554] using wordTrace_append hprefix tailTrace_3520554
  have hstable : (prefixWord ++ tailWord_3520554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520554).length < 2 ^ (prefixWord ++ tailWord_3520554).sum := by decide
  have hdescent : baseEnd_3520554 < baseStart_3520554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520591 : List Nat := [1, 1, 2, 1, 1, 2, 2, 8, 1, 2, 2]
def baseStart_3520591 : Nat := 118140960795 + 3520591 * 2 ^ 59
def prefixEnd_3520591 : Nat := 4983230072969 + 3 ^ 40 * 3520591 * 2
def baseEnd_3520591 : Nat := 1807755370893140405221603

theorem tailTrace_3520591 : CollatzResearch.WordTrace tailWord_3520591 prefixEnd_3520591 1807755370893140405221603 := by
  unfold tailWord_3520591
  simp only [CollatzResearch.WordTrace]
  refine ⟨128406502788507550918433627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85604335192338367278955751 128406502788507550918433627)
  ·
    refine ⟨192609754182761326377650441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128406502788507550918433627 192609754182761326377650441)
    ·
      refine ⟨144457315637070994783237831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192609754182761326377650441 144457315637070994783237831)
      ·
        refine ⟨216685973455606492174856747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144457315637070994783237831 216685973455606492174856747)
        ·
          refine ⟨325028960183409738262285121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216685973455606492174856747 325028960183409738262285121)
          ·
            refine ⟨243771720137557303696713841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325028960183409738262285121 243771720137557303696713841)
            ·
              refine ⟨182828790103167977772535381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243771720137557303696713841 182828790103167977772535381)
              ·
                refine ⟨2142524884021499739521899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 182828790103167977772535381 2142524884021499739521899)
                ·
                  refine ⟨3213787326032249609282849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142524884021499739521899 3213787326032249609282849)
                  ·
                    refine ⟨2410340494524187206962137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3213787326032249609282849 2410340494524187206962137)
                    ·
                      refine ⟨1807755370893140405221603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2410340494524187206962137 1807755370893140405221603)
                      ·
                        rfl

theorem cell23_3520591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 1, 2, 2].length) (baseStart_3520591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520591 prefixEnd_3520591 := by exact prefixLift 3520591
  have htrace : WordTrace (prefixWord ++ tailWord_3520591) baseStart_3520591 baseEnd_3520591 := by
    simpa [prefixWord, tailWord_3520591, baseEnd_3520591] using wordTrace_append hprefix tailTrace_3520591
  have hstable : (prefixWord ++ tailWord_3520591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520591).length < 2 ^ (prefixWord ++ tailWord_3520591).sum := by decide
  have hdescent : baseEnd_3520591 < baseStart_3520591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520597 : List Nat := [1, 3, 2, 2, 1, 5, 1, 8]
def baseStart_3520597 : Nat := 118140960795 + 3520597 * 2 ^ 59
def prefixEnd_3520597 : Nat := 4983230072969 + 3 ^ 40 * 3520597 * 2
def baseEnd_3520597 : Nat := 66954016732483977101725

theorem tailTrace_3520597 : CollatzResearch.WordTrace tailWord_3520597 prefixEnd_3520597 66954016732483977101725 := by
  unfold tailWord_3520597
  simp only [CollatzResearch.WordTrace]
  refine ⟨128406721626485813943152045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85604481084323875962101363 128406721626485813943152045)
  ·
    refine ⟨48152520609932180228682017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128406721626485813943152045 48152520609932180228682017)
    ·
      refine ⟨36114390457449135171511513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48152520609932180228682017 36114390457449135171511513)
      ·
        refine ⟨27085792843086851378633635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36114390457449135171511513 27085792843086851378633635)
        ·
          refine ⟨40628689264630277067950453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27085792843086851378633635 40628689264630277067950453)
          ·
            refine ⟨3808939618559088475120355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40628689264630277067950453 3808939618559088475120355)
            ·
              refine ⟨5713409427838632712680533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3808939618559088475120355 5713409427838632712680533)
              ·
                refine ⟨66954016732483977101725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5713409427838632712680533 66954016732483977101725)
                ·
                  rfl

theorem cell23_3520597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 8].length) (baseStart_3520597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520597 prefixEnd_3520597 := by exact prefixLift 3520597
  have htrace : WordTrace (prefixWord ++ tailWord_3520597) baseStart_3520597 baseEnd_3520597 := by
    simpa [prefixWord, tailWord_3520597, baseEnd_3520597] using wordTrace_append hprefix tailTrace_3520597
  have hstable : (prefixWord ++ tailWord_3520597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520597).length < 2 ^ (prefixWord ++ tailWord_3520597).sum := by decide
  have hdescent : baseEnd_3520597 < baseStart_3520597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520604 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_3520604 : Nat := 118140960795 + 3520604 * 2 ^ 59
def prefixEnd_3520604 : Nat := 4983230072969 + 3 ^ 40 * 3520604 * 2
def baseEnd_3520604 : Nat := 1807762046141648854359043

theorem tailTrace_3520604 : CollatzResearch.WordTrace tailWord_3520604 prefixEnd_3520604 1807762046141648854359043 := by
  unfold tailWord_3520604
  simp only [CollatzResearch.WordTrace]
  refine ⟨64203488468730227069328433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85604651291640302759104577 64203488468730227069328433)
  ·
    refine ⟨48152616351547670301996325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64203488468730227069328433 48152616351547670301996325)
    ·
      refine ⟨9028615565915188181624311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48152616351547670301996325 9028615565915188181624311)
      ·
        refine ⟨13542923348872782272436467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9028615565915188181624311 13542923348872782272436467)
        ·
          refine ⟨20314385023309173408654701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13542923348872782272436467 20314385023309173408654701)
          ·
            refine ⟨7617894383740940028245513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20314385023309173408654701 7617894383740940028245513)
            ·
              refine ⟨5713420787805705021184135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7617894383740940028245513 5713420787805705021184135)
              ·
                refine ⟨8570131181708557531776203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5713420787805705021184135 8570131181708557531776203)
                ·
                  refine ⟨12855196772562836297664305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8570131181708557531776203 12855196772562836297664305)
                  ·
                    refine ⟨9641397579422127223248229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12855196772562836297664305 9641397579422127223248229)
                    ·
                      refine ⟨1807762046141648854359043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9641397579422127223248229 1807762046141648854359043)
                      ·
                        rfl

theorem cell23_3520604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_3520604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520604 prefixEnd_3520604 := by exact prefixLift 3520604
  have htrace : WordTrace (prefixWord ++ tailWord_3520604) baseStart_3520604 baseEnd_3520604 := by
    simpa [prefixWord, tailWord_3520604, baseEnd_3520604] using wordTrace_append hprefix tailTrace_3520604
  have hstable : (prefixWord ++ tailWord_3520604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520604).length < 2 ^ (prefixWord ++ tailWord_3520604).sum := by decide
  have hdescent : baseEnd_3520604 < baseStart_3520604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520641 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_3520641 : Nat := 118140960795 + 3520641 * 2 ^ 59
def prefixEnd_3520641 : Nat := 4983230072969 + 3 ^ 40 * 3520641 * 2
def baseEnd_3520641 : Nat := 1807781044925865209596373

theorem tailTrace_3520641 : CollatzResearch.WordTrace tailWord_3520641 prefixEnd_3520641 1807781044925865209596373 := by
  unfold tailWord_3520641
  simp only [CollatzResearch.WordTrace]
  refine ⟨128408326438326409457753777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85605550958884272971835851 128408326438326409457753777)
  ·
    refine ⟨96306244828744807093315333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128408326438326409457753777 96306244828744807093315333)
    ·
      refine ⟨18057420905389651329996625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96306244828744807093315333 18057420905389651329996625)
      ·
        refine ⟨13543065679042238497497469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18057420905389651329996625 13543065679042238497497469)
        ·
          refine ⟨5078649629640839436561551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13543065679042238497497469 5078649629640839436561551)
          ·
            refine ⟨7617974444461259154842327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5078649629640839436561551 7617974444461259154842327)
            ·
              refine ⟨11426961666691888732263491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7617974444461259154842327 11426961666691888732263491)
              ·
                refine ⟨17140442500037833098395237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11426961666691888732263491 17140442500037833098395237)
                ·
                  refine ⟨3213832968757093705949107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17140442500037833098395237 3213832968757093705949107)
                  ·
                    refine ⟨4820749453135640558923661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3213832968757093705949107 4820749453135640558923661)
                    ·
                      refine ⟨1807781044925865209596373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4820749453135640558923661 1807781044925865209596373)
                      ·
                        rfl

theorem cell23_3520641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_3520641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520641 prefixEnd_3520641 := by exact prefixLift 3520641
  have htrace : WordTrace (prefixWord ++ tailWord_3520641) baseStart_3520641 baseEnd_3520641 := by
    simpa [prefixWord, tailWord_3520641, baseEnd_3520641] using wordTrace_append hprefix tailTrace_3520641
  have hstable : (prefixWord ++ tailWord_3520641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520641).length < 2 ^ (prefixWord ++ tailWord_3520641).sum := by decide
  have hdescent : baseEnd_3520641 < baseStart_3520641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520658 : List Nat := [3, 2, 3, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_3520658 : Nat := 118140960795 + 3520658 * 2 ^ 59
def prefixEnd_3520658 : Nat := 4983230072969 + 3 ^ 40 * 3520658 * 2
def baseEnd_3520658 : Nat := 1807789774096991643083795

theorem tailTrace_3520658 : CollatzResearch.WordTrace tailWord_3520658 prefixEnd_3520658 1807789774096991643083795 := by
  unfold tailWord_3520658
  simp only [CollatzResearch.WordTrace]
  refine ⟨32102236619816205340280657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85605964319509880907415085 32102236619816205340280657)
  ·
    refine ⟨24076677464862154005210493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32102236619816205340280657 24076677464862154005210493)
    ·
      refine ⟨9028754049323307751953935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24076677464862154005210493 9028754049323307751953935)
      ·
        refine ⟨13543131073984961627930903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9028754049323307751953935 13543131073984961627930903)
        ·
          refine ⟨20314696610977442441896355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13543131073984961627930903 20314696610977442441896355)
          ·
            refine ⟨30472044916466163662844533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20314696610977442441896355 30472044916466163662844533)
            ·
              refine ⟨2856754210918702843391675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30472044916466163662844533 2856754210918702843391675)
              ·
                refine ⟨4285131316378054265087513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2856754210918702843391675 4285131316378054265087513)
                ·
                  refine ⟨3213848487283540698815635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4285131316378054265087513 3213848487283540698815635)
                  ·
                    refine ⟨4820772730925311048223453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3213848487283540698815635 4820772730925311048223453)
                    ·
                      refine ⟨1807789774096991643083795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4820772730925311048223453 1807789774096991643083795)
                      ·
                        rfl

theorem cell23_3520658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_3520658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520658 prefixEnd_3520658 := by exact prefixLift 3520658
  have htrace : WordTrace (prefixWord ++ tailWord_3520658) baseStart_3520658 baseEnd_3520658 := by
    simpa [prefixWord, tailWord_3520658, baseEnd_3520658] using wordTrace_append hprefix tailTrace_3520658
  have hstable : (prefixWord ++ tailWord_3520658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520658).length < 2 ^ (prefixWord ++ tailWord_3520658).sum := by decide
  have hdescent : baseEnd_3520658 < baseStart_3520658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520704 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 7]
def baseStart_3520704 : Nat := 118140960795 + 3520704 * 2 ^ 59
def prefixEnd_3520704 : Nat := 4983230072969 + 3 ^ 40 * 3520704 * 2
def baseEnd_3520704 : Nat := 200868154911899829234287

theorem tailTrace_3520704 : CollatzResearch.WordTrace tailWord_3520704 prefixEnd_3520704 200868154911899829234287 := by
  unfold tailWord_3520704
  simp only [CollatzResearch.WordTrace]
  refine ⟨64205312118549085608648583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85607082824732114144864777 64205312118549085608648583)
  ·
    refine ⟨96307968177823628412972875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64205312118549085608648583 96307968177823628412972875)
    ·
      refine ⟨144461952266735442619459313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96307968177823628412972875 144461952266735442619459313)
      ·
        refine ⟨108346464200051581964594485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144461952266735442619459313 108346464200051581964594485)
        ·
          refine ⟨10157481018754835809180733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108346464200051581964594485 10157481018754835809180733)
          ·
            refine ⟨3809055382033063428442775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10157481018754835809180733 3809055382033063428442775)
            ·
              refine ⟨5713583073049595142664163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3809055382033063428442775 5713583073049595142664163)
              ·
                refine ⟨8570374609574392713996245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5713583073049595142664163 8570374609574392713996245)
                ·
                  refine ⟨200868154911899829234287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8570374609574392713996245 200868154911899829234287)
                  ·
                    rfl

theorem cell23_3520704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 7].length) (baseStart_3520704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520704 prefixEnd_3520704 := by exact prefixLift 3520704
  have htrace : WordTrace (prefixWord ++ tailWord_3520704) baseStart_3520704 baseEnd_3520704 := by
    simpa [prefixWord, tailWord_3520704, baseEnd_3520704] using wordTrace_append hprefix tailTrace_3520704
  have hstable : (prefixWord ++ tailWord_3520704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520704).length < 2 ^ (prefixWord ++ tailWord_3520704).sum := by decide
  have hdescent : baseEnd_3520704 < baseStart_3520704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520791 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 3]
def baseStart_3520791 : Nat := 118140960795 + 3520791 * 2 ^ 59
def prefixEnd_3520791 : Nat := 4983230072969 + 3 ^ 40 * 3520791 * 2
def baseEnd_3520791 : Nat := 1807858067024039622720683

theorem tailTrace_3520791 : CollatzResearch.WordTrace tailWord_3520791 prefixEnd_3520791 1807858067024039622720683 := by
  unfold tailWord_3520791
  simp only [CollatzResearch.WordTrace]
  refine ⟨128413797387782985075714227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85609198258521990050476151 128413797387782985075714227)
  ·
    refine ⟨192620696081674477613571341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128413797387782985075714227 192620696081674477613571341)
    ·
      refine ⟨72232761030627929105089253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192620696081674477613571341 72232761030627929105089253)
      ·
        refine ⟨13543642693242736707204235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72232761030627929105089253 13543642693242736707204235)
        ·
          refine ⟨20315464039864105060806353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13543642693242736707204235 20315464039864105060806353)
          ·
            refine ⟨15236598029898078795604765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20315464039864105060806353 15236598029898078795604765)
            ·
              refine ⟨5713724261211779548351787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15236598029898078795604765 5713724261211779548351787)
              ·
                refine ⟨8570586391817669322527681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5713724261211779548351787 8570586391817669322527681)
                ·
                  refine ⟨6427939793863251991895761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8570586391817669322527681 6427939793863251991895761)
                  ·
                    refine ⟨4820954845397438993921821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6427939793863251991895761 4820954845397438993921821)
                    ·
                      refine ⟨1807858067024039622720683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4820954845397438993921821 1807858067024039622720683)
                      ·
                        rfl

theorem cell23_3520791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_3520791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520791 prefixEnd_3520791 := by exact prefixLift 3520791
  have htrace : WordTrace (prefixWord ++ tailWord_3520791) baseStart_3520791 baseEnd_3520791 := by
    simpa [prefixWord, tailWord_3520791, baseEnd_3520791] using wordTrace_append hprefix tailTrace_3520791
  have hstable : (prefixWord ++ tailWord_3520791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520791).length < 2 ^ (prefixWord ++ tailWord_3520791).sum := by decide
  have hdescent : baseEnd_3520791 < baseStart_3520791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520871 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 4, 4]
def baseStart_3520871 : Nat := 118140960795 + 3520871 * 2 ^ 59
def prefixEnd_3520871 : Nat := 4983230072969 + 3 ^ 40 * 3520871 * 2
def baseEnd_3520871 : Nat := 602633048492133103240105

theorem tailTrace_3520871 : CollatzResearch.WordTrace tailWord_3520871 prefixEnd_3520871 602633048492133103240105 := by
  unfold tailWord_3520871
  simp only [CollatzResearch.WordTrace]
  refine ⟨128416715227493158738626467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85611143484995439159084311 128416715227493158738626467)
  ·
    refine ⟨192625072841239738107939701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128416715227493158738626467 192625072841239738107939701)
    ·
      refine ⟨18058600578866225447619347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192625072841239738107939701 18058600578866225447619347)
      ·
        refine ⟨27087900868299338171429021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18058600578866225447619347 27087900868299338171429021)
        ·
          refine ⟨10157962825612251814285883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27087900868299338171429021 10157962825612251814285883)
          ·
            refine ⟨15236944238418377721428825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10157962825612251814285883 15236944238418377721428825)
            ·
              refine ⟨11427708178813783291071619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15236944238418377721428825 11427708178813783291071619)
              ·
                refine ⟨17141562268220674936607429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11427708178813783291071619 17141562268220674936607429)
                ·
                  refine ⟨3214042925291376550613893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17141562268220674936607429 3214042925291376550613893)
                  ·
                    refine ⟨602633048492133103240105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3214042925291376550613893 602633048492133103240105)
                    ·
                      rfl

theorem cell23_3520871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_3520871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520871 prefixEnd_3520871 := by exact prefixLift 3520871
  have htrace : WordTrace (prefixWord ++ tailWord_3520871) baseStart_3520871 baseEnd_3520871 := by
    simpa [prefixWord, tailWord_3520871, baseEnd_3520871] using wordTrace_append hprefix tailTrace_3520871
  have hstable : (prefixWord ++ tailWord_3520871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520871).length < 2 ^ (prefixWord ++ tailWord_3520871).sum := by decide
  have hdescent : baseEnd_3520871 < baseStart_3520871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520872 : List Nat := [2, 1, 4, 2, 2, 2, 3, 2, 1, 1, 3]
def baseStart_3520872 : Nat := 118140960795 + 3520872 * 2 ^ 59
def prefixEnd_3520872 : Nat := 4983230072969 + 3 ^ 40 * 3520872 * 2
def baseEnd_3520872 : Nat := 1807899658957053805807811

theorem tailTrace_3520872 : CollatzResearch.WordTrace tailWord_3520872 prefixEnd_3520872 1807899658957053805807811 := by
  unfold tailWord_3520872
  simp only [CollatzResearch.WordTrace]
  refine ⟨64208375850244767954706435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85611167800326357272941913 64208375850244767954706435)
  ·
    refine ⟨96312563775367151932059653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64208375850244767954706435 96312563775367151932059653)
    ·
      refine ⟨18058605707881340987261185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96312563775367151932059653 18058605707881340987261185)
      ·
        refine ⟨13543954280911005740445889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18058605707881340987261185 13543954280911005740445889)
        ·
          refine ⟨10157965710683254305334417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13543954280911005740445889 10157965710683254305334417)
          ·
            refine ⟨7618474283012440729000813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10157965710683254305334417 7618474283012440729000813)
            ·
              refine ⟨2856927856129665273375305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7618474283012440729000813 2856927856129665273375305)
              ·
                refine ⟨2142695892097248955031479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2856927856129665273375305 2142695892097248955031479)
                ·
                  refine ⟨3214043838145873432547219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142695892097248955031479 3214043838145873432547219)
                  ·
                    refine ⟨4821065757218810148820829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3214043838145873432547219 4821065757218810148820829)
                    ·
                      refine ⟨1807899658957053805807811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4821065757218810148820829 1807899658957053805807811)
                      ·
                        rfl

theorem cell23_3520872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_3520872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520872 prefixEnd_3520872 := by exact prefixLift 3520872
  have htrace : WordTrace (prefixWord ++ tailWord_3520872) baseStart_3520872 baseEnd_3520872 := by
    simpa [prefixWord, tailWord_3520872, baseEnd_3520872] using wordTrace_append hprefix tailTrace_3520872
  have hstable : (prefixWord ++ tailWord_3520872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520872).length < 2 ^ (prefixWord ++ tailWord_3520872).sum := by decide
  have hdescent : baseEnd_3520872 < baseStart_3520872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520918 : List Nat := [5, 3, 1, 2, 12]
def baseStart_3520918 : Nat := 118140960795 + 3520918 * 2 ^ 59
def prefixEnd_3520918 : Nat := 4983230072969 + 3 ^ 40 * 3520918 * 2
def baseEnd_3520918 : Nat := 2480004498034513890031

theorem tailTrace_3520918 : CollatzResearch.WordTrace tailWord_3520918 prefixEnd_3520918 2480004498034513890031 := by
  unfold tailWord_3520918
  simp only [CollatzResearch.WordTrace]
  refine ⟨8026151841145180360349213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85612286305548590510391605 8026151841145180360349213)
  ·
    refine ⟨3009806940429442635130955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8026151841145180360349213 3009806940429442635130955)
    ·
      refine ⟨4514710410644163952696433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3009806940429442635130955 4514710410644163952696433)
      ·
        refine ⟨3386032807983122964522325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4514710410644163952696433 3386032807983122964522325)
        ·
          refine ⟨2480004498034513890031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3386032807983122964522325 2480004498034513890031)
          ·
            rfl

theorem cell23_3520918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 12].length) (baseStart_3520918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520918 prefixEnd_3520918 := by exact prefixLift 3520918
  have htrace : WordTrace (prefixWord ++ tailWord_3520918) baseStart_3520918 baseEnd_3520918 := by
    simpa [prefixWord, tailWord_3520918, baseEnd_3520918] using wordTrace_append hprefix tailTrace_3520918
  have hstable : (prefixWord ++ tailWord_3520918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520918).length < 2 ^ (prefixWord ++ tailWord_3520918).sum := by decide
  have hdescent : baseEnd_3520918 < baseStart_3520918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520928 : List Nat := [2, 1, 1, 4, 1, 3, 1, 4, 2, 1, 3]
def baseStart_3520928 : Nat := 118140960795 + 3520928 * 2 ^ 59
def prefixEnd_3520928 : Nat := 4983230072969 + 3 ^ 40 * 3520928 * 2
def baseEnd_3520928 : Nat := 1807928413873705586707553

theorem tailTrace_3520928 : CollatzResearch.WordTrace tailWord_3520928 prefixEnd_3520928 1807928413873705586707553 := by
  unfold tailWord_3520928
  simp only [CollatzResearch.WordTrace]
  refine ⟨64209397094143328736725719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85612529458857771648967625 64209397094143328736725719)
  ·
    refine ⟨96314095641214993105088579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64209397094143328736725719 96314095641214993105088579)
    ·
      refine ⟨144471143461822489657632869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96314095641214993105088579 144471143461822489657632869)
      ·
        refine ⟨27088339399091716810806163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144471143461822489657632869 27088339399091716810806163)
        ·
          refine ⟨40632509098637575216209245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27088339399091716810806163 40632509098637575216209245)
          ·
            refine ⟨15237190911989090706078467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40632509098637575216209245 15237190911989090706078467)
            ·
              refine ⟨22855786367983636059117701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15237190911989090706078467 22855786367983636059117701)
              ·
                refine ⟨4285459943996931761084569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22855786367983636059117701 4285459943996931761084569)
                ·
                  refine ⟨3214094957997698820813427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4285459943996931761084569 3214094957997698820813427)
                  ·
                    refine ⟨4821142436996548231220141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3214094957997698820813427 4821142436996548231220141)
                    ·
                      refine ⟨1807928413873705586707553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4821142436996548231220141 1807928413873705586707553)
                      ·
                        rfl

theorem cell23_3520928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_3520928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520928 prefixEnd_3520928 := by exact prefixLift 3520928
  have htrace : WordTrace (prefixWord ++ tailWord_3520928) baseStart_3520928 baseEnd_3520928 := by
    simpa [prefixWord, tailWord_3520928, baseEnd_3520928] using wordTrace_append hprefix tailTrace_3520928
  have hstable : (prefixWord ++ tailWord_3520928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520928).length < 2 ^ (prefixWord ++ tailWord_3520928).sum := by decide
  have hdescent : baseEnd_3520928 < baseStart_3520928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520929 : List Nat := [1, 2, 3, 5, 1, 1, 1, 4, 1, 2, 2]
def baseStart_3520929 : Nat := 118140960795 + 3520929 * 2 ^ 59
def prefixEnd_3520929 : Nat := 4983230072969 + 3 ^ 40 * 3520929 * 2
def baseEnd_3520929 : Nat := 1807928927354360082795049

theorem tailTrace_3520929 : CollatzResearch.WordTrace tailWord_3520929 prefixEnd_3520929 1807928927354360082795049 := by
  unfold tailWord_3520929
  simp only [CollatzResearch.WordTrace]
  refine ⟨128418830661283034644237841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85612553774188689762825227 128418830661283034644237841)
  ·
    refine ⟨96314122995962275983178381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128418830661283034644237841 96314122995962275983178381)
    ·
      refine ⟨36117796123485853493691893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96314122995962275983178381 36117796123485853493691893)
      ·
        refine ⟨3386043386576798765033615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36117796123485853493691893 3386043386576798765033615)
        ·
          refine ⟨5079065079865198147550423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3386043386576798765033615 5079065079865198147550423)
          ·
            refine ⟨7618597619797797221325635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5079065079865198147550423 7618597619797797221325635)
            ·
              refine ⟨11427896429696695831988453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7618597619797797221325635 11427896429696695831988453)
              ·
                refine ⟨2142730580568130468497835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11427896429696695831988453 2142730580568130468497835)
                ·
                  refine ⟨3214095870852195702746753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142730580568130468497835 3214095870852195702746753)
                  ·
                    refine ⟨2410571903139146777060065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3214095870852195702746753 2410571903139146777060065)
                    ·
                      refine ⟨1807928927354360082795049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2410571903139146777060065 1807928927354360082795049)
                      ·
                        rfl

theorem cell23_3520929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_3520929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520929 prefixEnd_3520929 := by exact prefixLift 3520929
  have htrace : WordTrace (prefixWord ++ tailWord_3520929) baseStart_3520929 baseEnd_3520929 := by
    simpa [prefixWord, tailWord_3520929, baseEnd_3520929] using wordTrace_append hprefix tailTrace_3520929
  have hstable : (prefixWord ++ tailWord_3520929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520929).length < 2 ^ (prefixWord ++ tailWord_3520929).sum := by decide
  have hdescent : baseEnd_3520929 < baseStart_3520929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520954 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5]
def baseStart_3520954 : Nat := 118140960795 + 3520954 * 2 ^ 59
def prefixEnd_3520954 : Nat := 4983230072969 + 3 ^ 40 * 3520954 * 2
def baseEnd_3520954 : Nat := 1807941764370722484982433

theorem tailTrace_3520954 : CollatzResearch.WordTrace tailWord_3520954 prefixEnd_3520954 1807941764370722484982433 := by
  unfold tailWord_3520954
  simp only [CollatzResearch.WordTrace]
  refine ⟨32104935621548115978474479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85613161657461642609265277 32104935621548115978474479)
  ·
    refine ⟨48157403432322173967711719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32104935621548115978474479 48157403432322173967711719)
    ·
      refine ⟨72236105148483260951567579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48157403432322173967711719 72236105148483260951567579)
      ·
        refine ⟨108354157722724891427351369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72236105148483260951567579 108354157722724891427351369)
        ·
          refine ⟨81265618292043668570513527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108354157722724891427351369 81265618292043668570513527)
          ·
            refine ⟨121898427438065502855770291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81265618292043668570513527 121898427438065502855770291)
            ·
              refine ⟨182847641157098254283655437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121898427438065502855770291 182847641157098254283655437)
              ·
                refine ⟨68567865433911845356370789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182847641157098254283655437 68567865433911845356370789)
                ·
                  refine ⟨12856474768858471004319523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68567865433911845356370789 12856474768858471004319523)
                  ·
                    refine ⟨19284712153287706506479285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12856474768858471004319523 19284712153287706506479285)
                    ·
                      refine ⟨1807941764370722484982433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19284712153287706506479285 1807941764370722484982433)
                      ·
                        rfl

theorem cell23_3520954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_3520954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520954 prefixEnd_3520954 := by exact prefixLift 3520954
  have htrace : WordTrace (prefixWord ++ tailWord_3520954) baseStart_3520954 baseEnd_3520954 := by
    simpa [prefixWord, tailWord_3520954, baseEnd_3520954] using wordTrace_append hprefix tailTrace_3520954
  have hstable : (prefixWord ++ tailWord_3520954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520954).length < 2 ^ (prefixWord ++ tailWord_3520954).sum := by decide
  have hdescent : baseEnd_3520954 < baseStart_3520954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520968 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 1, 4, 2]
def baseStart_3520968 : Nat := 118140960795 + 3520968 * 2 ^ 59
def prefixEnd_3520968 : Nat := 4983230072969 + 3 ^ 40 * 3520968 * 2
def baseEnd_3520968 : Nat := 1807948953099885430207369

theorem tailTrace_3520968 : CollatzResearch.WordTrace tailWord_3520968 prefixEnd_3520968 1807948953099885430207369 := by
  unfold tailWord_3520968
  simp only [CollatzResearch.WordTrace]
  refine ⟨64210126554070872152453779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85613502072094496203271705 64210126554070872152453779)
  ·
    refine ⟨96315189831106308228680669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64210126554070872152453779 96315189831106308228680669)
    ·
      refine ⟨36118196186664865585755251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96315189831106308228680669 36118196186664865585755251)
      ·
        refine ⟨54177294279997298378632877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36118196186664865585755251 54177294279997298378632877)
        ·
          refine ⟨20316485354998986891987329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54177294279997298378632877 20316485354998986891987329)
          ·
            refine ⟨15237364016249240168990497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20316485354998986891987329 15237364016249240168990497)
            ·
              refine ⟨11428023012186930126742873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15237364016249240168990497 11428023012186930126742873)
              ·
                refine ⟨8571017259140197595057155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11428023012186930126742873 8571017259140197595057155)
                ·
                  refine ⟨12856525888710296392585733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8571017259140197595057155 12856525888710296392585733)
                  ·
                    refine ⟨2410598604133180573609825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12856525888710296392585733 2410598604133180573609825)
                    ·
                      refine ⟨1807948953099885430207369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2410598604133180573609825 1807948953099885430207369)
                      ·
                        rfl

theorem cell23_3520968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_3520968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520968 prefixEnd_3520968 := by exact prefixLift 3520968
  have htrace : WordTrace (prefixWord ++ tailWord_3520968) baseStart_3520968 baseEnd_3520968 := by
    simpa [prefixWord, tailWord_3520968, baseEnd_3520968] using wordTrace_append hprefix tailTrace_3520968
  have hstable : (prefixWord ++ tailWord_3520968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520968).length < 2 ^ (prefixWord ++ tailWord_3520968).sum := by decide
  have hdescent : baseEnd_3520968 < baseStart_3520968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520974 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 11]
def baseStart_3520974 : Nat := 118140960795 + 3520974 * 2 ^ 59
def prefixEnd_3520974 : Nat := 4983230072969 + 3 ^ 40 * 3520974 * 2
def baseEnd_3520974 : Nat := 200883559331534711859149

theorem tailTrace_3520974 : CollatzResearch.WordTrace tailWord_3520974 prefixEnd_3520974 200883559331534711859149 := by
  unfold tailWord_3520974
  simp only [CollatzResearch.WordTrace]
  refine ⟨16052558993265000916203247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85613647964080004886417317 16052558993265000916203247)
  ·
    refine ⟨24078838489897501374304871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16052558993265000916203247 24078838489897501374304871)
    ·
      refine ⟨36118257734846252061457307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24078838489897501374304871 36118257734846252061457307)
      ·
        refine ⟨54177386602269378092185961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36118257734846252061457307 54177386602269378092185961)
        ·
          refine ⟨40633039951702033569139471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54177386602269378092185961 40633039951702033569139471)
          ·
            refine ⟨60949559927553050353709207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40633039951702033569139471 60949559927553050353709207)
            ·
              refine ⟨91424339891329575530563811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60949559927553050353709207 91424339891329575530563811)
              ·
                refine ⟨137136509836994363295845717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91424339891329575530563811 137136509836994363295845717)
                ·
                  refine ⟨200883559331534711859149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 137136509836994363295845717 200883559331534711859149)
                  ·
                    rfl

theorem cell23_3520974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_3520974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520974 prefixEnd_3520974 := by exact prefixLift 3520974
  have htrace : WordTrace (prefixWord ++ tailWord_3520974) baseStart_3520974 baseEnd_3520974 := by
    simpa [prefixWord, tailWord_3520974, baseEnd_3520974] using wordTrace_append hprefix tailTrace_3520974
  have hstable : (prefixWord ++ tailWord_3520974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520974).length < 2 ^ (prefixWord ++ tailWord_3520974).sum := by decide
  have hdescent : baseEnd_3520974 < baseStart_3520974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520981 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_3520981 : Nat := 118140960795 + 3520981 * 2 ^ 59
def prefixEnd_3520981 : Nat := 4983230072969 + 3 ^ 40 * 3520981 * 2
def baseEnd_3520981 : Nat := 1807955628348393879344809

theorem tailTrace_3520981 : CollatzResearch.WordTrace tailWord_3520981 prefixEnd_3520981 1807955628348393879344809 := by
  unfold tailWord_3520981
  simp only [CollatzResearch.WordTrace]
  refine ⟨128420727257094647525130797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85613818171396431683420531 128420727257094647525130797)
  ·
    refine ⟨48157772721410492821924049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128420727257094647525130797 48157772721410492821924049)
    ·
      refine ⟨36118329541057869616443037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48157772721410492821924049 36118329541057869616443037)
      ·
        refine ⟨13544373577896701106166139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36118329541057869616443037 13544373577896701106166139)
        ·
          refine ⟨20316560366845051659249209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13544373577896701106166139 20316560366845051659249209)
          ·
            refine ⟨15237420275133788744436907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20316560366845051659249209 15237420275133788744436907)
            ·
              refine ⟨22856130412700683116655361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15237420275133788744436907 22856130412700683116655361)
              ·
                refine ⟨17142097809525512337491521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22856130412700683116655361 17142097809525512337491521)
                ·
                  refine ⟨12856573357144134253118641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17142097809525512337491521 12856573357144134253118641)
                  ·
                    refine ⟨9642430017858100689838981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12856573357144134253118641 9642430017858100689838981)
                    ·
                      refine ⟨1807955628348393879344809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9642430017858100689838981 1807955628348393879344809)
                      ·
                        rfl

theorem cell23_3520981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_3520981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520981 prefixEnd_3520981 := by exact prefixLift 3520981
  have htrace : WordTrace (prefixWord ++ tailWord_3520981) baseStart_3520981 baseEnd_3520981 := by
    simpa [prefixWord, tailWord_3520981, baseEnd_3520981] using wordTrace_append hprefix tailTrace_3520981
  have hstable : (prefixWord ++ tailWord_3520981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520981).length < 2 ^ (prefixWord ++ tailWord_3520981).sum := by decide
  have hdescent : baseEnd_3520981 < baseStart_3520981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520991 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 7]
def baseStart_3520991 : Nat := 118140960795 + 3520991 * 2 ^ 59
def prefixEnd_3520991 : Nat := 4983230072969 + 3 ^ 40 * 3520991 * 2
def baseEnd_3520991 : Nat := 200884529239437648913307

theorem tailTrace_3520991 : CollatzResearch.WordTrace tailWord_3520991 prefixEnd_3520991 200884529239437648913307 := by
  unfold tailWord_3520991
  simp only [CollatzResearch.WordTrace]
  refine ⟨128421091987058419232994827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85614061324705612821996551 128421091987058419232994827)
  ·
    refine ⟨192631637980587628849492241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128421091987058419232994827 192631637980587628849492241)
    ·
      refine ⟨144473728485440721637119181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192631637980587628849492241 144473728485440721637119181)
      ·
        refine ⟨54177648182040270613919693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144473728485440721637119181 54177648182040270613919693)
        ·
          refine ⟨20316618068265101480219885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54177648182040270613919693 20316618068265101480219885)
          ·
            refine ⟨7618731775599413055082457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20316618068265101480219885 7618731775599413055082457)
            ·
              refine ⟨5714048831699559791311843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7618731775599413055082457 5714048831699559791311843)
              ·
                refine ⟨8571073247549339686967765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5714048831699559791311843 8571073247549339686967765)
                ·
                  refine ⟨200884529239437648913307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8571073247549339686967765 200884529239437648913307)
                  ·
                    rfl

theorem cell23_3520991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 7].length) (baseStart_3520991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3520991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3520991 prefixEnd_3520991 := by exact prefixLift 3520991
  have htrace : WordTrace (prefixWord ++ tailWord_3520991) baseStart_3520991 baseEnd_3520991 := by
    simpa [prefixWord, tailWord_3520991, baseEnd_3520991] using wordTrace_append hprefix tailTrace_3520991
  have hstable : (prefixWord ++ tailWord_3520991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520991).length < 2 ^ (prefixWord ++ tailWord_3520991).sum := by decide
  have hdescent : baseEnd_3520991 < baseStart_3520991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521004 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 3, 7]
def baseStart_3521004 : Nat := 118140960795 + 3521004 * 2 ^ 59
def prefixEnd_3521004 : Nat := 4983230072969 + 3 ^ 40 * 3521004 * 2
def baseEnd_3521004 : Nat := 602655812801149096452401

theorem tailTrace_3521004 : CollatzResearch.WordTrace tailWord_3521004 prefixEnd_3521004 602655812801149096452401 := by
  unfold tailWord_3521004
  simp only [CollatzResearch.WordTrace]
  refine ⟨64210783068005661226609033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85614377424007548302145377 64210783068005661226609033)
  ·
    refine ⟨48158087301004245919956775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64210783068005661226609033 48158087301004245919956775)
    ·
      refine ⟨72237130951506368879935163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48158087301004245919956775 72237130951506368879935163)
      ·
        refine ⟨108355696427259553319902745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72237130951506368879935163 108355696427259553319902745)
        ·
          refine ⟨81266772320444664989927059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108355696427259553319902745 81266772320444664989927059)
          ·
            refine ⟨121900158480666997484890589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81266772320444664989927059 121900158480666997484890589)
            ·
              refine ⟨45712559430250124056833971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121900158480666997484890589 45712559430250124056833971)
              ·
                refine ⟨68568839145375186085250957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45712559430250124056833971 68568839145375186085250957)
                ·
                  refine ⟨25713314679515694781969109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68568839145375186085250957 25713314679515694781969109)
                  ·
                    refine ⟨602655812801149096452401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25713314679515694781969109 602655812801149096452401)
                    ·
                      rfl

theorem cell23_3521004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_3521004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521004 prefixEnd_3521004 := by exact prefixLift 3521004
  have htrace : WordTrace (prefixWord ++ tailWord_3521004) baseStart_3521004 baseEnd_3521004 := by
    simpa [prefixWord, tailWord_3521004, baseEnd_3521004] using wordTrace_append hprefix tailTrace_3521004
  have hstable : (prefixWord ++ tailWord_3521004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521004).length < 2 ^ (prefixWord ++ tailWord_3521004).sum := by decide
  have hdescent : baseEnd_3521004 < baseStart_3521004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521021 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 2, 5]
def baseStart_3521021 : Nat := 118140960795 + 3521021 * 2 ^ 59
def prefixEnd_3521021 : Nat := 4983230072969 + 3 ^ 40 * 3521021 * 2
def baseEnd_3521021 : Nat := 602658722524857907614875

theorem tailTrace_3521021 : CollatzResearch.WordTrace tailWord_3521021 prefixEnd_3521021 602658722524857907614875 := by
  unfold tailWord_3521021
  simp only [CollatzResearch.WordTrace]
  refine ⟨128422186176949734356586917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85614790784633156237724611 128422186176949734356586917)
  ·
    refine ⟨24079159908178075191860047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128422186176949734356586917 24079159908178075191860047)
    ·
      refine ⟨36118739862267112787790071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24079159908178075191860047 36118739862267112787790071)
      ·
        refine ⟨54178109793400669181685107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36118739862267112787790071 54178109793400669181685107)
        ·
          refine ⟨81267164690101003772527661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54178109793400669181685107 81267164690101003772527661)
          ·
            refine ⟨30475186758787876414697873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81267164690101003772527661 30475186758787876414697873)
            ·
              refine ⟨22856390069090907311023405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30475186758787876414697873 22856390069090907311023405)
              ·
                refine ⟨8571146275909090241633777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22856390069090907311023405 8571146275909090241633777)
                ·
                  refine ⟨6428359706931817681225333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8571146275909090241633777 6428359706931817681225333)
                  ·
                    refine ⟨602658722524857907614875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6428359706931817681225333 602658722524857907614875)
                    ·
                      rfl

theorem cell23_3521021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_3521021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521021 prefixEnd_3521021 := by exact prefixLift 3521021
  have htrace : WordTrace (prefixWord ++ tailWord_3521021) baseStart_3521021 baseEnd_3521021 := by
    simpa [prefixWord, tailWord_3521021, baseEnd_3521021] using wordTrace_append hprefix tailTrace_3521021
  have hstable : (prefixWord ++ tailWord_3521021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521021).length < 2 ^ (prefixWord ++ tailWord_3521021).sum := by decide
  have hdescent : baseEnd_3521021 < baseStart_3521021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521025 : List Nat := [1, 2, 4, 1, 3, 3, 1, 3, 5]
def baseStart_3521025 : Nat := 118140960795 + 3521025 * 2 ^ 59
def prefixEnd_3521025 : Nat := 4983230072969 + 3 ^ 40 * 3521025 * 2
def baseEnd_3521025 : Nat := 200886469055243523021623

theorem tailTrace_3521025 : CollatzResearch.WordTrace tailWord_3521025 prefixEnd_3521025 200886469055243523021623 := by
  unfold tailWord_3521025
  simp only [CollatzResearch.WordTrace]
  refine ⟨128422332068935243039732529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85614888045956828693155019 128422332068935243039732529)
  ·
    refine ⟨96316749051701432279799397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128422332068935243039732529 96316749051701432279799397)
    ·
      refine ⟨18059390447194018552462387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96316749051701432279799397 18059390447194018552462387)
      ·
        refine ⟨27089085670791027828693581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18059390447194018552462387 27089085670791027828693581)
        ·
          refine ⟨10158407126546635435760093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27089085670791027828693581 10158407126546635435760093)
          ·
            refine ⟨3809402672454988288410035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10158407126546635435760093 3809402672454988288410035)
            ·
              refine ⟨5714104008682482432615053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3809402672454988288410035 5714104008682482432615053)
              ·
                refine ⟨2142789003255930912230645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5714104008682482432615053 2142789003255930912230645)
                ·
                  refine ⟨200886469055243523021623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2142789003255930912230645 200886469055243523021623)
                  ·
                    rfl

theorem cell23_3521025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 5].length) (baseStart_3521025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521025 prefixEnd_3521025 := by exact prefixLift 3521025
  have htrace : WordTrace (prefixWord ++ tailWord_3521025) baseStart_3521025 baseEnd_3521025 := by
    simpa [prefixWord, tailWord_3521025, baseEnd_3521025] using wordTrace_append hprefix tailTrace_3521025
  have hstable : (prefixWord ++ tailWord_3521025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521025).length < 2 ^ (prefixWord ++ tailWord_3521025).sum := by decide
  have hdescent : baseEnd_3521025 < baseStart_3521025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521038 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 2, 5]
def baseStart_3521038 : Nat := 118140960795 + 3521038 * 2 ^ 59
def prefixEnd_3521038 : Nat := 4983230072969 + 3 ^ 40 * 3521038 * 2
def baseEnd_3521038 : Nat := 602661632248566718777349

theorem tailTrace_3521038 : CollatzResearch.WordTrace tailWord_3521038 prefixEnd_3521038 602661632248566718777349 := by
  unfold tailWord_3521038
  simp only [CollatzResearch.WordTrace]
  refine ⟨16052850777236018282494471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85615204145258764173303845 16052850777236018282494471)
  ·
    refine ⟨24079276165854027423741707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16052850777236018282494471 24079276165854027423741707)
    ·
      refine ⟨36118914248781041135612561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24079276165854027423741707 36118914248781041135612561)
      ·
        refine ⟨27089185686585780851709421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36118914248781041135612561 27089185686585780851709421)
        ·
          refine ⟨10158444632469667819391033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27089185686585780851709421 10158444632469667819391033)
          ·
            refine ⟨7618833474352250864543275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10158444632469667819391033 7618833474352250864543275)
            ·
              refine ⟨11428250211528376296814913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7618833474352250864543275 11428250211528376296814913)
              ·
                refine ⟨8571187658646282222611185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11428250211528376296814913 8571187658646282222611185)
                ·
                  refine ⟨6428390743984711666958389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8571187658646282222611185 6428390743984711666958389)
                  ·
                    refine ⟨602661632248566718777349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6428390743984711666958389 602661632248566718777349)
                    ·
                      rfl

theorem cell23_3521038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_3521038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521038 prefixEnd_3521038 := by exact prefixLift 3521038
  have htrace : WordTrace (prefixWord ++ tailWord_3521038) baseStart_3521038 baseEnd_3521038 := by
    simpa [prefixWord, tailWord_3521038, baseEnd_3521038] using wordTrace_append hprefix tailTrace_3521038
  have hstable : (prefixWord ++ tailWord_3521038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521038).length < 2 ^ (prefixWord ++ tailWord_3521038).sum := by decide
  have hdescent : baseEnd_3521038 < baseStart_3521038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521058 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 1, 6, 2]
def baseStart_3521058 : Nat := 118140960795 + 3521058 * 2 ^ 59
def prefixEnd_3521058 : Nat := 4983230072969 + 3 ^ 40 * 3521058 * 2
def baseEnd_3521058 : Nat := 1807995166358790078081955

theorem tailTrace_3521058 : CollatzResearch.WordTrace tailWord_3521058 prefixEnd_3521058 1807995166358790078081955 := by
  unfold tailWord_3521058
  simp only [CollatzResearch.WordTrace]
  refine ⟨32105883919453922418920957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85615690451877126450455885 32105883919453922418920957)
  ·
    refine ⟨12039706469795220907095359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32105883919453922418920957 12039706469795220907095359)
    ·
      refine ⟨18059559704692831360643039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12039706469795220907095359 18059559704692831360643039)
      ·
        refine ⟨27089339557039247040964559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18059559704692831360643039 27089339557039247040964559)
        ·
          refine ⟨40634009335558870561446839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27089339557039247040964559 40634009335558870561446839)
          ·
            refine ⟨60951014003338305842170259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40634009335558870561446839 60951014003338305842170259)
            ·
              refine ⟨91426521005007458763255389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60951014003338305842170259 91426521005007458763255389)
              ·
                refine ⟨34284945376877797036220771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91426521005007458763255389 34284945376877797036220771)
                ·
                  refine ⟨51427418065316695554331157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34284945376877797036220771 51427418065316695554331157)
                  ·
                    refine ⟨2410660221811720104109273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51427418065316695554331157 2410660221811720104109273)
                    ·
                      refine ⟨1807995166358790078081955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2410660221811720104109273 1807995166358790078081955)
                      ·
                        rfl

theorem cell23_3521058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_3521058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521058 prefixEnd_3521058 := by exact prefixLift 3521058
  have htrace : WordTrace (prefixWord ++ tailWord_3521058) baseStart_3521058 baseEnd_3521058 := by
    simpa [prefixWord, tailWord_3521058, baseEnd_3521058] using wordTrace_append hprefix tailTrace_3521058
  have hstable : (prefixWord ++ tailWord_3521058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521058).length < 2 ^ (prefixWord ++ tailWord_3521058).sum := by decide
  have hdescent : baseEnd_3521058 < baseStart_3521058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521061 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 3, 4, 3]
def baseStart_3521061 : Nat := 118140960795 + 3521061 * 2 ^ 59
def prefixEnd_3521061 : Nat := 4983230072969 + 3 ^ 40 * 3521061 * 2
def baseEnd_3521061 : Nat := 1807996706800753566344441

theorem tailTrace_3521061 : CollatzResearch.WordTrace tailWord_3521061 prefixEnd_3521061 1807996706800753566344441 := by
  unfold tailWord_3521061
  simp only [CollatzResearch.WordTrace]
  refine ⟨128423645096804821188043037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85615763397869880792028691 128423645096804821188043037)
  ·
    refine ⟨48158866911301807945516139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128423645096804821188043037 48158866911301807945516139)
    ·
      refine ⟨72238300366952711918274209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48158866911301807945516139 72238300366952711918274209)
      ·
        refine ⟨54178725275214533938705657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72238300366952711918274209 54178725275214533938705657)
        ·
          refine ⟨40634043956410900454029243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54178725275214533938705657 40634043956410900454029243)
          ·
            refine ⟨60951065934616350681043865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40634043956410900454029243 60951065934616350681043865)
            ·
              refine ⟨45713299450962263010782899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60951065934616350681043865 45713299450962263010782899)
              ·
                refine ⟨68569949176443394516174349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45713299450962263010782899 68569949176443394516174349)
                ·
                  refine ⟨25713730941166272943565381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68569949176443394516174349 25713730941166272943565381)
                  ·
                    refine ⟨4821324551468676176918509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25713730941166272943565381 4821324551468676176918509)
                    ·
                      refine ⟨1807996706800753566344441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4821324551468676176918509 1807996706800753566344441)
                      ·
                        rfl

theorem cell23_3521061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_3521061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521061 prefixEnd_3521061 := by exact prefixLift 3521061
  have htrace : WordTrace (prefixWord ++ tailWord_3521061) baseStart_3521061 baseEnd_3521061 := by
    simpa [prefixWord, tailWord_3521061, baseEnd_3521061] using wordTrace_append hprefix tailTrace_3521061
  have hstable : (prefixWord ++ tailWord_3521061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521061).length < 2 ^ (prefixWord ++ tailWord_3521061).sum := by decide
  have hdescent : baseEnd_3521061 < baseStart_3521061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521098 : List Nat := [3, 1, 2, 1, 1, 5, 2, 2, 6]
def baseStart_3521098 : Nat := 118140960795 + 3521098 * 2 ^ 59
def prefixEnd_3521098 : Nat := 4983230072969 + 3 ^ 40 * 3521098 * 2
def baseEnd_3521098 : Nat := 200890633953885546842419

theorem tailTrace_3521098 : CollatzResearch.WordTrace tailWord_3521098 prefixEnd_3521098 200890633953885546842419 := by
  unfold tailWord_3521098
  simp only [CollatzResearch.WordTrace]
  refine ⟨32106248649417694126784987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85616663065113851004759965 32106248649417694126784987)
  ·
    refine ⟨48159372974126541190177481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32106248649417694126784987 48159372974126541190177481)
    ·
      refine ⟨36119529730594905892633111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48159372974126541190177481 36119529730594905892633111)
      ·
        refine ⟨54179294595892358838949667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36119529730594905892633111 54179294595892358838949667)
        ·
          refine ⟨81268941893838538258424501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54179294595892358838949667 81268941893838538258424501)
          ·
            refine ⟨7618963302547362961727297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81268941893838538258424501 7618963302547362961727297)
            ·
              refine ⟨5714222476910522221295473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7618963302547362961727297 5714222476910522221295473)
              ·
                refine ⟨4285666857682891665971605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5714222476910522221295473 4285666857682891665971605)
                ·
                  refine ⟨200890633953885546842419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4285666857682891665971605 200890633953885546842419)
                  ·
                    rfl

theorem cell23_3521098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 6].length) (baseStart_3521098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521098 prefixEnd_3521098 := by exact prefixLift 3521098
  have htrace : WordTrace (prefixWord ++ tailWord_3521098) baseStart_3521098 baseEnd_3521098 := by
    simpa [prefixWord, tailWord_3521098, baseEnd_3521098] using wordTrace_append hprefix tailTrace_3521098
  have hstable : (prefixWord ++ tailWord_3521098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521098).length < 2 ^ (prefixWord ++ tailWord_3521098).sum := by decide
  have hdescent : baseEnd_3521098 < baseStart_3521098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521102 : List Nat := [4, 1, 1, 1, 1, 2, 6, 2, 1, 4]
def baseStart_3521102 : Nat := 118140960795 + 3521102 * 2 ^ 59
def prefixEnd_3521102 : Nat := 4983230072969 + 3 ^ 40 * 3521102 * 2
def baseEnd_3521102 : Nat := 602672586502529301977251

theorem tailTrace_3521102 : CollatzResearch.WordTrace tailWord_3521102 prefixEnd_3521102 602672586502529301977251 := by
  unfold tailWord_3521102
  simp only [CollatzResearch.WordTrace]
  refine ⟨16053142561207035648785695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85616760326437523460190373 16053142561207035648785695)
  ·
    refine ⟨24079713841810553473178543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16053142561207035648785695 24079713841810553473178543)
    ·
      refine ⟨36119570762715830209767815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24079713841810553473178543 36119570762715830209767815)
      ·
        refine ⟨54179356144073745314651723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36119570762715830209767815 54179356144073745314651723)
        ·
          refine ⟨81269034216110617971977585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54179356144073745314651723 81269034216110617971977585)
          ·
            refine ⟨60951775662082963478983189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81269034216110617971977585 60951775662082963478983189)
            ·
              refine ⟨2857114484160138913077337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60951775662082963478983189 2857114484160138913077337)
              ·
                refine ⟨2142835863120104184808003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2857114484160138913077337 2142835863120104184808003)
                ·
                  refine ⟨3214253794680156277212005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142835863120104184808003 3214253794680156277212005)
                  ·
                    refine ⟨602672586502529301977251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3214253794680156277212005 602672586502529301977251)
                    ·
                      rfl

theorem cell23_3521102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_3521102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521102 prefixEnd_3521102 := by exact prefixLift 3521102
  have htrace : WordTrace (prefixWord ++ tailWord_3521102) baseStart_3521102 baseEnd_3521102 := by
    simpa [prefixWord, tailWord_3521102, baseEnd_3521102] using wordTrace_append hprefix tailTrace_3521102
  have hstable : (prefixWord ++ tailWord_3521102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521102).length < 2 ^ (prefixWord ++ tailWord_3521102).sum := by decide
  have hdescent : baseEnd_3521102 < baseStart_3521102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521111 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 5, 5]
def baseStart_3521111 : Nat := 118140960795 + 3521111 * 2 ^ 59
def prefixEnd_3521111 : Nat := 4983230072969 + 3 ^ 40 * 3521111 * 2
def baseEnd_3521111 : Nat := 602674126944492790239737

theorem tailTrace_3521111 : CollatzResearch.WordTrace tailWord_3521111 prefixEnd_3521111 602674126944492790239737 := by
  unfold tailWord_3521111
  simp only [CollatzResearch.WordTrace]
  refine ⟨128425468746623679727363187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85616979164415786484908791 128425468746623679727363187)
  ·
    refine ⟨192638203119935519591044781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128425468746623679727363187 192638203119935519591044781)
    ·
      refine ⟨72239326169975819846641793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192638203119935519591044781 72239326169975819846641793)
      ·
        refine ⟨54179494627481864884981345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72239326169975819846641793 54179494627481864884981345)
        ·
          refine ⟨40634620970611398663736009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54179494627481864884981345 40634620970611398663736009)
          ·
            refine ⟨30475965727958548997802007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40634620970611398663736009 30475965727958548997802007)
            ·
              refine ⟨45713948591937823496703011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30475965727958548997802007 45713948591937823496703011)
              ·
                refine ⟨68570922887906735245054517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45713948591937823496703011 68570922887906735245054517)
                ·
                  refine ⟨6428524020741256429223861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68570922887906735245054517 6428524020741256429223861)
                  ·
                    refine ⟨602674126944492790239737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6428524020741256429223861 602674126944492790239737)
                    ·
                      rfl

theorem cell23_3521111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_3521111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521111 prefixEnd_3521111 := by exact prefixLift 3521111
  have htrace : WordTrace (prefixWord ++ tailWord_3521111) baseStart_3521111 baseEnd_3521111 := by
    simpa [prefixWord, tailWord_3521111, baseEnd_3521111] using wordTrace_append hprefix tailTrace_3521111
  have hstable : (prefixWord ++ tailWord_3521111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521111).length < 2 ^ (prefixWord ++ tailWord_3521111).sum := by decide
  have hdescent : baseEnd_3521111 < baseStart_3521111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521135 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 2, 3, 2]
def baseStart_3521135 : Nat := 118140960795 + 3521135 * 2 ^ 59
def prefixEnd_3521135 : Nat := 4983230072969 + 3 ^ 40 * 3521135 * 2
def baseEnd_3521135 : Nat := 1808034704369186276819101

theorem tailTrace_3521135 : CollatzResearch.WordTrace tailWord_3521135 prefixEnd_3521135 1808034704369186276819101 := by
  unfold tailWord_3521135
  simp only [CollatzResearch.WordTrace]
  refine ⟨128426344098536731826236859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85617562732357821217491239 128426344098536731826236859)
  ·
    refine ⟨192639516147805097739355289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128426344098536731826236859 192639516147805097739355289)
    ·
      refine ⟨144479637110853823304516467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192639516147805097739355289 144479637110853823304516467)
      ·
        refine ⟨216719455666280734956774701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144479637110853823304516467 216719455666280734956774701)
        ·
          refine ⟨81269795874855275608790513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216719455666280734956774701 81269795874855275608790513)
          ·
            refine ⟨60952346906141456706592885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81269795874855275608790513 60952346906141456706592885)
            ·
              refine ⟨5714282522450761566243083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60952346906141456706592885 5714282522450761566243083)
              ·
                refine ⟨8571423783676142349364625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5714282522450761566243083 8571423783676142349364625)
                ·
                  refine ⟨6428567837757106762023469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8571423783676142349364625 6428567837757106762023469)
                  ·
                    refine ⟨2410712939158915035758801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6428567837757106762023469 2410712939158915035758801)
                    ·
                      refine ⟨1808034704369186276819101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2410712939158915035758801 1808034704369186276819101)
                      ·
                        rfl

theorem cell23_3521135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 3, 2].length) (baseStart_3521135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521135 prefixEnd_3521135 := by exact prefixLift 3521135
  have htrace : WordTrace (prefixWord ++ tailWord_3521135) baseStart_3521135 baseEnd_3521135 := by
    simpa [prefixWord, tailWord_3521135, baseEnd_3521135] using wordTrace_append hprefix tailTrace_3521135
  have hstable : (prefixWord ++ tailWord_3521135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521135).length < 2 ^ (prefixWord ++ tailWord_3521135).sum := by decide
  have hdescent : baseEnd_3521135 < baseStart_3521135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521145 : List Nat := [1, 2, 1, 3, 3, 2, 4, 1, 1, 5]
def baseStart_3521145 : Nat := 118140960795 + 3521145 * 2 ^ 59
def prefixEnd_3521145 : Nat := 4983230072969 + 3 ^ 40 * 3521145 * 2
def baseEnd_3521145 : Nat := 602679946391910412564685

theorem tailTrace_3521145 : CollatzResearch.WordTrace tailWord_3521145 prefixEnd_3521145 602679946391910412564685 := by
  unfold tailWord_3521145
  simp only [CollatzResearch.WordTrace]
  refine ⟨128426708828500503534100889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85617805885667002356067259 128426708828500503534100889)
  ·
    refine ⟨96320031621375377650575667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128426708828500503534100889 96320031621375377650575667)
    ·
      refine ⟨144480047432063066475863501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96320031621375377650575667 144480047432063066475863501)
      ·
        refine ⟨54180017787023649928448813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144480047432063066475863501 54180017787023649928448813)
        ·
          refine ⟨20317506670133868723168305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54180017787023649928448813 20317506670133868723168305)
          ·
            refine ⟨15238130002600401542376229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20317506670133868723168305 15238130002600401542376229)
            ·
              refine ⟨2857149375487575289195543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15238130002600401542376229 2857149375487575289195543)
              ·
                refine ⟨4285724063231362933793315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2857149375487575289195543 4285724063231362933793315)
                ·
                  refine ⟨6428586094847044400689973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4285724063231362933793315 6428586094847044400689973)
                  ·
                    refine ⟨602679946391910412564685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6428586094847044400689973 602679946391910412564685)
                    ·
                      rfl

theorem cell23_3521145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 1, 5].length) (baseStart_3521145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521145 prefixEnd_3521145 := by exact prefixLift 3521145
  have htrace : WordTrace (prefixWord ++ tailWord_3521145) baseStart_3521145 baseEnd_3521145 := by
    simpa [prefixWord, tailWord_3521145, baseEnd_3521145] using wordTrace_append hprefix tailTrace_3521145
  have hstable : (prefixWord ++ tailWord_3521145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521145).length < 2 ^ (prefixWord ++ tailWord_3521145).sum := by decide
  have hdescent : baseEnd_3521145 < baseStart_3521145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521161 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 1, 1, 6]
def baseStart_3521161 : Nat := 118140960795 + 3521161 * 2 ^ 59
def prefixEnd_3521161 : Nat := 4983230072969 + 3 ^ 40 * 3521161 * 2
def baseEnd_3521161 : Nat := 1808048054866203175093981

theorem tailTrace_3521161 : CollatzResearch.WordTrace tailWord_3521161 prefixEnd_3521161 1808048054866203175093981 := by
  unfold tailWord_3521161
  simp only [CollatzResearch.WordTrace]
  refine ⟨128427292396442538266683337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85618194930961692177788891 128427292396442538266683337)
  ·
    refine ⟨96320469297331903700012503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128427292396442538266683337 96320469297331903700012503)
    ·
      refine ⟨144480703945997855550018755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96320469297331903700012503 144480703945997855550018755)
      ·
        refine ⟨216721055918996783325028133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144480703945997855550018755 216721055918996783325028133)
        ·
          refine ⟨40635197984811896873442775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216721055918996783325028133 40635197984811896873442775)
          ·
            refine ⟨60952796977217845310164163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40635197984811896873442775 60952796977217845310164163)
            ·
              refine ⟨91429195465826767965246245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60952796977217845310164163 91429195465826767965246245)
              ·
                refine ⟨17142974149842518993483671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91429195465826767965246245 17142974149842518993483671)
                ·
                  refine ⟨25714461224763778490225507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17142974149842518993483671 25714461224763778490225507)
                  ·
                    refine ⟨38571691837145667735338261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25714461224763778490225507 38571691837145667735338261)
                    ·
                      refine ⟨1808048054866203175093981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38571691837145667735338261 1808048054866203175093981)
                      ·
                        rfl

theorem cell23_3521161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_3521161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521161 prefixEnd_3521161 := by exact prefixLift 3521161
  have htrace : WordTrace (prefixWord ++ tailWord_3521161) baseStart_3521161 baseEnd_3521161 := by
    simpa [prefixWord, tailWord_3521161, baseEnd_3521161] using wordTrace_append hprefix tailTrace_3521161
  have hstable : (prefixWord ++ tailWord_3521161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521161).length < 2 ^ (prefixWord ++ tailWord_3521161).sum := by decide
  have hdescent : baseEnd_3521161 < baseStart_3521161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521182 : List Nat := [4, 3, 1, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_3521182 : Nat := 118140960795 + 3521182 * 2 ^ 59
def prefixEnd_3521182 : Nat := 4983230072969 + 3 ^ 40 * 3521182 * 2
def baseEnd_3521182 : Nat := 1808058837959947592931385

theorem tailTrace_3521182 : CollatzResearch.WordTrace tailWord_3521182 prefixEnd_3521182 1808058837959947592931385 := by
  unfold tailWord_3521182
  simp only [CollatzResearch.WordTrace]
  refine ⟨16053507291170807356649725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85618705552910972568798533 16053507291170807356649725)
  ·
    refine ⟨6020065234189052758743647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16053507291170807356649725 6020065234189052758743647)
    ·
      refine ⟨9030097851283579138115471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6020065234189052758743647 9030097851283579138115471)
      ·
        refine ⟨13545146776925368707173207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9030097851283579138115471 13545146776925368707173207)
        ·
          refine ⟨20317720165388053060759811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13545146776925368707173207 20317720165388053060759811)
          ·
            refine ⟨30476580248082079591139717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20317720165388053060759811 30476580248082079591139717)
            ·
              refine ⟨5714358796515389923338697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30476580248082079591139717 5714358796515389923338697)
              ·
                refine ⟨4285769097386542442504023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5714358796515389923338697 4285769097386542442504023)
                ·
                  refine ⟨6428653646079813663756035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4285769097386542442504023 6428653646079813663756035)
                  ·
                    refine ⟨9642980469119720495634053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6428653646079813663756035 9642980469119720495634053)
                    ·
                      refine ⟨1808058837959947592931385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9642980469119720495634053 1808058837959947592931385)
                      ·
                        rfl

theorem cell23_3521182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_3521182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521182 prefixEnd_3521182 := by exact prefixLift 3521182
  have htrace : WordTrace (prefixWord ++ tailWord_3521182) baseStart_3521182 baseEnd_3521182 := by
    simpa [prefixWord, tailWord_3521182, baseEnd_3521182] using wordTrace_append hprefix tailTrace_3521182
  have hstable : (prefixWord ++ tailWord_3521182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521182).length < 2 ^ (prefixWord ++ tailWord_3521182).sum := by decide
  have hdescent : baseEnd_3521182 < baseStart_3521182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521199 : List Nat := [1, 1, 2, 1, 2, 5, 3, 3, 1, 2, 2]
def baseStart_3521199 : Nat := 118140960795 + 3521199 * 2 ^ 59
def prefixEnd_3521199 : Nat := 4983230072969 + 3 ^ 40 * 3521199 * 2
def baseEnd_3521199 : Nat := 1808067567131074026418807

theorem tailTrace_3521199 : CollatzResearch.WordTrace tailWord_3521199 prefixEnd_3521199 1808067567131074026418807 := by
  unfold tailWord_3521199
  simp only [CollatzResearch.WordTrace]
  refine ⟨128428678370304870756566651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85619118913536580504377767 128428678370304870756566651)
  ·
    refine ⟨192643017555457306134849977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128428678370304870756566651 192643017555457306134849977)
    ·
      refine ⟨144482263166592979601137483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192643017555457306134849977 144482263166592979601137483)
      ·
        refine ⟨216723394749889469401706225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144482263166592979601137483 216723394749889469401706225)
        ·
          refine ⟨162542546062417102051279669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216723394749889469401706225 162542546062417102051279669)
          ·
            refine ⟨15238363693351603317307469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162542546062417102051279669 15238363693351603317307469)
            ·
              refine ⟨5714386385006851243990301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15238363693351603317307469 5714386385006851243990301)
              ·
                refine ⟨2142894894377569216496363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5714386385006851243990301 2142894894377569216496363)
                ·
                  refine ⟨3214342341566353824744545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142894894377569216496363 3214342341566353824744545)
                  ·
                    refine ⟨2410756756174765368558409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3214342341566353824744545 2410756756174765368558409)
                    ·
                      refine ⟨1808067567131074026418807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2410756756174765368558409 1808067567131074026418807)
                      ·
                        rfl

theorem cell23_3521199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 1, 2, 2].length) (baseStart_3521199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521199 prefixEnd_3521199 := by exact prefixLift 3521199
  have htrace : WordTrace (prefixWord ++ tailWord_3521199) baseStart_3521199 baseEnd_3521199 := by
    simpa [prefixWord, tailWord_3521199, baseEnd_3521199] using wordTrace_append hprefix tailTrace_3521199
  have hstable : (prefixWord ++ tailWord_3521199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521199).length < 2 ^ (prefixWord ++ tailWord_3521199).sum := by decide
  have hdescent : baseEnd_3521199 < baseStart_3521199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521215 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 4, 1, 3]
def baseStart_3521215 : Nat := 118140960795 + 3521215 * 2 ^ 59
def prefixEnd_3521215 : Nat := 4983230072969 + 3 ^ 40 * 3521215 * 2
def baseEnd_3521215 : Nat := 1808075782821545963818733

theorem tailTrace_3521215 : CollatzResearch.WordTrace tailWord_3521215 prefixEnd_3521215 1808075782821545963818733 := by
  unfold tailWord_3521215
  simp only [CollatzResearch.WordTrace]
  refine ⟨128429261938246905489149099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85619507958831270326099399 128429261938246905489149099)
  ·
    refine ⟨192643892907370358233723649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128429261938246905489149099 192643892907370358233723649)
    ·
      refine ⟨144482919680527768675292737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192643892907370358233723649 144482919680527768675292737)
      ·
        refine ⟨108362189760395826506469553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144482919680527768675292737 108362189760395826506469553)
        ·
          refine ⟨81271642320296869879852165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108362189760395826506469553 81271642320296869879852165)
          ·
            refine ⟨15238432935055663102472281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81271642320296869879852165 15238432935055663102472281)
            ·
              refine ⟨11428824701291747326854211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15238432935055663102472281 11428824701291747326854211)
              ·
                refine ⟨17143237051937620990281317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11428824701291747326854211 17143237051937620990281317)
                ·
                  refine ⟨3214356947238303935677747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17143237051937620990281317 3214356947238303935677747)
                  ·
                    refine ⟨4821535420857455903516621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3214356947238303935677747 4821535420857455903516621)
                    ·
                      refine ⟨1808075782821545963818733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4821535420857455903516621 1808075782821545963818733)
                      ·
                        rfl

theorem cell23_3521215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 1, 3].length) (baseStart_3521215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521215 prefixEnd_3521215 := by exact prefixLift 3521215
  have htrace : WordTrace (prefixWord ++ tailWord_3521215) baseStart_3521215 baseEnd_3521215 := by
    simpa [prefixWord, tailWord_3521215, baseEnd_3521215] using wordTrace_append hprefix tailTrace_3521215
  have hstable : (prefixWord ++ tailWord_3521215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521215).length < 2 ^ (prefixWord ++ tailWord_3521215).sum := by decide
  have hdescent : baseEnd_3521215 < baseStart_3521215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521216 : List Nat := [2, 1, 1, 2, 4, 3, 3, 2, 1, 2, 2]
def baseStart_3521216 : Nat := 118140960795 + 3521216 * 2 ^ 59
def prefixEnd_3521216 : Nat := 4983230072969 + 3 ^ 40 * 3521216 * 2
def baseEnd_3521216 : Nat := 1808076296302200459906229

theorem tailTrace_3521216 : CollatzResearch.WordTrace tailWord_3521216 prefixEnd_3521216 1808076296302200459906229 := by
  unfold tailWord_3521216
  simp only [CollatzResearch.WordTrace]
  refine ⟨64214649205621641329967751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85619532274162188439957001 64214649205621641329967751)
  ·
    refine ⟨96321973808432461994951627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64214649205621641329967751 96321973808432461994951627)
    ·
      refine ⟨144482960712648692992427441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96321973808432461994951627 144482960712648692992427441)
      ·
        refine ⟨108362220534486519744320581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144482960712648692992427441 108362220534486519744320581)
        ·
          refine ⟨20317916350216222452060109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108362220534486519744320581 20317916350216222452060109)
          ·
            refine ⟨7619218631331083419522541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20317916350216222452060109 7619218631331083419522541)
            ·
              refine ⟨2857206986749156282320953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7619218631331083419522541 2857206986749156282320953)
              ·
                refine ⟨2142905240061867211740715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2857206986749156282320953 2142905240061867211740715)
                ·
                  refine ⟨3214357860092800817611073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142905240061867211740715 3214357860092800817611073)
                  ·
                    refine ⟨2410768395069600613208305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3214357860092800817611073 2410768395069600613208305)
                    ·
                      refine ⟨1808076296302200459906229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2410768395069600613208305 1808076296302200459906229)
                      ·
                        rfl

theorem cell23_3521216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 1, 2, 2].length) (baseStart_3521216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521216 prefixEnd_3521216 := by exact prefixLift 3521216
  have htrace : WordTrace (prefixWord ++ tailWord_3521216) baseStart_3521216 baseEnd_3521216 := by
    simpa [prefixWord, tailWord_3521216, baseEnd_3521216] using wordTrace_append hprefix tailTrace_3521216
  have hstable : (prefixWord ++ tailWord_3521216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521216).length < 2 ^ (prefixWord ++ tailWord_3521216).sum := by decide
  have hdescent : baseEnd_3521216 < baseStart_3521216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521236 : List Nat := [2, 4, 1, 3, 3, 1, 1, 2, 1, 2, 3]
def baseStart_3521236 : Nat := 118140960795 + 3521236 * 2 ^ 59
def prefixEnd_3521236 : Nat := 4983230072969 + 3 ^ 40 * 3521236 * 2
def baseEnd_3521236 : Nat := 1808086565915290381656137

theorem tailTrace_3521236 : CollatzResearch.WordTrace tailWord_3521236 prefixEnd_3521236 1808086565915290381656137 := by
  unfold tailWord_3521236
  simp only [CollatzResearch.WordTrace]
  refine ⟨64215013935585413037831781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85620018580780550717109041 64215013935585413037831781)
  ·
    refine ⟨12040315112922264944593459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64215013935585413037831781 12040315112922264944593459)
    ·
      refine ⟨18060472669383397416890189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12040315112922264944593459 18060472669383397416890189)
      ·
        refine ⟨6772677251018774031333821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18060472669383397416890189 6772677251018774031333821)
        ·
          refine ⟨2539753969132040261750183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6772677251018774031333821 2539753969132040261750183)
          ·
            refine ⟨3809630953698060392625275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539753969132040261750183 3809630953698060392625275)
            ·
              refine ⟨5714446430547090588937913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3809630953698060392625275 5714446430547090588937913)
              ·
                refine ⟨4285834822910317941703435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5714446430547090588937913 4285834822910317941703435)
                ·
                  refine ⟨6428752234365476912555153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4285834822910317941703435 6428752234365476912555153)
                  ·
                    refine ⟨4821564175774107684416365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6428752234365476912555153 4821564175774107684416365)
                    ·
                      refine ⟨1808086565915290381656137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4821564175774107684416365 1808086565915290381656137)
                      ·
                        rfl

theorem cell23_3521236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_3521236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521236 prefixEnd_3521236 := by exact prefixLift 3521236
  have htrace : WordTrace (prefixWord ++ tailWord_3521236) baseStart_3521236 baseEnd_3521236 := by
    simpa [prefixWord, tailWord_3521236, baseEnd_3521236] using wordTrace_append hprefix tailTrace_3521236
  have hstable : (prefixWord ++ tailWord_3521236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521236).length < 2 ^ (prefixWord ++ tailWord_3521236).sum := by decide
  have hdescent : baseEnd_3521236 < baseStart_3521236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521312 : List Nat := [2, 1, 1, 5, 1, 3, 2, 3, 5]
def baseStart_3521312 : Nat := 118140960795 + 3521312 * 2 ^ 59
def prefixEnd_3521312 : Nat := 4983230072969 + 3 ^ 40 * 3521312 * 2
def baseEnd_3521312 : Nat := 200902843382781342700643

theorem tailTrace_3521312 : CollatzResearch.WordTrace tailWord_3521312 prefixEnd_3521312 200902843382781342700643 := by
  unfold tailWord_3521312
  simp only [CollatzResearch.WordTrace]
  refine ⟨64216399909447745527715095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85621866545930327370286793 64216399909447745527715095)
  ·
    refine ⟨96324599864171618291572643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64216399909447745527715095 96324599864171618291572643)
    ·
      refine ⟨144486899796257427437358965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96324599864171618291572643 144486899796257427437358965)
      ·
        refine ⟨13545646855899133822252403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144486899796257427437358965 13545646855899133822252403)
        ·
          refine ⟨20318470283848700733378605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13545646855899133822252403 20318470283848700733378605)
          ·
            refine ⟨7619426356443262775016977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20318470283848700733378605 7619426356443262775016977)
            ·
              refine ⟨5714569767332447081262733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7619426356443262775016977 5714569767332447081262733)
              ·
                refine ⟨2142963662749667655473525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5714569767332447081262733 2142963662749667655473525)
                ·
                  refine ⟨200902843382781342700643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2142963662749667655473525 200902843382781342700643)
                  ·
                    rfl

theorem cell23_3521312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 5].length) (baseStart_3521312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521312 prefixEnd_3521312 := by exact prefixLift 3521312
  have htrace : WordTrace (prefixWord ++ tailWord_3521312) baseStart_3521312 baseEnd_3521312 := by
    simpa [prefixWord, tailWord_3521312, baseEnd_3521312] using wordTrace_append hprefix tailTrace_3521312
  have hstable : (prefixWord ++ tailWord_3521312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521312).length < 2 ^ (prefixWord ++ tailWord_3521312).sum := by decide
  have hdescent : baseEnd_3521312 < baseStart_3521312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521365 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 1, 4, 3]
def baseStart_3521365 : Nat := 118140960795 + 3521365 * 2 ^ 59
def prefixEnd_3521365 : Nat := 4983230072969 + 3 ^ 40 * 3521365 * 2
def baseEnd_3521365 : Nat := 1808152804919720376943043

theorem tailTrace_3521365 : CollatzResearch.WordTrace tailWord_3521365 prefixEnd_3521365 1808152804919720376943043 := by
  unfold tailWord_3521365
  simp only [CollatzResearch.WordTrace]
  refine ⟨128434732887703481107109549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85623155258468987404739699 128434732887703481107109549)
  ·
    refine ⟨48163024832888805415166081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128434732887703481107109549 48163024832888805415166081)
    ·
      refine ⟨36122268624666604061374561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48163024832888805415166081 36122268624666604061374561)
      ·
        refine ⟨27091701468499953046030921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36122268624666604061374561 27091701468499953046030921)
        ·
          refine ⟨20318776101374964784523191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27091701468499953046030921 20318776101374964784523191)
          ·
            refine ⟨30478164152062447176784787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20318776101374964784523191 30478164152062447176784787)
            ·
              refine ⟨45717246228093670765177181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30478164152062447176784787 45717246228093670765177181)
              ·
                refine ⟨17143967335535126536941443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45717246228093670765177181 17143967335535126536941443)
                ·
                  refine ⟨25715951003302689805412165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17143967335535126536941443 25715951003302689805412165)
                  ·
                    refine ⟨4821740813119254338514781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25715951003302689805412165 4821740813119254338514781)
                    ·
                      refine ⟨1808152804919720376943043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4821740813119254338514781 1808152804919720376943043)
                      ·
                        rfl

theorem cell23_3521365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_3521365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521365 prefixEnd_3521365 := by exact prefixLift 3521365
  have htrace : WordTrace (prefixWord ++ tailWord_3521365) baseStart_3521365 baseEnd_3521365 := by
    simpa [prefixWord, tailWord_3521365, baseEnd_3521365] using wordTrace_append hprefix tailTrace_3521365
  have hstable : (prefixWord ++ tailWord_3521365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521365).length < 2 ^ (prefixWord ++ tailWord_3521365).sum := by decide
  have hdescent : baseEnd_3521365 < baseStart_3521365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521408 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 7]
def baseStart_3521408 : Nat := 118140960795 + 3521408 * 2 ^ 59
def prefixEnd_3521408 : Nat := 4983230072969 + 3 ^ 40 * 3521408 * 2
def baseEnd_3521408 : Nat := 1808174884587863708705345

theorem tailTrace_3521408 : CollatzResearch.WordTrace tailWord_3521408 prefixEnd_3521408 1808174884587863708705345 := by
  unfold tailWord_3521408
  simp only [CollatzResearch.WordTrace]
  refine ⟨64218150613273849725462439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85624200817698466300616585 64218150613273849725462439)
  ·
    refine ⟨96327225919910774588193659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64218150613273849725462439 96327225919910774588193659)
    ·
      refine ⟨144490838879866161882290489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96327225919910774588193659 144490838879866161882290489)
      ·
        refine ⟨108368129159899621411717867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144490838879866161882290489 108368129159899621411717867)
        ·
          refine ⟨162552193739849432117576801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108368129159899621411717867 162552193739849432117576801)
          ·
            refine ⟨121914145304887074088182601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162552193739849432117576801 121914145304887074088182601)
            ·
              refine ⟨91435608978665305566136951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121914145304887074088182601 91435608978665305566136951)
              ·
                refine ⟨137153413467997958349205427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91435608978665305566136951 137153413467997958349205427)
                ·
                  refine ⟨205730120201996937523808141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137153413467997958349205427 205730120201996937523808141)
                  ·
                    refine ⟨77148795075748851571428053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 205730120201996937523808141 77148795075748851571428053)
                    ·
                      refine ⟨1808174884587863708705345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77148795075748851571428053 1808174884587863708705345)
                      ·
                        rfl

theorem cell23_3521408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_3521408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521408 prefixEnd_3521408 := by exact prefixLift 3521408
  have htrace : WordTrace (prefixWord ++ tailWord_3521408) baseStart_3521408 baseEnd_3521408 := by
    simpa [prefixWord, tailWord_3521408, baseEnd_3521408] using wordTrace_append hprefix tailTrace_3521408
  have hstable : (prefixWord ++ tailWord_3521408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521408).length < 2 ^ (prefixWord ++ tailWord_3521408).sum := by decide
  have hdescent : baseEnd_3521408 < baseStart_3521408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521412 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_3521412 : Nat := 118140960795 + 3521412 * 2 ^ 59
def prefixEnd_3521412 : Nat := 4983230072969 + 3 ^ 40 * 3521412 * 2
def baseEnd_3521412 : Nat := 1808176938510481693055327

theorem tailTrace_3521412 : CollatzResearch.WordTrace tailWord_3521412 prefixEnd_3521412 1808176938510481693055327 := by
  unfold tailWord_3521412
  simp only [CollatzResearch.WordTrace]
  refine ⟨64218223559266604067035245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85624298079022138756046993 64218223559266604067035245)
  ·
    refine ⟨24081833834724976525138217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64218223559266604067035245 24081833834724976525138217)
    ·
      refine ⟨18061375376043732393853663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24081833834724976525138217 18061375376043732393853663)
      ·
        refine ⟨27092063064065598590780495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18061375376043732393853663 27092063064065598590780495)
        ·
          refine ⟨40638094596098397886170743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27092063064065598590780495 40638094596098397886170743)
          ·
            refine ⟨60957141894147596829256115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40638094596098397886170743 60957141894147596829256115)
            ·
              refine ⟨91435712841221395243884173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60957141894147596829256115 91435712841221395243884173)
              ·
                refine ⟨34288392315458023216456565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91435712841221395243884173 34288392315458023216456565)
                ·
                  refine ⟨3214536779574189676542803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34288392315458023216456565 3214536779574189676542803)
                  ·
                    refine ⟨4821805169361284514814205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3214536779574189676542803 4821805169361284514814205)
                    ·
                      refine ⟨1808176938510481693055327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4821805169361284514814205 1808176938510481693055327)
                      ·
                        rfl

theorem cell23_3521412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_3521412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521412 prefixEnd_3521412 := by exact prefixLift 3521412
  have htrace : WordTrace (prefixWord ++ tailWord_3521412) baseStart_3521412 baseEnd_3521412 := by
    simpa [prefixWord, tailWord_3521412, baseEnd_3521412] using wordTrace_append hprefix tailTrace_3521412
  have hstable : (prefixWord ++ tailWord_3521412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521412).length < 2 ^ (prefixWord ++ tailWord_3521412).sum := by decide
  have hdescent : baseEnd_3521412 < baseStart_3521412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521439 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 2, 3, 2]
def baseStart_3521439 : Nat := 118140960795 + 3521439 * 2 ^ 59
def prefixEnd_3521439 : Nat := 4983230072969 + 3 ^ 40 * 3521439 * 2
def baseEnd_3521439 : Nat := 1808190802488153087417703

theorem tailTrace_3521439 : CollatzResearch.WordTrace tailWord_3521439 prefixEnd_3521439 1808190802488153087417703 := by
  unfold tailWord_3521439
  simp only [CollatzResearch.WordTrace]
  refine ⟨128437431889435391745303371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85624954592956927830202247 128437431889435391745303371)
  ·
    refine ⟨192656147834153087617955057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128437431889435391745303371 192656147834153087617955057)
    ·
      refine ⟨144492110875614815713466293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192656147834153087617955057 144492110875614815713466293)
      ·
        refine ⟨13546135394588888973137465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144492110875614815713466293 13546135394588888973137465)
        ·
          refine ⟨10159601545941666729853099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13546135394588888973137465 10159601545941666729853099)
          ·
            refine ⟨15239402318912500094779649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10159601545941666729853099 15239402318912500094779649)
            ·
              refine ⟨11429551739184375071084737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15239402318912500094779649 11429551739184375071084737)
              ·
                refine ⟨8572163804388281303313553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11429551739184375071084737 8572163804388281303313553)
                ·
                  refine ⟨6429122853291210977485165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8572163804388281303313553 6429122853291210977485165)
                  ·
                    refine ⟨2410921069984204116556937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6429122853291210977485165 2410921069984204116556937)
                    ·
                      refine ⟨1808190802488153087417703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2410921069984204116556937 1808190802488153087417703)
                      ·
                        rfl

theorem cell23_3521439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_3521439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521439 prefixEnd_3521439 := by exact prefixLift 3521439
  have htrace : WordTrace (prefixWord ++ tailWord_3521439) baseStart_3521439 baseEnd_3521439 := by
    simpa [prefixWord, tailWord_3521439, baseEnd_3521439] using wordTrace_append hprefix tailTrace_3521439
  have hstable : (prefixWord ++ tailWord_3521439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521439).length < 2 ^ (prefixWord ++ tailWord_3521439).sum := by decide
  have hdescent : baseEnd_3521439 < baseStart_3521439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521472 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 3]
def baseStart_3521472 : Nat := 118140960795 + 3521472 * 2 ^ 59
def prefixEnd_3521472 : Nat := 4983230072969 + 3 ^ 40 * 3521472 * 2
def baseEnd_3521472 : Nat := 1808207747349751458305051

theorem tailTrace_3521472 : CollatzResearch.WordTrace tailWord_3521472 prefixEnd_3521472 1808207747349751458305051 := by
  unfold tailWord_3521472
  simp only [CollatzResearch.WordTrace]
  refine ⟨64219317749157919190627335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85625756998877225587503113 64219317749157919190627335)
  ·
    refine ⟨96328976623736878785941003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64219317749157919190627335 96328976623736878785941003)
    ·
      refine ⟨144493464935605318178911505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96328976623736878785941003 144493464935605318178911505)
      ·
        refine ⟨108370098701703988634183629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144493464935605318178911505 108370098701703988634183629)
        ·
          refine ⟨40638787013138995737818861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108370098701703988634183629 40638787013138995737818861)
          ·
            refine ⟨15239545129927123401682073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40638787013138995737818861 15239545129927123401682073)
            ·
              refine ⟨11429658847445342551261555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15239545129927123401682073 11429658847445342551261555)
              ·
                refine ⟨17144488271168013826892333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11429658847445342551261555 17144488271168013826892333)
                ·
                  refine ⟨6429183101688005185084625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17144488271168013826892333 6429183101688005185084625)
                  ·
                    refine ⟨4821887326266003888813469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6429183101688005185084625 4821887326266003888813469)
                    ·
                      refine ⟨1808207747349751458305051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4821887326266003888813469 1808207747349751458305051)
                      ·
                        rfl

theorem cell23_3521472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_3521472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521472 prefixEnd_3521472 := by exact prefixLift 3521472
  have htrace : WordTrace (prefixWord ++ tailWord_3521472) baseStart_3521472 baseEnd_3521472 := by
    simpa [prefixWord, tailWord_3521472, baseEnd_3521472] using wordTrace_append hprefix tailTrace_3521472
  have hstable : (prefixWord ++ tailWord_3521472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521472).length < 2 ^ (prefixWord ++ tailWord_3521472).sum := by decide
  have hdescent : baseEnd_3521472 < baseStart_3521472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521486 : List Nat := [4, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4]
def baseStart_3521486 : Nat := 118140960795 + 3521486 * 2 ^ 59
def prefixEnd_3521486 : Nat := 4983230072969 + 3 ^ 40 * 3521486 * 2
def baseEnd_3521486 : Nat := 1808214936078914403529987

theorem tailTrace_3521486 : CollatzResearch.WordTrace tailWord_3521486 prefixEnd_3521486 1808214936078914403529987 := by
  unfold tailWord_3521486
  simp only [CollatzResearch.WordTrace]
  refine ⟨16054893265033139846533039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85626097413510079181509541 16054893265033139846533039)
  ·
    refine ⟨24082339897549709769799559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16054893265033139846533039 24082339897549709769799559)
    ·
      refine ⟨36123509846324564654699339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24082339897549709769799559 36123509846324564654699339)
      ·
        refine ⟨54185264769486846982049009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36123509846324564654699339 54185264769486846982049009)
        ·
          refine ⟨40638948577115135236536757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54185264769486846982049009 40638948577115135236536757)
          ·
            refine ⟨3809901429104543928425321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40638948577115135236536757 3809901429104543928425321)
            ·
              refine ⟨2857426071828407946318991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3809901429104543928425321 2857426071828407946318991)
              ·
                refine ⟨4286139107742611919478487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2857426071828407946318991 4286139107742611919478487)
                ·
                  refine ⟨6429208661613917879217731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4286139107742611919478487 6429208661613917879217731)
                  ·
                    refine ⟨9643812992420876818826597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6429208661613917879217731 9643812992420876818826597)
                    ·
                      refine ⟨1808214936078914403529987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9643812992420876818826597 1808214936078914403529987)
                      ·
                        rfl

theorem cell23_3521486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_3521486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521486 prefixEnd_3521486 := by exact prefixLift 3521486
  have htrace : WordTrace (prefixWord ++ tailWord_3521486) baseStart_3521486 baseEnd_3521486 := by
    simpa [prefixWord, tailWord_3521486, baseEnd_3521486] using wordTrace_append hprefix tailTrace_3521486
  have hstable : (prefixWord ++ tailWord_3521486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521486).length < 2 ^ (prefixWord ++ tailWord_3521486).sum := by decide
  have hdescent : baseEnd_3521486 < baseStart_3521486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521519 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 1, 3, 3]
def baseStart_3521519 : Nat := 118140960795 + 3521519 * 2 ^ 59
def prefixEnd_3521519 : Nat := 4983230072969 + 3 ^ 40 * 3521519 * 2
def baseEnd_3521519 : Nat := 1808231880940512774417335

theorem tailTrace_3521519 : CollatzResearch.WordTrace tailWord_3521519 prefixEnd_3521519 1808231880940512774417335 := by
  unfold tailWord_3521519
  simp only [CollatzResearch.WordTrace]
  refine ⟨128440349729145565408215611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85626899819430376938810407 128440349729145565408215611)
  ·
    refine ⟨192660524593718348112323417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128440349729145565408215611 192660524593718348112323417)
    ·
      refine ⟨144495393445288761084242563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192660524593718348112323417 144495393445288761084242563)
      ·
        refine ⟨216743090167933141626363845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144495393445288761084242563 216743090167933141626363845)
        ·
          refine ⟨40639329406487464054943221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216743090167933141626363845 40639329406487464054943221)
          ·
            refine ⟨3809937131858199755150927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40639329406487464054943221 3809937131858199755150927)
            ·
              refine ⟨5714905697787299632726391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3809937131858199755150927 5714905697787299632726391)
              ·
                refine ⟨8572358546680949449089587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5714905697787299632726391 8572358546680949449089587)
                ·
                  refine ⟨12858537820021424173634381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8572358546680949449089587 12858537820021424173634381)
                  ·
                    refine ⟨4821951682508034065112893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12858537820021424173634381 4821951682508034065112893)
                    ·
                      refine ⟨1808231880940512774417335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4821951682508034065112893 1808231880940512774417335)
                      ·
                        rfl

theorem cell23_3521519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 3, 3].length) (baseStart_3521519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521519 prefixEnd_3521519 := by exact prefixLift 3521519
  have htrace : WordTrace (prefixWord ++ tailWord_3521519) baseStart_3521519 baseEnd_3521519 := by
    simpa [prefixWord, tailWord_3521519, baseEnd_3521519] using wordTrace_append hprefix tailTrace_3521519
  have hstable : (prefixWord ++ tailWord_3521519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521519).length < 2 ^ (prefixWord ++ tailWord_3521519).sum := by decide
  have hdescent : baseEnd_3521519 < baseStart_3521519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521546 : List Nat := [3, 1, 2, 2, 3, 1, 2, 3, 1, 3, 2]
def baseStart_3521546 : Nat := 118140960795 + 3521546 * 2 ^ 59
def prefixEnd_3521546 : Nat := 4983230072969 + 3 ^ 40 * 3521546 * 2
def baseEnd_3521546 : Nat := 1808245744918184168779711

theorem tailTrace_3521546 : CollatzResearch.WordTrace tailWord_3521546 prefixEnd_3521546 1808245744918184168779711 := by
  unfold tailWord_3521546
  simp only [CollatzResearch.WordTrace]
  refine ⟨32110333625011937254862123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85627556333365166012965661 32110333625011937254862123)
  ·
    refine ⟨48165500437517905882293185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32110333625011937254862123 48165500437517905882293185)
    ·
      refine ⟨36124125328138429411719889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48165500437517905882293185 36124125328138429411719889)
      ·
        refine ⟨27093093996103822058789917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36124125328138429411719889 27093093996103822058789917)
        ·
          refine ⟨10159910248538933272046219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27093093996103822058789917 10159910248538933272046219)
          ·
            refine ⟨15239865372808399908069329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10159910248538933272046219 15239865372808399908069329)
            ·
              refine ⟨11429899029606299931051997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15239865372808399908069329 11429899029606299931051997)
              ·
                refine ⟨4286212136102362474144499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11429899029606299931051997 4286212136102362474144499)
                ·
                  refine ⟨6429318204153543711216749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4286212136102362474144499 6429318204153543711216749)
                  ·
                    refine ⟨2410994326557578891706281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6429318204153543711216749 2410994326557578891706281)
                    ·
                      refine ⟨1808245744918184168779711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2410994326557578891706281 1808245744918184168779711)
                      ·
                        rfl

theorem cell23_3521546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_3521546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521546 prefixEnd_3521546 := by exact prefixLift 3521546
  have htrace : WordTrace (prefixWord ++ tailWord_3521546) baseStart_3521546 baseEnd_3521546 := by
    simpa [prefixWord, tailWord_3521546, baseEnd_3521546] using wordTrace_append hprefix tailTrace_3521546
  have hstable : (prefixWord ++ tailWord_3521546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521546).length < 2 ^ (prefixWord ++ tailWord_3521546).sum := by decide
  have hdescent : baseEnd_3521546 < baseStart_3521546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521554 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_3521554 : Nat := 118140960795 + 3521554 * 2 ^ 59
def prefixEnd_3521554 : Nat := 4983230072969 + 3 ^ 40 * 3521554 * 2
def baseEnd_3521554 : Nat := 1808249852763420137479675

theorem tailTrace_3521554 : CollatzResearch.WordTrace tailWord_3521554 prefixEnd_3521554 1808249852763420137479675 := by
  unfold tailWord_3521554
  simp only [CollatzResearch.WordTrace]
  refine ⟨32110406571004691596434929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85627750856012510923826477 32110406571004691596434929)
  ·
    refine ⟨24082804928253518697326197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32110406571004691596434929 24082804928253518697326197)
    ·
      refine ⟨2257762962023767377874331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24082804928253518697326197 2257762962023767377874331)
      ·
        refine ⟨3386644443035651066811497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2257762962023767377874331 3386644443035651066811497)
        ·
          refine ⟨2539983332276738300108623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3386644443035651066811497 2539983332276738300108623)
          ·
            refine ⟨3809974998415107450162935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539983332276738300108623 3809974998415107450162935)
            ·
              refine ⟨5714962497622661175244403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3809974998415107450162935 5714962497622661175244403)
              ·
                refine ⟨8572443746433991762866605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5714962497622661175244403 8572443746433991762866605)
                ·
                  refine ⟨3214666404912746911074977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8572443746433991762866605 3214666404912746911074977)
                  ·
                    refine ⟨2410999803684560183306233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3214666404912746911074977 2410999803684560183306233)
                    ·
                      refine ⟨1808249852763420137479675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2410999803684560183306233 1808249852763420137479675)
                      ·
                        rfl

theorem cell23_3521554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_3521554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521554 prefixEnd_3521554 := by exact prefixLift 3521554
  have htrace : WordTrace (prefixWord ++ tailWord_3521554) baseStart_3521554 baseEnd_3521554 := by
    simpa [prefixWord, tailWord_3521554, baseEnd_3521554] using wordTrace_append hprefix tailTrace_3521554
  have hstable : (prefixWord ++ tailWord_3521554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521554).length < 2 ^ (prefixWord ++ tailWord_3521554).sum := by decide
  have hdescent : baseEnd_3521554 < baseStart_3521554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521562 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3]
def baseStart_3521562 : Nat := 118140960795 + 3521562 * 2 ^ 59
def prefixEnd_3521562 : Nat := 4983230072969 + 3 ^ 40 * 3521562 * 2
def baseEnd_3521562 : Nat := 1808253960608656106179637

theorem tailTrace_3521562 : CollatzResearch.WordTrace tailWord_3521562 prefixEnd_3521562 1808253960608656106179637 := by
  unfold tailWord_3521562
  simp only [CollatzResearch.WordTrace]
  refine ⟨32110479516997445938007735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85627945378659855834687293 32110479516997445938007735)
  ·
    refine ⟨48165719275496168907011603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32110479516997445938007735 48165719275496168907011603)
    ·
      refine ⟨72248578913244253360517405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48165719275496168907011603 72248578913244253360517405)
      ·
        refine ⟨27093217092466595010194027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72248578913244253360517405 27093217092466595010194027)
        ·
          refine ⟨40639825638699892515291041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27093217092466595010194027 40639825638699892515291041)
          ·
            refine ⟨30479869229024919386468281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40639825638699892515291041 30479869229024919386468281)
            ·
              refine ⟨22859901921768689539851211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30479869229024919386468281 22859901921768689539851211)
              ·
                refine ⟨34289852882653034309776817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22859901921768689539851211 34289852882653034309776817)
                ·
                  refine ⟨25717389661989775732332613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34289852882653034309776817 25717389661989775732332613)
                  ·
                    refine ⟨4822010561623082949812365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25717389661989775732332613 4822010561623082949812365)
                    ·
                      refine ⟨1808253960608656106179637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4822010561623082949812365 1808253960608656106179637)
                      ·
                        rfl

theorem cell23_3521562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_3521562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521562 prefixEnd_3521562 := by exact prefixLift 3521562
  have htrace : WordTrace (prefixWord ++ tailWord_3521562) baseStart_3521562 baseEnd_3521562 := by
    simpa [prefixWord, tailWord_3521562, baseEnd_3521562] using wordTrace_append hprefix tailTrace_3521562
  have hstable : (prefixWord ++ tailWord_3521562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521562).length < 2 ^ (prefixWord ++ tailWord_3521562).sum := by decide
  have hdescent : baseEnd_3521562 < baseStart_3521562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521582 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 9]
def baseStart_3521582 : Nat := 118140960795 + 3521582 * 2 ^ 59
def prefixEnd_3521582 : Nat := 4983230072969 + 3 ^ 40 * 3521582 * 2
def baseEnd_3521582 : Nat := 200918247802416225325505

theorem tailTrace_3521582 : CollatzResearch.WordTrace tailWord_3521582 prefixEnd_3521582 200918247802416225325505 := by
  unfold tailWord_3521582
  simp only [CollatzResearch.WordTrace]
  refine ⟨16055330940989665895969875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85628431685278218111839333 16055330940989665895969875)
  ·
    refine ⟨24082996411484498843954813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16055330940989665895969875 24082996411484498843954813)
    ·
      refine ⟨9031123654306687066483055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24082996411484498843954813 9031123654306687066483055)
      ·
        refine ⟨13546685481460030599724583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9031123654306687066483055 13546685481460030599724583)
        ·
          refine ⟨20320028222190045899586875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13546685481460030599724583 20320028222190045899586875)
          ·
            refine ⟨30480042333285068849380313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20320028222190045899586875 30480042333285068849380313)
            ·
              refine ⟨22860031749963801637035235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30480042333285068849380313 22860031749963801637035235)
              ·
                refine ⟨34290047624945702455552853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22860031749963801637035235 34290047624945702455552853)
                ·
                  refine ⟨200918247802416225325505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34290047624945702455552853 200918247802416225325505)
                  ·
                    rfl

theorem cell23_3521582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_3521582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521582 prefixEnd_3521582 := by exact prefixLift 3521582
  have htrace : WordTrace (prefixWord ++ tailWord_3521582) baseStart_3521582 baseEnd_3521582 := by
    simpa [prefixWord, tailWord_3521582, baseEnd_3521582] using wordTrace_append hprefix tailTrace_3521582
  have hstable : (prefixWord ++ tailWord_3521582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521582).length < 2 ^ (prefixWord ++ tailWord_3521582).sum := by decide
  have hdescent : baseEnd_3521582 < baseStart_3521582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521615 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 8]
def baseStart_3521615 : Nat := 118140960795 + 3521615 * 2 ^ 59
def prefixEnd_3521615 : Nat := 4983230072969 + 3 ^ 40 * 3521615 * 2
def baseEnd_3521615 : Nat := 1808281175083344398816893

theorem tailTrace_3521615 : CollatzResearch.WordTrace tailWord_3521615 prefixEnd_3521615 1808281175083344398816893 := by
  unfold tailWord_3521615
  simp only [CollatzResearch.WordTrace]
  refine ⟨128443851136797773803710299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85629234091198515869140199 128443851136797773803710299)
  ·
    refine ⟨192665776705196660705565449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128443851136797773803710299 192665776705196660705565449)
    ·
      refine ⟨144499332528897495529174087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192665776705196660705565449 144499332528897495529174087)
      ·
        refine ⟨216748998793346243293761131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144499332528897495529174087 216748998793346243293761131)
        ·
          refine ⟨325123498190019364940641697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216748998793346243293761131 325123498190019364940641697)
          ·
            refine ⟨243842623642514523705481273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325123498190019364940641697 243842623642514523705481273)
            ·
              refine ⟨182881967731885892779110955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243842623642514523705481273 182881967731885892779110955)
              ·
                refine ⟨274322951597828839168666433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182881967731885892779110955 274322951597828839168666433)
                ·
                  refine ⟨205742213698371629376499825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274322951597828839168666433 205742213698371629376499825)
                  ·
                    refine ⟨154306660273778722032374869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 205742213698371629376499825 154306660273778722032374869)
                    ·
                      refine ⟨1808281175083344398816893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 154306660273778722032374869 1808281175083344398816893)
                      ·
                        rfl

theorem cell23_3521615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_3521615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521615 prefixEnd_3521615 := by exact prefixLift 3521615
  have htrace : WordTrace (prefixWord ++ tailWord_3521615) baseStart_3521615 baseEnd_3521615 := by
    simpa [prefixWord, tailWord_3521615, baseEnd_3521615] using wordTrace_append hprefix tailTrace_3521615
  have hstable : (prefixWord ++ tailWord_3521615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521615).length < 2 ^ (prefixWord ++ tailWord_3521615).sum := by decide
  have hdescent : baseEnd_3521615 < baseStart_3521615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521632 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 4]
def baseStart_3521632 : Nat := 118140960795 + 3521632 * 2 ^ 59
def prefixEnd_3521632 : Nat := 4983230072969 + 3 ^ 40 * 3521632 * 2
def baseEnd_3521632 : Nat := 1808289904254470832304315

theorem tailTrace_3521632 : CollatzResearch.WordTrace tailWord_3521632 prefixEnd_3521632 1808289904254470832304315 := by
  unfold tailWord_3521632
  simp only [CollatzResearch.WordTrace]
  refine ⟨64222235588868092853539575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85629647451824123804719433 64222235588868092853539575)
  ·
    refine ⟨96333353383302139280309363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64222235588868092853539575 96333353383302139280309363)
    ·
      refine ⟨144500030074953208920464045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96333353383302139280309363 144500030074953208920464045)
      ·
        refine ⟨54187511278107453345174017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144500030074953208920464045 54187511278107453345174017)
        ·
          refine ⟨40640633458580590008880513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54187511278107453345174017 40640633458580590008880513)
          ·
            refine ⟨30480475093935442506660385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40640633458580590008880513 30480475093935442506660385)
            ·
              refine ⟨22860356320451581879995289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30480475093935442506660385 22860356320451581879995289)
              ·
                refine ⟨17145267240338686409996467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22860356320451581879995289 17145267240338686409996467)
                ·
                  refine ⟨25717900860508029614994701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17145267240338686409996467 25717900860508029614994701)
                  ·
                    refine ⟨9644212822690511105623013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25717900860508029614994701 9644212822690511105623013)
                    ·
                      refine ⟨1808289904254470832304315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9644212822690511105623013 1808289904254470832304315)
                      ·
                        rfl

theorem cell23_3521632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_3521632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521632 prefixEnd_3521632 := by exact prefixLift 3521632
  have htrace : WordTrace (prefixWord ++ tailWord_3521632) baseStart_3521632 baseEnd_3521632 := by
    simpa [prefixWord, tailWord_3521632, baseEnd_3521632] using wordTrace_append hprefix tailTrace_3521632
  have hstable : (prefixWord ++ tailWord_3521632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521632).length < 2 ^ (prefixWord ++ tailWord_3521632).sum := by decide
  have hdescent : baseEnd_3521632 < baseStart_3521632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521646 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 2, 5]
def baseStart_3521646 : Nat := 118140960795 + 3521646 * 2 ^ 59
def prefixEnd_3521646 : Nat := 4983230072969 + 3 ^ 40 * 3521646 * 2
def baseEnd_3521646 : Nat := 602765697661211259176417

theorem tailTrace_3521646 : CollatzResearch.WordTrace tailWord_3521646 prefixEnd_3521646 602765697661211259176417 := by
  unfold tailWord_3521646
  simp only [CollatzResearch.WordTrace]
  refine ⟨16055622724960683262261099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85629987866456977398725861 16055622724960683262261099)
  ·
    refine ⟨24083434087441024893391649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16055622724960683262261099 24083434087441024893391649)
    ·
      refine ⟨18062575565580768670043737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24083434087441024893391649 18062575565580768670043737)
      ·
        refine ⟨13546931674185576502532803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18062575565580768670043737 13546931674185576502532803)
        ·
          refine ⟨20320397511278364753799205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13546931674185576502532803 20320397511278364753799205)
          ·
            refine ⟨3810074533364693391337351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20320397511278364753799205 3810074533364693391337351)
            ·
              refine ⟨5715111800047040087006027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3810074533364693391337351 5715111800047040087006027)
              ·
                refine ⟨8572667700070560130509041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5715111800047040087006027 8572667700070560130509041)
                ·
                  refine ⟨6429500775052920097881781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8572667700070560130509041 6429500775052920097881781)
                  ·
                    refine ⟨602765697661211259176417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6429500775052920097881781 602765697661211259176417)
                    ·
                      rfl

theorem cell23_3521646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_3521646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521646 prefixEnd_3521646 := by exact prefixLift 3521646
  have htrace : WordTrace (prefixWord ++ tailWord_3521646) baseStart_3521646 baseEnd_3521646 := by
    simpa [prefixWord, tailWord_3521646, baseEnd_3521646] using wordTrace_append hprefix tailTrace_3521646
  have hstable : (prefixWord ++ tailWord_3521646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521646).length < 2 ^ (prefixWord ++ tailWord_3521646).sum := by decide
  have hdescent : baseEnd_3521646 < baseStart_3521646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521719 : List Nat := [1, 1, 3, 1, 4, 1, 1, 5, 1, 5]
def baseStart_3521719 : Nat := 118140960795 + 3521719 * 2 ^ 59
def prefixEnd_3521719 : Nat := 4983230072969 + 3 ^ 40 * 3521719 * 2
def baseEnd_3521719 : Nat := 602778192357137330638805

theorem tailTrace_3521719 : CollatzResearch.WordTrace tailWord_3521719 prefixEnd_3521719 602778192357137330638805 := by
  unfold tailWord_3521719
  simp only [CollatzResearch.WordTrace]
  refine ⟨128447644328420999565496211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85631762885613999710330807 128447644328420999565496211)
  ·
    refine ⟨192671466492631499348244317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128447644328420999565496211 192671466492631499348244317)
    ·
      refine ⟨72251799934736812255591619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192671466492631499348244317 72251799934736812255591619)
      ·
        refine ⟨108377699902105218383387429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72251799934736812255591619 108377699902105218383387429)
        ·
          refine ⟨20320818731644728446885143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108377699902105218383387429 20320818731644728446885143)
          ·
            refine ⟨30481228097467092670327715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20320818731644728446885143 30481228097467092670327715)
            ·
              refine ⟨45721842146200639005491573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30481228097467092670327715 45721842146200639005491573)
              ·
                refine ⟨4286422701206309906764835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45721842146200639005491573 4286422701206309906764835)
                ·
                  refine ⟨6429634051809464860147253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4286422701206309906764835 6429634051809464860147253)
                  ·
                    refine ⟨602778192357137330638805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6429634051809464860147253 602778192357137330638805)
                    ·
                      rfl

theorem cell23_3521719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_3521719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521719 prefixEnd_3521719 := by exact prefixLift 3521719
  have htrace : WordTrace (prefixWord ++ tailWord_3521719) baseStart_3521719 baseEnd_3521719 := by
    simpa [prefixWord, tailWord_3521719, baseEnd_3521719] using wordTrace_append hprefix tailTrace_3521719
  have hstable : (prefixWord ++ tailWord_3521719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521719).length < 2 ^ (prefixWord ++ tailWord_3521719).sum := by decide
  have hdescent : baseEnd_3521719 < baseStart_3521719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521739 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 2, 6, 2]
def baseStart_3521739 : Nat := 118140960795 + 3521739 * 2 ^ 59
def prefixEnd_3521739 : Nat := 4983230072969 + 3 ^ 40 * 3521739 * 2
def baseEnd_3521739 : Nat := 1808344846684501913666323

theorem tailTrace_3521739 : CollatzResearch.WordTrace tailWord_3521739 prefixEnd_3521739 1808344846684501913666323 := by
  unfold tailWord_3521739
  simp only [CollatzResearch.WordTrace]
  refine ⟨128448373788348542981224271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85632249192232361987482847 128448373788348542981224271)
  ·
    refine ⟨192672560682522814471836407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128448373788348542981224271 192672560682522814471836407)
    ·
      refine ⟨289008841023784221707754611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192672560682522814471836407 289008841023784221707754611)
      ·
        refine ⟨433513261535676332561631917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289008841023784221707754611 433513261535676332561631917)
        ·
          refine ⟨162567473075878624710611969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433513261535676332561631917 162567473075878624710611969)
          ·
            refine ⟨121925604806908968532958977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162567473075878624710611969 121925604806908968532958977)
            ·
              refine ⟨91444203605181726399719233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121925604806908968532958977 91444203605181726399719233)
              ·
                refine ⟨68583152703886294799789425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91444203605181726399719233 68583152703886294799789425)
                ·
                  refine ⟨51437364527914721099842069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68583152703886294799789425 51437364527914721099842069)
                  ·
                    refine ⟨2411126462246002551555097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51437364527914721099842069 2411126462246002551555097)
                    ·
                      refine ⟨1808344846684501913666323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2411126462246002551555097 1808344846684501913666323)
                      ·
                        rfl

theorem cell23_3521739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 6, 2].length) (baseStart_3521739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521739 prefixEnd_3521739 := by exact prefixLift 3521739
  have htrace : WordTrace (prefixWord ++ tailWord_3521739) baseStart_3521739 baseEnd_3521739 := by
    simpa [prefixWord, tailWord_3521739, baseEnd_3521739] using wordTrace_append hprefix tailTrace_3521739
  have hstable : (prefixWord ++ tailWord_3521739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521739).length < 2 ^ (prefixWord ++ tailWord_3521739).sum := by decide
  have hdescent : baseEnd_3521739 < baseStart_3521739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521796 : List Nat := [2, 3, 2, 2, 2, 3, 1, 8]
def baseStart_3521796 : Nat := 118140960795 + 3521796 * 2 ^ 59
def prefixEnd_3521796 : Nat := 4983230072969 + 3 ^ 40 * 3521796 * 2
def baseEnd_3521796 : Nat := 66976819077104007061243

theorem tailTrace_3521796 : CollatzResearch.WordTrace tailWord_3521796 prefixEnd_3521796 66976819077104007061243 := by
  unfold tailWord_3521796
  simp only [CollatzResearch.WordTrace]
  refine ⟨64225226374571020858024621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85633635166094694477366161 64225226374571020858024621)
  ·
    refine ⟨24084459890464132821759233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64225226374571020858024621 24084459890464132821759233)
    ·
      refine ⟨18063344917848099616319425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24084459890464132821759233 18063344917848099616319425)
      ·
        refine ⟨13547508688386074712239569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18063344917848099616319425 13547508688386074712239569)
        ·
          refine ⟨10160631516289556034179677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13547508688386074712239569 10160631516289556034179677)
          ·
            refine ⟨3810236818608583512817379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10160631516289556034179677 3810236818608583512817379)
            ·
              refine ⟨5715355227912875269226069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3810236818608583512817379 5715355227912875269226069)
              ·
                refine ⟨66976819077104007061243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5715355227912875269226069 66976819077104007061243)
                ·
                  rfl

theorem cell23_3521796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 8].length) (baseStart_3521796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521796 prefixEnd_3521796 := by exact prefixLift 3521796
  have htrace : WordTrace (prefixWord ++ tailWord_3521796) baseStart_3521796 baseEnd_3521796 := by
    simpa [prefixWord, tailWord_3521796, baseEnd_3521796] using wordTrace_append hprefix tailTrace_3521796
  have hstable : (prefixWord ++ tailWord_3521796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521796).length < 2 ^ (prefixWord ++ tailWord_3521796).sum := by decide
  have hdescent : baseEnd_3521796 < baseStart_3521796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521806 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3]
def baseStart_3521806 : Nat := 118140960795 + 3521806 * 2 ^ 59
def prefixEnd_3521806 : Nat := 4983230072969 + 3 ^ 40 * 3521806 * 2
def baseEnd_3521806 : Nat := 1808379249888353151528515

theorem tailTrace_3521806 : CollatzResearch.WordTrace tailWord_3521806 prefixEnd_3521806 1808379249888353151528515 := by
  unfold tailWord_3521806
  simp only [CollatzResearch.WordTrace]
  refine ⟨16056352184888226677989159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85633878319403875615942181 16056352184888226677989159)
  ·
    refine ⟨24084528277332340016983739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16056352184888226677989159 24084528277332340016983739)
    ·
      refine ⟨36126792415998510025475609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24084528277332340016983739 36126792415998510025475609)
      ·
        refine ⟨27095094311998882519106707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36126792415998510025475609 27095094311998882519106707)
        ·
          refine ⟨40642641467998323778660061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27095094311998882519106707 40642641467998323778660061)
          ·
            refine ⟨15240990550499371416997523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40642641467998323778660061 15240990550499371416997523)
            ·
              refine ⟨22861485825749057125496285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15240990550499371416997523 22861485825749057125496285)
              ·
                refine ⟨8573057184655896422061107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22861485825749057125496285 8573057184655896422061107)
                ·
                  refine ⟨12859585776983844633091661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8573057184655896422061107 12859585776983844633091661)
                  ·
                    refine ⟨4822344666368941737409373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12859585776983844633091661 4822344666368941737409373)
                    ·
                      refine ⟨1808379249888353151528515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4822344666368941737409373 1808379249888353151528515)
                      ·
                        rfl

theorem cell23_3521806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_3521806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521806 prefixEnd_3521806 := by exact prefixLift 3521806
  have htrace : WordTrace (prefixWord ++ tailWord_3521806) baseStart_3521806 baseEnd_3521806 := by
    simpa [prefixWord, tailWord_3521806, baseEnd_3521806] using wordTrace_append hprefix tailTrace_3521806
  have hstable : (prefixWord ++ tailWord_3521806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521806).length < 2 ^ (prefixWord ++ tailWord_3521806).sum := by decide
  have hdescent : baseEnd_3521806 < baseStart_3521806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521857 : List Nat := [1, 2, 5, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_3521857 : Nat := 118140960795 + 3521857 * 2 ^ 59
def prefixEnd_3521857 : Nat := 4983230072969 + 3 ^ 40 * 3521857 * 2
def baseEnd_3521857 : Nat := 1808405437401732451990781

theorem tailTrace_3521857 : CollatzResearch.WordTrace tailWord_3521857 prefixEnd_3521857 1808405437401732451990781 := by
  unfold tailWord_3521857
  simp only [CollatzResearch.WordTrace]
  refine ⟨128452677601921049134019825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85635118401280699422679883 128452677601921049134019825)
  ·
    refine ⟨96339508201440786850514869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128452677601921049134019825 96339508201440786850514869)
    ·
      refine ⟨9031828893885073767235769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96339508201440786850514869 9031828893885073767235769)
      ·
        refine ⟨6773871670413805325426827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9031828893885073767235769 6773871670413805325426827)
        ·
          refine ⟨10160807505620707988140241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6773871670413805325426827 10160807505620707988140241)
          ·
            refine ⟨7620605629215530991105181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10160807505620707988140241 7620605629215530991105181)
            ·
              refine ⟨2857727110955824121664443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7620605629215530991105181 2857727110955824121664443)
              ·
                refine ⟨4286590666433736182496665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2857727110955824121664443 4286590666433736182496665)
                ·
                  refine ⟨3214942999825302136872499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4286590666433736182496665 3214942999825302136872499)
                  ·
                    refine ⟨4822414499737953205308749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3214942999825302136872499 4822414499737953205308749)
                    ·
                      refine ⟨1808405437401732451990781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4822414499737953205308749 1808405437401732451990781)
                      ·
                        rfl

theorem cell23_3521857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_3521857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521857 prefixEnd_3521857 := by exact prefixLift 3521857
  have htrace : WordTrace (prefixWord ++ tailWord_3521857) baseStart_3521857 baseEnd_3521857 := by
    simpa [prefixWord, tailWord_3521857, baseEnd_3521857] using wordTrace_append hprefix tailTrace_3521857
  have hstable : (prefixWord ++ tailWord_3521857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521857).length < 2 ^ (prefixWord ++ tailWord_3521857).sum := by decide
  have hdescent : baseEnd_3521857 < baseStart_3521857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521863 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 1, 4, 2]
def baseStart_3521863 : Nat := 118140960795 + 3521863 * 2 ^ 59
def prefixEnd_3521863 : Nat := 4983230072969 + 3 ^ 40 * 3521863 * 2
def baseEnd_3521863 : Nat := 1808408518285659428515753

theorem tailTrace_3521863 : CollatzResearch.WordTrace tailWord_3521863 prefixEnd_3521863 1808408518285659428515753 := by
  unfold tailWord_3521863
  simp only [CollatzResearch.WordTrace]
  refine ⟨128452896439899312158738243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85635264293266208105825495 128452896439899312158738243)
  ·
    refine ⟨192679344659848968238107365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128452896439899312158738243 192679344659848968238107365)
    ·
      refine ⟨36127377123721681544645131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192679344659848968238107365 36127377123721681544645131)
      ·
        refine ⟨54191065685582522316967697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36127377123721681544645131 54191065685582522316967697)
        ·
          refine ⟨40643299264186891737725773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54191065685582522316967697 40643299264186891737725773)
          ·
            refine ⟨15241237224070084401647165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40643299264186891737725773 15241237224070084401647165)
            ·
              refine ⟨5715463959026281650617687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15241237224070084401647165 5715463959026281650617687)
              ·
                refine ⟨8573195938539422475926531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5715463959026281650617687 8573195938539422475926531)
                ·
                  refine ⟨12859793907809133713889797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8573195938539422475926531 12859793907809133713889797)
                  ·
                    refine ⟨2411211357714212571354337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12859793907809133713889797 2411211357714212571354337)
                    ·
                      refine ⟨1808408518285659428515753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2411211357714212571354337 1808408518285659428515753)
                      ·
                        rfl

theorem cell23_3521863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_3521863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521863 prefixEnd_3521863 := by exact prefixLift 3521863
  have htrace : WordTrace (prefixWord ++ tailWord_3521863) baseStart_3521863 baseEnd_3521863 := by
    simpa [prefixWord, tailWord_3521863, baseEnd_3521863] using wordTrace_append hprefix tailTrace_3521863
  have hstable : (prefixWord ++ tailWord_3521863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521863).length < 2 ^ (prefixWord ++ tailWord_3521863).sum := by decide
  have hdescent : baseEnd_3521863 < baseStart_3521863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521903 : List Nat := [1, 1, 2, 1, 3, 1, 7, 2, 5]
def baseStart_3521903 : Nat := 118140960795 + 3521903 * 2 ^ 59
def prefixEnd_3521903 : Nat := 4983230072969 + 3 ^ 40 * 3521903 * 2
def baseEnd_3521903 : Nat := 200936561945759919112841

theorem tailTrace_3521903 : CollatzResearch.WordTrace tailWord_3521903 prefixEnd_3521903 200936561945759919112841 := by
  unfold tailWord_3521903
  simp only [CollatzResearch.WordTrace]
  refine ⟨128454355359754398990194363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85636236906502932660129575 128454355359754398990194363)
  ·
    refine ⟨192681533039631598485291545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128454355359754398990194363 192681533039631598485291545)
    ·
      refine ⟨144511149779723698863968659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192681533039631598485291545 144511149779723698863968659)
      ·
        refine ⟨216766724669585548295952989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144511149779723698863968659 216766724669585548295952989)
        ·
          refine ⟨81287521751094580610982371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216766724669585548295952989 81287521751094580610982371)
          ·
            refine ⟨121931282626641870916473557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81287521751094580610982371 121931282626641870916473557)
            ·
              refine ⟨2857764436561918849604849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 121931282626641870916473557 2857764436561918849604849)
              ·
                refine ⟨2143323327421439137203637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2857764436561918849604849 2143323327421439137203637)
                ·
                  refine ⟨200936561945759919112841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2143323327421439137203637 200936561945759919112841)
                  ·
                    rfl

theorem cell23_3521903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 5].length) (baseStart_3521903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521903 prefixEnd_3521903 := by exact prefixLift 3521903
  have htrace : WordTrace (prefixWord ++ tailWord_3521903) baseStart_3521903 baseEnd_3521903 := by
    simpa [prefixWord, tailWord_3521903, baseEnd_3521903] using wordTrace_append hprefix tailTrace_3521903
  have hstable : (prefixWord ++ tailWord_3521903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521903).length < 2 ^ (prefixWord ++ tailWord_3521903).sum := by decide
  have hdescent : baseEnd_3521903 < baseStart_3521903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521956 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 3, 4, 3]
def baseStart_3521956 : Nat := 118140960795 + 3521956 * 2 ^ 59
def prefixEnd_3521956 : Nat := 4983230072969 + 3 ^ 40 * 3521956 * 2
def baseEnd_3521956 : Nat := 1808456271986527564652825

theorem tailTrace_3521956 : CollatzResearch.WordTrace tailWord_3521956 prefixEnd_3521956 1808456271986527564652825 := by
  unfold tailWord_3521956
  simp only [CollatzResearch.WordTrace]
  refine ⟨64228144214281194520936861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85637525619041592694582481 64228144214281194520936861)
  ·
    refine ⟨24085554080355447945351323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64228144214281194520936861 24085554080355447945351323)
    ·
      refine ⟨36128331120533171918026985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24085554080355447945351323 36128331120533171918026985)
      ·
        refine ⟨27096248340399878938520239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36128331120533171918026985 27096248340399878938520239)
        ·
          refine ⟨40644372510599818407780359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27096248340399878938520239 40644372510599818407780359)
          ·
            refine ⟨60966558765899727611670539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40644372510599818407780359 60966558765899727611670539)
            ·
              refine ⟨91449838148849591417505809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60966558765899727611670539 91449838148849591417505809)
              ·
                refine ⟨68587378611637193563129357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91449838148849591417505809 68587378611637193563129357)
                ·
                  refine ⟨25720266979363947586173509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68587378611637193563129357 25720266979363947586173509)
                  ·
                    refine ⟨4822550058630740172407533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25720266979363947586173509 4822550058630740172407533)
                    ·
                      refine ⟨1808456271986527564652825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4822550058630740172407533 1808456271986527564652825)
                      ·
                        rfl

theorem cell23_3521956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_3521956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521956 prefixEnd_3521956 := by exact prefixLift 3521956
  have htrace : WordTrace (prefixWord ++ tailWord_3521956) baseStart_3521956 baseEnd_3521956 := by
    simpa [prefixWord, tailWord_3521956, baseEnd_3521956] using wordTrace_append hprefix tailTrace_3521956
  have hstable : (prefixWord ++ tailWord_3521956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521956).length < 2 ^ (prefixWord ++ tailWord_3521956).sum := by decide
  have hdescent : baseEnd_3521956 < baseStart_3521956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521976 : List Nat := [2, 1, 2, 1, 2, 2, 4, 3, 6]
def baseStart_3521976 : Nat := 118140960795 + 3521976 * 2 ^ 59
def prefixEnd_3521976 : Nat := 4983230072969 + 3 ^ 40 * 3521976 * 2
def baseEnd_3521976 : Nat := 200940726844401942933637

theorem tailTrace_3521976 : CollatzResearch.WordTrace tailWord_3521976 prefixEnd_3521976 200940726844401942933637 := by
  unfold tailWord_3521976
  simp only [CollatzResearch.WordTrace]
  refine ⟨64228508944244966228800891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85638011925659954971734521 64228508944244966228800891)
  ·
    refine ⟨96342763416367449343201337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64228508944244966228800891 96342763416367449343201337)
    ·
      refine ⟨72257072562275587007401003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96342763416367449343201337 72257072562275587007401003)
      ·
        refine ⟨108385608843413380511101505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72257072562275587007401003 108385608843413380511101505)
        ·
          refine ⟨81289206632560035383326129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108385608843413380511101505 81289206632560035383326129)
          ·
            refine ⟨60966904974420026537494597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81289206632560035383326129 60966904974420026537494597)
            ·
              refine ⟨11431294682703754975780237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60966904974420026537494597 11431294682703754975780237)
              ·
                refine ⟨4286735506013908115917589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11431294682703754975780237 4286735506013908115917589)
                ·
                  refine ⟨200940726844401942933637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4286735506013908115917589 200940726844401942933637)
                  ·
                    rfl

theorem cell23_3521976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 6].length) (baseStart_3521976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521976 prefixEnd_3521976 := by exact prefixLift 3521976
  have htrace : WordTrace (prefixWord ++ tailWord_3521976) baseStart_3521976 baseEnd_3521976 := by
    simpa [prefixWord, tailWord_3521976, baseEnd_3521976] using wordTrace_append hprefix tailTrace_3521976
  have hstable : (prefixWord ++ tailWord_3521976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521976).length < 2 ^ (prefixWord ++ tailWord_3521976).sum := by decide
  have hdescent : baseEnd_3521976 < baseStart_3521976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521980 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 3, 4]
def baseStart_3521980 : Nat := 118140960795 + 3521980 * 2 ^ 59
def prefixEnd_3521980 : Nat := 4983230072969 + 3 ^ 40 * 3521980 * 2
def baseEnd_3521980 : Nat := 602822865174078490250905

theorem tailTrace_3521980 : CollatzResearch.WordTrace tailWord_3521980 prefixEnd_3521980 602822865174078490250905 := by
  unfold tailWord_3521980
  simp only [CollatzResearch.WordTrace]
  refine ⟨64228581890237720570373697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85638109186983627427164929 64228581890237720570373697)
  ·
    refine ⟨48171436417678290427780273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64228581890237720570373697 48171436417678290427780273)
    ·
      refine ⟨36128577313258717820835205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48171436417678290427780273 36128577313258717820835205)
      ·
        refine ⟨6774108246236009591406601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36128577313258717820835205 6774108246236009591406601)
        ·
          refine ⟨5080581184677007193554951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6774108246236009591406601 5080581184677007193554951)
          ·
            refine ⟨7620871777015510790332427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5080581184677007193554951 7620871777015510790332427)
            ·
              refine ⟨11431307665523266185498641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7620871777015510790332427 11431307665523266185498641)
              ·
                refine ⟨8573480749142449639123981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11431307665523266185498641 8573480749142449639123981)
                ·
                  refine ⟨3215055280928418614671493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8573480749142449639123981 3215055280928418614671493)
                  ·
                    refine ⟨602822865174078490250905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3215055280928418614671493 602822865174078490250905)
                    ·
                      rfl

theorem cell23_3521980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_3521980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3521980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3521980 prefixEnd_3521980 := by exact prefixLift 3521980
  have htrace : WordTrace (prefixWord ++ tailWord_3521980) baseStart_3521980 baseEnd_3521980 := by
    simpa [prefixWord, tailWord_3521980, baseEnd_3521980] using wordTrace_append hprefix tailTrace_3521980
  have hstable : (prefixWord ++ tailWord_3521980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521980).length < 2 ^ (prefixWord ++ tailWord_3521980).sum := by decide
  have hdescent : baseEnd_3521980 < baseStart_3521980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522037 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3522037 : Nat := 118140960795 + 3522037 * 2 ^ 59
def prefixEnd_3522037 : Nat := 4983230072969 + 3 ^ 40 * 3522037 * 2
def baseEnd_3522037 : Nat := 1808497863919541747739953

theorem tailTrace_3522037 : CollatzResearch.WordTrace tailWord_3522037 prefixEnd_3522037 1808497863919541747739953 := by
  unfold tailWord_3522037
  simp only [CollatzResearch.WordTrace]
  refine ⟨128459242741268939875572365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85639495160845959917048243 128459242741268939875572365)
  ·
    refine ⟨48172216027975852453339637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128459242741268939875572365 48172216027975852453339637)
    ·
      refine ⟨4516145252622736167500591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48172216027975852453339637 4516145252622736167500591)
      ·
        refine ⟨6774217878934104251250887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4516145252622736167500591 6774217878934104251250887)
        ·
          refine ⟨10161326818401156376876331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6774217878934104251250887 10161326818401156376876331)
          ·
            refine ⟨15241990227601734565314497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10161326818401156376876331 15241990227601734565314497)
            ·
              refine ⟨11431492670701300923985873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15241990227601734565314497 11431492670701300923985873)
              ·
                refine ⟨8573619503025975692989405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11431492670701300923985873 8573619503025975692989405)
                ·
                  refine ⟨3215107313634740884871027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8573619503025975692989405 3215107313634740884871027)
                  ·
                    refine ⟨4822660970452111327306541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3215107313634740884871027 4822660970452111327306541)
                    ·
                      refine ⟨1808497863919541747739953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4822660970452111327306541 1808497863919541747739953)
                      ·
                        rfl

theorem cell23_3522037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3522037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522037 prefixEnd_3522037 := by exact prefixLift 3522037
  have htrace : WordTrace (prefixWord ++ tailWord_3522037) baseStart_3522037 baseEnd_3522037 := by
    simpa [prefixWord, tailWord_3522037, baseEnd_3522037] using wordTrace_append hprefix tailTrace_3522037
  have hstable : (prefixWord ++ tailWord_3522037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522037).length < 2 ^ (prefixWord ++ tailWord_3522037).sum := by decide
  have hdescent : baseEnd_3522037 < baseStart_3522037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522078 : List Nat := [4, 3, 3, 1, 2, 1, 2, 1, 6]
def baseStart_3522078 : Nat := 118140960795 + 3522078 * 2 ^ 59
def prefixEnd_3522078 : Nat := 4983230072969 + 3 ^ 40 * 3522078 * 2
def baseEnd_3522078 : Nat := 200946546291819565258585

theorem tailTrace_3522078 : CollatzResearch.WordTrace tailWord_3522078 prefixEnd_3522078 200946546291819565258585 := by
  unfold tailWord_3522078
  simp only [CollatzResearch.WordTrace]
  refine ⟨16057592266765050484726861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85640492089413602585209925 16057592266765050484726861)
  ·
    refine ⟨6021597100036893931772573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16057592266765050484726861 6021597100036893931772573)
    ·
      refine ⟨2258098912513835224414715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6021597100036893931772573 2258098912513835224414715)
      ·
        refine ⟨3387148368770752836622073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2258098912513835224414715 3387148368770752836622073)
        ·
          refine ⟨2540361276578064627466555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3387148368770752836622073 2540361276578064627466555)
          ·
            refine ⟨3810541914867096941199833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2540361276578064627466555 3810541914867096941199833)
            ·
              refine ⟨2857906436150322705899875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3810541914867096941199833 2857906436150322705899875)
              ·
                refine ⟨4286859654225484058849813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2857906436150322705899875 4286859654225484058849813)
                ·
                  refine ⟨200946546291819565258585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4286859654225484058849813 200946546291819565258585)
                  ·
                    rfl

theorem cell23_3522078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_3522078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522078 prefixEnd_3522078 := by exact prefixLift 3522078
  have htrace : WordTrace (prefixWord ++ tailWord_3522078) baseStart_3522078 baseEnd_3522078 := by
    simpa [prefixWord, tailWord_3522078, baseEnd_3522078] using wordTrace_append hprefix tailTrace_3522078
  have hstable : (prefixWord ++ tailWord_3522078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522078).length < 2 ^ (prefixWord ++ tailWord_3522078).sum := by decide
  have hdescent : baseEnd_3522078 < baseStart_3522078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522083 : List Nat := [1, 1, 1, 4, 5, 1, 2, 8]
def baseStart_3522083 : Nat := 118140960795 + 3522083 * 2 ^ 59
def prefixEnd_3522083 : Nat := 4983230072969 + 3 ^ 40 * 3522083 * 2
def baseEnd_3522083 : Nat := 66982277186283280287583

theorem tailTrace_3522083 : CollatzResearch.WordTrace tailWord_3522083 prefixEnd_3522083 66982277186283280287583 := by
  unfold tailWord_3522083
  simp only [CollatzResearch.WordTrace]
  refine ⟨128460920499102289731746903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85640613666068193154497935 128460920499102289731746903)
  ·
    refine ⟨192691380748653434597620355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128460920499102289731746903 192691380748653434597620355)
    ·
      refine ⟨289037071122980151896430533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192691380748653434597620355 289037071122980151896430533)
      ·
        refine ⟨54194450835558778480580725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289037071122980151896430533 54194450835558778480580725)
        ·
          refine ⟨5080729765833635482554443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54194450835558778480580725 5080729765833635482554443)
          ·
            refine ⟨7621094648750453223831665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5080729765833635482554443 7621094648750453223831665)
            ·
              refine ⟨5715820986562839917873749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7621094648750453223831665 5715820986562839917873749)
              ·
                refine ⟨66982277186283280287583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5715820986562839917873749 66982277186283280287583)
                ·
                  rfl

theorem cell23_3522083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 8].length) (baseStart_3522083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522083 prefixEnd_3522083 := by exact prefixLift 3522083
  have htrace : WordTrace (prefixWord ++ tailWord_3522083) baseStart_3522083 baseEnd_3522083 := by
    simpa [prefixWord, tailWord_3522083, baseEnd_3522083] using wordTrace_append hprefix tailTrace_3522083
  have hstable : (prefixWord ++ tailWord_3522083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522083).length < 2 ^ (prefixWord ++ tailWord_3522083).sum := by decide
  have hdescent : baseEnd_3522083 < baseStart_3522083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522134 : List Nat := [5, 2, 2, 2, 1, 2, 1, 8]
def baseStart_3522134 : Nat := 118140960795 + 3522134 * 2 ^ 59
def prefixEnd_3522134 : Nat := 4983230072969 + 3 ^ 40 * 3522134 * 2
def baseEnd_3522134 : Nat := 66983247094186217341741

theorem tailTrace_3522134 : CollatzResearch.WordTrace tailWord_3522134 prefixEnd_3522134 66983247094186217341741 := by
  unfold tailWord_3522134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8028923788869845340115841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85641853747945016961235637 8028923788869845340115841)
  ·
    refine ⟨6021692841652384005086881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8028923788869845340115841 6021692841652384005086881)
    ·
      refine ⟨4516269631239288003815161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6021692841652384005086881 4516269631239288003815161)
      ·
        refine ⟨3387202223429466002861371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4516269631239288003815161 3387202223429466002861371)
        ·
          refine ⟨5080803335144199004292057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3387202223429466002861371 5080803335144199004292057)
          ·
            refine ⟨3810602501358149253219043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5080803335144199004292057 3810602501358149253219043)
            ·
              refine ⟨5715903752037223879828565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3810602501358149253219043 5715903752037223879828565)
              ·
                refine ⟨66983247094186217341741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5715903752037223879828565 66983247094186217341741)
                ·
                  rfl

theorem cell23_3522134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_3522134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522134 prefixEnd_3522134 := by exact prefixLift 3522134
  have htrace : WordTrace (prefixWord ++ tailWord_3522134) baseStart_3522134 baseEnd_3522134 := by
    simpa [prefixWord, tailWord_3522134, baseEnd_3522134] using wordTrace_append hprefix tailTrace_3522134
  have hstable : (prefixWord ++ tailWord_3522134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522134).length < 2 ^ (prefixWord ++ tailWord_3522134).sum := by decide
  have hdescent : baseEnd_3522134 < baseStart_3522134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522190 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 7]
def baseStart_3522190 : Nat := 118140960795 + 3522190 * 2 ^ 59
def prefixEnd_3522190 : Nat := 4983230072969 + 3 ^ 40 * 3522190 * 2
def baseEnd_3522190 : Nat := 200952936273297738791861

theorem tailTrace_3522190 : CollatzResearch.WordTrace tailWord_3522190 prefixEnd_3522190 200952936273297738791861 := by
  unfold tailWord_3522190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16058102888714330875736503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85643215406476431337261349 16058102888714330875736503)
  ·
    refine ⟨24087154333071496313604755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16058102888714330875736503 24087154333071496313604755)
    ·
      refine ⟨36130731499607244470407133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24087154333071496313604755 36130731499607244470407133)
      ·
        refine ⟨13549024312352716676402675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36130731499607244470407133 13549024312352716676402675)
        ·
          refine ⟨20323536468529075014604013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13549024312352716676402675 20323536468529075014604013)
          ·
            refine ⟨7621326175698403130476505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20323536468529075014604013 7621326175698403130476505)
            ·
              refine ⟨5715994631773802347857379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7621326175698403130476505 5715994631773802347857379)
              ·
                refine ⟨8573991947660703521786069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5715994631773802347857379 8573991947660703521786069)
                ·
                  refine ⟨200952936273297738791861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8573991947660703521786069 200952936273297738791861)
                  ·
                    rfl

theorem cell23_3522190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_3522190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522190 prefixEnd_3522190 := by exact prefixLift 3522190
  have htrace : WordTrace (prefixWord ++ tailWord_3522190) baseStart_3522190 baseEnd_3522190 := by
    simpa [prefixWord, tailWord_3522190, baseEnd_3522190] using wordTrace_append hprefix tailTrace_3522190
  have hstable : (prefixWord ++ tailWord_3522190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522190).length < 2 ^ (prefixWord ++ tailWord_3522190).sum := by decide
  have hdescent : baseEnd_3522190 < baseStart_3522190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522200 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 2, 3, 3]
def baseStart_3522200 : Nat := 118140960795 + 3522200 * 2 ^ 59
def prefixEnd_3522200 : Nat := 4983230072969 + 3 ^ 40 * 3522200 * 2
def baseEnd_3522200 : Nat := 1808581561266224610001703

theorem tailTrace_3522200 : CollatzResearch.WordTrace tailWord_3522200 prefixEnd_3522200 1808581561266224610001703 := by
  unfold tailWord_3522200
  simp only [CollatzResearch.WordTrace]
  refine ⟨64232593919839209356878027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85643458559785612475837369 64232593919839209356878027)
  ·
    refine ⟨96348890879758814035317041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64232593919839209356878027 96348890879758814035317041)
    ·
      refine ⟨72261668159819110526487781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96348890879758814035317041 72261668159819110526487781)
      ·
        refine ⟨13549062779966083223716459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72261668159819110526487781 13549062779966083223716459)
        ·
          refine ⟨20323594169949124835574689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13549062779966083223716459 20323594169949124835574689)
          ·
            refine ⟨15242695627461843626681017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20323594169949124835574689 15242695627461843626681017)
            ·
              refine ⟨11432021720596382720010763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15242695627461843626681017 11432021720596382720010763)
              ·
                refine ⟨17148032580894574080016145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11432021720596382720010763 17148032580894574080016145)
                ·
                  refine ⟨12861024435670930560012109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17148032580894574080016145 12861024435670930560012109)
                  ·
                    refine ⟨4822884163376598960004541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12861024435670930560012109 4822884163376598960004541)
                    ·
                      refine ⟨1808581561266224610001703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4822884163376598960004541 1808581561266224610001703)
                      ·
                        rfl

theorem cell23_3522200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_3522200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522200 prefixEnd_3522200 := by exact prefixLift 3522200
  have htrace : WordTrace (prefixWord ++ tailWord_3522200) baseStart_3522200 baseEnd_3522200 := by
    simpa [prefixWord, tailWord_3522200, baseEnd_3522200] using wordTrace_append hprefix tailTrace_3522200
  have hstable : (prefixWord ++ tailWord_3522200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522200).length < 2 ^ (prefixWord ++ tailWord_3522200).sum := by decide
  have hdescent : baseEnd_3522200 < baseStart_3522200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522223 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 4]
def baseStart_3522223 : Nat := 118140960795 + 3522223 * 2 ^ 59
def prefixEnd_3522223 : Nat := 4983230072969 + 3 ^ 40 * 3522223 * 2
def baseEnd_3522223 : Nat := 1808593371321278020014097

theorem tailTrace_3522223 : CollatzResearch.WordTrace tailWord_3522223 prefixEnd_3522223 1808593371321278020014097 := by
  unfold tailWord_3522223
  simp only [CollatzResearch.WordTrace]
  refine ⟨128466026718595093641843323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85644017812396729094562215 128466026718595093641843323)
  ·
    refine ⟨192699040077892640462764985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128466026718595093641843323 192699040077892640462764985)
    ·
      refine ⟨144524280058419480347073739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192699040077892640462764985 144524280058419480347073739)
      ·
        refine ⟨216786420087629220520610609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144524280058419480347073739 216786420087629220520610609)
        ·
          refine ⟨162589815065721915390457957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216786420087629220520610609 162589815065721915390457957)
          ·
            refine ⟨30485590324822859135710867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162589815065721915390457957 30485590324822859135710867)
            ·
              refine ⟨45728385487234288703566301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30485590324822859135710867 45728385487234288703566301)
              ·
                refine ⟨17148144557712858263837363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45728385487234288703566301 17148144557712858263837363)
                ·
                  refine ⟨25722216836569287395756045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17148144557712858263837363 25722216836569287395756045)
                  ·
                    refine ⟨9645831313713482773408517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25722216836569287395756045 9645831313713482773408517)
                    ·
                      refine ⟨1808593371321278020014097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9645831313713482773408517 1808593371321278020014097)
                      ·
                        rfl

theorem cell23_3522223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_3522223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522223 prefixEnd_3522223 := by exact prefixLift 3522223
  have htrace : WordTrace (prefixWord ++ tailWord_3522223) baseStart_3522223 baseEnd_3522223 := by
    simpa [prefixWord, tailWord_3522223, baseEnd_3522223] using wordTrace_append hprefix tailTrace_3522223
  have hstable : (prefixWord ++ tailWord_3522223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522223).length < 2 ^ (prefixWord ++ tailWord_3522223).sum := by decide
  have hdescent : baseEnd_3522223 < baseStart_3522223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522240 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 4]
def baseStart_3522240 : Nat := 118140960795 + 3522240 * 2 ^ 59
def prefixEnd_3522240 : Nat := 4983230072969 + 3 ^ 40 * 3522240 * 2
def baseEnd_3522240 : Nat := 1808602100492404453501519

theorem tailTrace_3522240 : CollatzResearch.WordTrace tailWord_3522240 prefixEnd_3522240 1808602100492404453501519 := by
  unfold tailWord_3522240
  simp only [CollatzResearch.WordTrace]
  refine ⟨64233323379766752772606087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85644431173022337030141449 64233323379766752772606087)
  ·
    refine ⟨96349985069650129158909131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64233323379766752772606087 96349985069650129158909131)
    ·
      refine ⟨144524977604475193738363697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96349985069650129158909131 144524977604475193738363697)
      ·
        refine ⟨108393733203356395303772773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144524977604475193738363697 108393733203356395303772773)
        ·
          refine ⟨20323824975629324119457395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108393733203356395303772773 20323824975629324119457395)
          ·
            refine ⟨30485737463443986179186093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20323824975629324119457395 30485737463443986179186093)
            ·
              refine ⟨11432151548791494817194785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30485737463443986179186093 11432151548791494817194785)
              ·
                refine ⟨8574113661593621112896089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11432151548791494817194785 8574113661593621112896089)
                ·
                  refine ⟨6430585246195215834672067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8574113661593621112896089 6430585246195215834672067)
                  ·
                    refine ⟨9645877869292823752008101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6430585246195215834672067 9645877869292823752008101)
                    ·
                      refine ⟨1808602100492404453501519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9645877869292823752008101 1808602100492404453501519)
                      ·
                        rfl

theorem cell23_3522240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_3522240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522240 prefixEnd_3522240 := by exact prefixLift 3522240
  have htrace : WordTrace (prefixWord ++ tailWord_3522240) baseStart_3522240 baseEnd_3522240 := by
    simpa [prefixWord, tailWord_3522240, baseEnd_3522240] using wordTrace_append hprefix tailTrace_3522240
  have hstable : (prefixWord ++ tailWord_3522240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522240).length < 2 ^ (prefixWord ++ tailWord_3522240).sum := by decide
  have hdescent : baseEnd_3522240 < baseStart_3522240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522243 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 3]
def baseStart_3522243 : Nat := 118140960795 + 3522243 * 2 ^ 59
def prefixEnd_3522243 : Nat := 4983230072969 + 3 ^ 40 * 3522243 * 2
def baseEnd_3522243 : Nat := 1808603640934367941764005

theorem tailTrace_3522243 : CollatzResearch.WordTrace tailWord_3522243 prefixEnd_3522243 1808603640934367941764005 := by
  unfold tailWord_3522243
  simp only [CollatzResearch.WordTrace]
  refine ⟨128466756178522637057571383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85644504119015091371714255 128466756178522637057571383)
  ·
    refine ⟨192700134267783955586357075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128466756178522637057571383 192700134267783955586357075)
    ·
      refine ⟨289050201401675933379535613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192700134267783955586357075 289050201401675933379535613)
      ·
        refine ⟨108393825525628475017325855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289050201401675933379535613 108393825525628475017325855)
        ·
          refine ⟨162590738288442712525988783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108393825525628475017325855 162590738288442712525988783)
          ·
            refine ⟨243886107432664068788983175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162590738288442712525988783 243886107432664068788983175)
            ·
              refine ⟨365829161148996103183474763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243886107432664068788983175 365829161148996103183474763)
              ·
                refine ⟨548743741723494154775212145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365829161148996103183474763 548743741723494154775212145)
                ·
                  refine ⟨411557806292620616081409109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548743741723494154775212145 411557806292620616081409109)
                  ·
                    refine ⟨4822943042491647844704013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 411557806292620616081409109 4822943042491647844704013)
                    ·
                      refine ⟨1808603640934367941764005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4822943042491647844704013 1808603640934367941764005)
                      ·
                        rfl

theorem cell23_3522243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_3522243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522243 prefixEnd_3522243 := by exact prefixLift 3522243
  have htrace : WordTrace (prefixWord ++ tailWord_3522243) baseStart_3522243 baseEnd_3522243 := by
    simpa [prefixWord, tailWord_3522243, baseEnd_3522243] using wordTrace_append hprefix tailTrace_3522243
  have hstable : (prefixWord ++ tailWord_3522243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522243).length < 2 ^ (prefixWord ++ tailWord_3522243).sum := by decide
  have hdescent : baseEnd_3522243 < baseStart_3522243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522277 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 2, 2, 3]
def baseStart_3522277 : Nat := 118140960795 + 3522277 * 2 ^ 59
def prefixEnd_3522277 : Nat := 4983230072969 + 3 ^ 40 * 3522277 * 2
def baseEnd_3522277 : Nat := 1808621099276620808738849

theorem tailTrace_3522277 : CollatzResearch.WordTrace tailWord_3522277 prefixEnd_3522277 1808621099276620808738849 := by
  unfold tailWord_3522277
  simp only [CollatzResearch.WordTrace]
  refine ⟨128467996260399460864309085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85645330840266307242872723 128467996260399460864309085)
  ·
    refine ⟨48175498597649797824115907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128467996260399460864309085 48175498597649797824115907)
    ·
      refine ⟨72263247896474696736173861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48175498597649797824115907 72263247896474696736173861)
      ·
        refine ⟨13549358980589005638032599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72263247896474696736173861 13549358980589005638032599)
        ·
          refine ⟨20324038470883508457048899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13549358980589005638032599 20324038470883508457048899)
          ·
            refine ⟨30486057706325262685573349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20324038470883508457048899 30486057706325262685573349)
            ·
              refine ⟨5716135819935986753545003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30486057706325262685573349 5716135819935986753545003)
              ·
                refine ⟨8574203729903980130317505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5716135819935986753545003 8574203729903980130317505)
                ·
                  refine ⟨6430652797427985097738129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8574203729903980130317505 6430652797427985097738129)
                  ·
                    refine ⟨4822989598070988823303597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6430652797427985097738129 4822989598070988823303597)
                    ·
                      refine ⟨1808621099276620808738849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4822989598070988823303597 1808621099276620808738849)
                      ·
                        rfl

theorem cell23_3522277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_3522277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522277 prefixEnd_3522277 := by exact prefixLift 3522277
  have htrace : WordTrace (prefixWord ++ tailWord_3522277) baseStart_3522277 baseEnd_3522277 := by
    simpa [prefixWord, tailWord_3522277, baseEnd_3522277] using wordTrace_append hprefix tailTrace_3522277
  have hstable : (prefixWord ++ tailWord_3522277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522277).length < 2 ^ (prefixWord ++ tailWord_3522277).sum := by decide
  have hdescent : baseEnd_3522277 < baseStart_3522277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522341 : List Nat := [1, 3, 1, 2, 3, 3, 2, 3, 1, 1, 3]
def baseStart_3522341 : Nat := 118140960795 + 3522341 * 2 ^ 59
def prefixEnd_3522341 : Nat := 4983230072969 + 3 ^ 40 * 3522341 * 2
def baseEnd_3522341 : Nat := 1808653962038508558338555

theorem tailTrace_3522341 : CollatzResearch.WordTrace tailWord_3522341 prefixEnd_3522341 1808653962038508558338555 := by
  unfold tailWord_3522341
  simp only [CollatzResearch.WordTrace]
  refine ⟨128470330532167599794638877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85646887021445066529759251 128470330532167599794638877)
  ·
    refine ⟨48176373949562849922989579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128470330532167599794638877 48176373949562849922989579)
    ·
      refine ⟨72264560924344274884484369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48176373949562849922989579 72264560924344274884484369)
      ·
        refine ⟨54198420693258206163363277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72264560924344274884484369 54198420693258206163363277)
        ·
          refine ⟨20324407759971827311261229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54198420693258206163363277 20324407759971827311261229)
          ·
            refine ⟨7621652909989435241722961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20324407759971827311261229 7621652909989435241722961)
            ·
              refine ⟨5716239682492076431292221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7621652909989435241722961 5716239682492076431292221)
              ·
                refine ⟨2143589880934528661734583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5716239682492076431292221 2143589880934528661734583)
                ·
                  refine ⟨3215384821401792992601875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143589880934528661734583 3215384821401792992601875)
                  ·
                    refine ⟨4823077232102689488902813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3215384821401792992601875 4823077232102689488902813)
                    ·
                      refine ⟨1808653962038508558338555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4823077232102689488902813 1808653962038508558338555)
                      ·
                        rfl

theorem cell23_3522341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_3522341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522341 prefixEnd_3522341 := by exact prefixLift 3522341
  have htrace : WordTrace (prefixWord ++ tailWord_3522341) baseStart_3522341 baseEnd_3522341 := by
    simpa [prefixWord, tailWord_3522341, baseEnd_3522341] using wordTrace_append hprefix tailTrace_3522341
  have hstable : (prefixWord ++ tailWord_3522341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522341).length < 2 ^ (prefixWord ++ tailWord_3522341).sum := by decide
  have hdescent : baseEnd_3522341 < baseStart_3522341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522344 : List Nat := [2, 1, 5, 1, 1, 2, 4, 1, 1, 5]
def baseStart_3522344 : Nat := 118140960795 + 3522344 * 2 ^ 59
def prefixEnd_3522344 : Nat := 4983230072969 + 3 ^ 40 * 3522344 * 2
def baseEnd_3522344 : Nat := 602885167493490682200347

theorem tailTrace_3522344 : CollatzResearch.WordTrace tailWord_3522344 prefixEnd_3522344 602885167493490682200347 := by
  unfold tailWord_3522344
  simp only [CollatzResearch.WordTrace]
  refine ⟨64235219975578365653499043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85646959967437820871332057 64235219975578365653499043)
  ·
    refine ⟨96352829963367548480248565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64235219975578365653499043 96352829963367548480248565)
    ·
      refine ⟨9033077809065707670023303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96352829963367548480248565 9033077809065707670023303)
      ·
        refine ⟨13549616713598561505034955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9033077809065707670023303 13549616713598561505034955)
        ·
          refine ⟨20324425070397842257552433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13549616713598561505034955 20324425070397842257552433)
          ·
            refine ⟨15243318802798381693164325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20324425070397842257552433 15243318802798381693164325)
            ·
              refine ⟨2858122275524696567468311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15243318802798381693164325 2858122275524696567468311)
              ·
                refine ⟨4287183413287044851202467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2858122275524696567468311 4287183413287044851202467)
                ·
                  refine ⟨6430775119930567276803701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4287183413287044851202467 6430775119930567276803701)
                  ·
                    refine ⟨602885167493490682200347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6430775119930567276803701 602885167493490682200347)
                    ·
                      rfl

theorem cell23_3522344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_3522344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522344 prefixEnd_3522344 := by exact prefixLift 3522344
  have htrace : WordTrace (prefixWord ++ tailWord_3522344) baseStart_3522344 baseEnd_3522344 := by
    simpa [prefixWord, tailWord_3522344, baseEnd_3522344] using wordTrace_append hprefix tailTrace_3522344
  have hstable : (prefixWord ++ tailWord_3522344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522344).length < 2 ^ (prefixWord ++ tailWord_3522344).sum := by decide
  have hdescent : baseEnd_3522344 < baseStart_3522344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522358 : List Nat := [5, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_3522358 : Nat := 118140960795 + 3522358 * 2 ^ 59
def prefixEnd_3522358 : Nat := 4983230072969 + 3 ^ 40 * 3522358 * 2
def baseEnd_3522358 : Nat := 1808662691209634991825977

theorem tailTrace_3522358 : CollatzResearch.WordTrace tailWord_3522358 prefixEnd_3522358 1808662691209634991825977 := by
  unfold tailWord_3522358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8029434410819125731125483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85647300382070674465338485 8029434410819125731125483)
  ·
    refine ⟨12044151616228688596688225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8029434410819125731125483 12044151616228688596688225)
    ·
      refine ⟨9033113712171516447516169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12044151616228688596688225 9033113712171516447516169)
      ·
        refine ⟨6774835284128637335637127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9033113712171516447516169 6774835284128637335637127)
        ·
          refine ⟨10162252926192956003455691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6774835284128637335637127 10162252926192956003455691)
          ·
            refine ⟨15243379389289434005183537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10162252926192956003455691 15243379389289434005183537)
            ·
              refine ⟨11432534541967075503887653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15243379389289434005183537 11432534541967075503887653)
              ·
                refine ⟨2143600226618826656978935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11432534541967075503887653 2143600226618826656978935)
                ·
                  refine ⟨3215400339928239985468403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143600226618826656978935 3215400339928239985468403)
                  ·
                    refine ⟨4823100509892359978202605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3215400339928239985468403 4823100509892359978202605)
                    ·
                      refine ⟨1808662691209634991825977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4823100509892359978202605 1808662691209634991825977)
                      ·
                        rfl

theorem cell23_3522358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_3522358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522358 prefixEnd_3522358 := by exact prefixLift 3522358
  have htrace : WordTrace (prefixWord ++ tailWord_3522358) baseStart_3522358 baseEnd_3522358 := by
    simpa [prefixWord, tailWord_3522358, baseEnd_3522358] using wordTrace_append hprefix tailTrace_3522358
  have hstable : (prefixWord ++ tailWord_3522358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522358).length < 2 ^ (prefixWord ++ tailWord_3522358).sum := by decide
  have hdescent : baseEnd_3522358 < baseStart_3522358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522364 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 3, 2, 2]
def baseStart_3522364 : Nat := 118140960795 + 3522364 * 2 ^ 59
def prefixEnd_3522364 : Nat := 4983230072969 + 3 ^ 40 * 3522364 * 2
def baseEnd_3522364 : Nat := 1808665772093561968350949

theorem tailTrace_3522364 : CollatzResearch.WordTrace tailWord_3522364 prefixEnd_3522364 1808665772093561968350949 := by
  unfold tailWord_3522364
  simp only [CollatzResearch.WordTrace]
  refine ⟨64235584705542137361363073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85647446274056183148484097 64235584705542137361363073)
  ·
    refine ⟨48176688529156603021022305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64235584705542137361363073 48176688529156603021022305)
    ·
      refine ⟨36132516396867452265766729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48176688529156603021022305 36132516396867452265766729)
      ·
        refine ⟨27099387297650589199325047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36132516396867452265766729 27099387297650589199325047)
        ·
          refine ⟨40649080946475883798987571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27099387297650589199325047 40649080946475883798987571)
          ·
            refine ⟨60973621419713825698481357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40649080946475883798987571 60973621419713825698481357)
            ·
              refine ⟨22865108032392684636930509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60973621419713825698481357 22865108032392684636930509)
              ·
                refine ⟨8574415512147256738848941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22865108032392684636930509 8574415512147256738848941)
                ·
                  refine ⟨3215405817055221277068353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8574415512147256738848941 3215405817055221277068353)
                  ·
                    refine ⟨2411554362791415957801265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3215405817055221277068353 2411554362791415957801265)
                    ·
                      refine ⟨1808665772093561968350949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2411554362791415957801265 1808665772093561968350949)
                      ·
                        rfl

theorem cell23_3522364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_3522364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522364 prefixEnd_3522364 := by exact prefixLift 3522364
  have htrace : WordTrace (prefixWord ++ tailWord_3522364) baseStart_3522364 baseEnd_3522364 := by
    simpa [prefixWord, tailWord_3522364, baseEnd_3522364] using wordTrace_append hprefix tailTrace_3522364
  have hstable : (prefixWord ++ tailWord_3522364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522364).length < 2 ^ (prefixWord ++ tailWord_3522364).sum := by decide
  have hdescent : baseEnd_3522364 < baseStart_3522364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522367 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 5]
def baseStart_3522367 : Nat := 118140960795 + 3522367 * 2 ^ 59
def prefixEnd_3522367 : Nat := 4983230072969 + 3 ^ 40 * 3522367 * 2
def baseEnd_3522367 : Nat := 1808667312535525456613435

theorem tailTrace_3522367 : CollatzResearch.WordTrace tailWord_3522367 prefixEnd_3522367 1808667312535525456613435 := by
  unfold tailWord_3522367
  simp only [CollatzResearch.WordTrace]
  refine ⟨128471278830073406235085355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85647519220048937490056903 128471278830073406235085355)
  ·
    refine ⟨192706918245110109352628033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128471278830073406235085355 192706918245110109352628033)
    ·
      refine ⟨144530188683832582014471025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192706918245110109352628033 144530188683832582014471025)
      ·
        refine ⟨108397641512874436510853269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144530188683832582014471025 108397641512874436510853269)
        ·
          refine ⟨5081139445915989211446247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108397641512874436510853269 5081139445915989211446247)
          ·
            refine ⟨7621709168873983817169371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5081139445915989211446247 7621709168873983817169371)
            ·
              refine ⟨11432563753310975725754057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7621709168873983817169371 11432563753310975725754057)
              ·
                refine ⟨8574422814983231794315543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11432563753310975725754057 8574422814983231794315543)
                ·
                  refine ⟨12861634222474847691473315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8574422814983231794315543 12861634222474847691473315)
                  ·
                    refine ⟨19292451333712271537209973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12861634222474847691473315 19292451333712271537209973)
                    ·
                      refine ⟨1808667312535525456613435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19292451333712271537209973 1808667312535525456613435)
                      ·
                        rfl

theorem cell23_3522367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_3522367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522367 prefixEnd_3522367 := by exact prefixLift 3522367
  have htrace : WordTrace (prefixWord ++ tailWord_3522367) baseStart_3522367 baseEnd_3522367 := by
    simpa [prefixWord, tailWord_3522367, baseEnd_3522367] using wordTrace_append hprefix tailTrace_3522367
  have hstable : (prefixWord ++ tailWord_3522367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522367).length < 2 ^ (prefixWord ++ tailWord_3522367).sum := by decide
  have hdescent : baseEnd_3522367 < baseStart_3522367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522381 : List Nat := [1, 6, 1, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_3522381 : Nat := 118140960795 + 3522381 * 2 ^ 59
def prefixEnd_3522381 : Nat := 4983230072969 + 3 ^ 40 * 3522381 * 2
def baseEnd_3522381 : Nat := 1808674501264688401838371

theorem tailTrace_3522381 : CollatzResearch.WordTrace tailWord_3522381 prefixEnd_3522381 1808674501264688401838371 := by
  unfold tailWord_3522381
  simp only [CollatzResearch.WordTrace]
  refine ⟨128471789452022686626094997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85647859634681791084063331 128471789452022686626094997)
  ·
    refine ⟨6022115130563563435598203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128471789452022686626094997 6022115130563563435598203)
    ·
      refine ⟨9033172695845345153397305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6022115130563563435598203 9033172695845345153397305)
      ·
        refine ⟨6774879521884008865047979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9033172695845345153397305 6774879521884008865047979)
        ·
          refine ⟨10162319282826013297571969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6774879521884008865047979 10162319282826013297571969)
          ·
            refine ⟨7621739462119509973178977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10162319282826013297571969 7621739462119509973178977)
            ·
              refine ⟨5716304596589632479884233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7621739462119509973178977 5716304596589632479884233)
              ·
                refine ⟨4287228447442224359913175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5716304596589632479884233 4287228447442224359913175)
                ·
                  refine ⟨6430842671163336539869763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4287228447442224359913175 6430842671163336539869763)
                  ·
                    refine ⟨9646264006745004809804645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6430842671163336539869763 9646264006745004809804645)
                    ·
                      refine ⟨1808674501264688401838371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9646264006745004809804645 1808674501264688401838371)
                      ·
                        rfl

theorem cell23_3522381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_3522381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522381 prefixEnd_3522381 := by exact prefixLift 3522381
  have htrace : WordTrace (prefixWord ++ tailWord_3522381) baseStart_3522381 baseEnd_3522381 := by
    simpa [prefixWord, tailWord_3522381, baseEnd_3522381] using wordTrace_append hprefix tailTrace_3522381
  have hstable : (prefixWord ++ tailWord_3522381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522381).length < 2 ^ (prefixWord ++ tailWord_3522381).sum := by decide
  have hdescent : baseEnd_3522381 < baseStart_3522381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522458 : List Nat := [3, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2]
def baseStart_3522458 : Nat := 118140960795 + 3522458 * 2 ^ 59
def prefixEnd_3522458 : Nat := 4983230072969 + 3 ^ 40 * 3522458 * 2
def baseEnd_3522458 : Nat := 1808714039275084600575517

theorem tailTrace_3522458 : CollatzResearch.WordTrace tailWord_3522458 prefixEnd_3522458 1808714039275084600575517 := by
  unfold tailWord_3522458
  simp only [CollatzResearch.WordTrace]
  refine ⟨32118649468185932194162007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85649731915162485851098685 32118649468185932194162007)
  ·
    refine ⟨48177974202278898291243011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32118649468185932194162007 48177974202278898291243011)
    ·
      refine ⟨72266961303418347436864517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48177974202278898291243011 72266961303418347436864517)
      ·
        refine ⟨13550055244390940144412097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72266961303418347436864517 13550055244390940144412097)
        ·
          refine ⟨10162541433293205108309073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13550055244390940144412097 10162541433293205108309073)
          ·
            refine ⟨7621906074969903831231805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10162541433293205108309073 7621906074969903831231805)
            ·
              refine ⟨2858214778113713936711927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7621906074969903831231805 2858214778113713936711927)
              ·
                refine ⟨4287322167170570905067891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2858214778113713936711927 4287322167170570905067891)
                ·
                  refine ⟨6430983250755856357601837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4287322167170570905067891 6430983250755856357601837)
                  ·
                    refine ⟨2411618719033446134100689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6430983250755856357601837 2411618719033446134100689)
                    ·
                      refine ⟨1808714039275084600575517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2411618719033446134100689 1808714039275084600575517)
                      ·
                        rfl

theorem cell23_3522458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_3522458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522458 prefixEnd_3522458 := by exact prefixLift 3522458
  have htrace : WordTrace (prefixWord ++ tailWord_3522458) baseStart_3522458 baseEnd_3522458 := by
    simpa [prefixWord, tailWord_3522458, baseEnd_3522458] using wordTrace_append hprefix tailTrace_3522458
  have hstable : (prefixWord ++ tailWord_3522458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522458).length < 2 ^ (prefixWord ++ tailWord_3522458).sum := by decide
  have hdescent : baseEnd_3522458 < baseStart_3522458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522544 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 2, 4, 2]
def baseStart_3522544 : Nat := 118140960795 + 3522544 * 2 ^ 59
def prefixEnd_3522544 : Nat := 4983230072969 + 3 ^ 40 * 3522544 * 2
def baseEnd_3522544 : Nat := 1808758198611371264100121

theorem tailTrace_3522544 : CollatzResearch.WordTrace tailWord_3522544 prefixEnd_3522544 1808758198611371264100121 := by
  unfold tailWord_3522544
  simp only [CollatzResearch.WordTrace]
  refine ⟨64238867275216082732139343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85651823033621443642852457 64238867275216082732139343)
  ·
    refine ⟨96358300912824124098209015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64238867275216082732139343 96358300912824124098209015)
    ·
      refine ⟨144537451369236186147313523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96358300912824124098209015 144537451369236186147313523)
      ·
        refine ⟨216806177053854279220970285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144537451369236186147313523 216806177053854279220970285)
        ·
          refine ⟨81302316395195354707863857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216806177053854279220970285 81302316395195354707863857)
          ·
            refine ⟨60976737296396516030897893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81302316395195354707863857 60976737296396516030897893)
            ·
              refine ⟨11433138243074346755793355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60976737296396516030897893 11433138243074346755793355)
              ·
                refine ⟨17149707364611520133690033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11433138243074346755793355 17149707364611520133690033)
                ·
                  refine ⟨12862280523458640100267525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17149707364611520133690033 12862280523458640100267525)
                  ·
                    refine ⟨2411677598148495018800161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12862280523458640100267525 2411677598148495018800161)
                    ·
                      refine ⟨1808758198611371264100121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2411677598148495018800161 1808758198611371264100121)
                      ·
                        rfl

theorem cell23_3522544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 2, 4, 2].length) (baseStart_3522544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522544 prefixEnd_3522544 := by exact prefixLift 3522544
  have htrace : WordTrace (prefixWord ++ tailWord_3522544) baseStart_3522544 baseEnd_3522544 := by
    simpa [prefixWord, tailWord_3522544, baseEnd_3522544] using wordTrace_append hprefix tailTrace_3522544
  have hstable : (prefixWord ++ tailWord_3522544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522544).length < 2 ^ (prefixWord ++ tailWord_3522544).sum := by decide
  have hdescent : baseEnd_3522544 < baseStart_3522544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522567 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 8]
def baseStart_3522567 : Nat := 118140960795 + 3522567 * 2 ^ 59
def prefixEnd_3522567 : Nat := 4983230072969 + 3 ^ 40 * 3522567 * 2
def baseEnd_3522567 : Nat := 200974445407380519345835

theorem tailTrace_3522567 : CollatzResearch.WordTrace tailWord_3522567 prefixEnd_3522567 200974445407380519345835 := by
  unfold tailWord_3522567
  simp only [CollatzResearch.WordTrace]
  refine ⟨128478573429348840392365955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85652382286232560261577303 128478573429348840392365955)
  ·
    refine ⟨192717860144023260588548933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128478573429348840392365955 192717860144023260588548933)
    ·
      refine ⟨36134598777004361360352925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192717860144023260588548933 36134598777004361360352925)
      ·
        refine ⟨13550474541376635510132347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36134598777004361360352925 13550474541376635510132347)
        ·
          refine ⟨20325711812064953265198521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13550474541376635510132347 20325711812064953265198521)
          ·
            refine ⟨15244283859048714948898891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20325711812064953265198521 15244283859048714948898891)
            ·
              refine ⟨22866425788573072423348337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15244283859048714948898891 22866425788573072423348337)
              ·
                refine ⟨17149819341429804317511253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22866425788573072423348337 17149819341429804317511253)
                ·
                  refine ⟨200974445407380519345835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17149819341429804317511253 200974445407380519345835)
                  ·
                    rfl

theorem cell23_3522567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 8].length) (baseStart_3522567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522567 prefixEnd_3522567 := by exact prefixLift 3522567
  have htrace : WordTrace (prefixWord ++ tailWord_3522567) baseStart_3522567 baseEnd_3522567 := by
    simpa [prefixWord, tailWord_3522567, baseEnd_3522567] using wordTrace_append hprefix tailTrace_3522567
  have hstable : (prefixWord ++ tailWord_3522567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522567).length < 2 ^ (prefixWord ++ tailWord_3522567).sum := by decide
  have hdescent : baseEnd_3522567 < baseStart_3522567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522581 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 2, 2, 3]
def baseStart_3522581 : Nat := 118140960795 + 3522581 * 2 ^ 59
def prefixEnd_3522581 : Nat := 4983230072969 + 3 ^ 40 * 3522581 * 2
def baseEnd_3522581 : Nat := 1808777197395587619337451

theorem tailTrace_3522581 : CollatzResearch.WordTrace tailWord_3522581 prefixEnd_3522581 1808777197395587619337451 := by
  unfold tailWord_3522581
  simp only [CollatzResearch.WordTrace]
  refine ⟨128479084051298120783375597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85652722700865413855583731 128479084051298120783375597)
  ·
    refine ⟨48179656519236795293765849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128479084051298120783375597 48179656519236795293765849)
    ·
      refine ⟨36134742389427596470324387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48179656519236795293765849 36134742389427596470324387)
      ·
        refine ⟨54202113584141394705486581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36134742389427596470324387 54202113584141394705486581)
        ·
          refine ⟨5081448148513255753639367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54202113584141394705486581 5081448148513255753639367)
          ·
            refine ⟨7622172222769883630459051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5081448148513255753639367 7622172222769883630459051)
            ·
              refine ⟨11433258334154825445688577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7622172222769883630459051 11433258334154825445688577)
              ·
                refine ⟨8574943750616119084266433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11433258334154825445688577 8574943750616119084266433)
                ·
                  refine ⟨6431207812962089313199825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8574943750616119084266433 6431207812962089313199825)
                  ·
                    refine ⟨4823405859721566984899869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6431207812962089313199825 4823405859721566984899869)
                    ·
                      refine ⟨1808777197395587619337451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4823405859721566984899869 1808777197395587619337451)
                      ·
                        rfl

theorem cell23_3522581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_3522581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522581 prefixEnd_3522581 := by exact prefixLift 3522581
  have htrace : WordTrace (prefixWord ++ tailWord_3522581) baseStart_3522581 baseEnd_3522581 := by
    simpa [prefixWord, tailWord_3522581, baseEnd_3522581] using wordTrace_append hprefix tailTrace_3522581
  have hstable : (prefixWord ++ tailWord_3522581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522581).length < 2 ^ (prefixWord ++ tailWord_3522581).sum := by decide
  have hdescent : baseEnd_3522581 < baseStart_3522581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522604 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 1, 5, 2]
def baseStart_3522604 : Nat := 118140960795 + 3522604 * 2 ^ 59
def prefixEnd_3522604 : Nat := 4983230072969 + 3 ^ 40 * 3522604 * 2
def baseEnd_3522604 : Nat := 1808789007450641029349845

theorem tailTrace_3522604 : CollatzResearch.WordTrace tailWord_3522604 prefixEnd_3522604 1808789007450641029349845 := by
  unfold tailWord_3522604
  simp only [CollatzResearch.WordTrace]
  refine ⟨64239961465107397855731433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85653281953476530474308577 64239961465107397855731433)
  ·
    refine ⟨48179971098830548391798575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64239961465107397855731433 48179971098830548391798575)
    ·
      refine ⟨72269956648245822587697863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48179971098830548391798575 72269956648245822587697863)
      ·
        refine ⟨108404934972368733881546795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72269956648245822587697863 108404934972368733881546795)
        ·
          refine ⟨162607402458553100822320193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108404934972368733881546795 162607402458553100822320193)
          ·
            refine ⟨121955551843914825616740145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162607402458553100822320193 121955551843914825616740145)
            ·
              refine ⟨91466663882936119212555109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121955551843914825616740145 91466663882936119212555109)
              ·
                refine ⟨17149999478050522352354083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91466663882936119212555109 17149999478050522352354083)
                ·
                  refine ⟨25724999217075783528531125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17149999478050522352354083 25724999217075783528531125)
                  ·
                    refine ⟨2411718676600854705799793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25724999217075783528531125 2411718676600854705799793)
                    ·
                      refine ⟨1808789007450641029349845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2411718676600854705799793 1808789007450641029349845)
                      ·
                        rfl

theorem cell23_3522604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 5, 2].length) (baseStart_3522604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522604 prefixEnd_3522604 := by exact prefixLift 3522604
  have htrace : WordTrace (prefixWord ++ tailWord_3522604) baseStart_3522604 baseEnd_3522604 := by
    simpa [prefixWord, tailWord_3522604, baseEnd_3522604] using wordTrace_append hprefix tailTrace_3522604
  have hstable : (prefixWord ++ tailWord_3522604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522604).length < 2 ^ (prefixWord ++ tailWord_3522604).sum := by decide
  have hdescent : baseEnd_3522604 < baseStart_3522604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522631 : List Nat := [1, 1, 4, 1, 3, 1, 5, 1, 1, 5]
def baseStart_3522631 : Nat := 118140960795 + 3522631 * 2 ^ 59
def prefixEnd_3522631 : Nat := 4983230072969 + 3 ^ 40 * 3522631 * 2
def baseEnd_3522631 : Nat := 602934290476104141237407

theorem tailTrace_3522631 : CollatzResearch.WordTrace tailWord_3522631 prefixEnd_3522631 602934290476104141237407 := by
  unfold tailWord_3522631
  simp only [CollatzResearch.WordTrace]
  refine ⟨128480907701116979322695747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85653938467411319548463831 128480907701116979322695747)
  ·
    refine ⟨192721361551675468984043621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128480907701116979322695747 192721361551675468984043621)
    ·
      refine ⟨36135255290939150434508179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192721361551675468984043621 36135255290939150434508179)
      ·
        refine ⟨54202882936408725651762269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36135255290939150434508179 54202882936408725651762269)
        ·
          refine ⟨20326081101153272119410851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54202882936408725651762269 20326081101153272119410851)
          ·
            refine ⟨30489121651729908179116277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20326081101153272119410851 30489121651729908179116277)
            ·
              refine ⟨2858355154849678891792151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30489121651729908179116277 2858355154849678891792151)
              ·
                refine ⟨4287532732274518337688227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2858355154849678891792151 4287532732274518337688227)
                ·
                  refine ⟨6431299098411777506532341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4287532732274518337688227 6431299098411777506532341)
                  ·
                    refine ⟨602934290476104141237407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6431299098411777506532341 602934290476104141237407)
                    ·
                      rfl

theorem cell23_3522631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_3522631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522631 prefixEnd_3522631 := by exact prefixLift 3522631
  have htrace : WordTrace (prefixWord ++ tailWord_3522631) baseStart_3522631 baseEnd_3522631 := by
    simpa [prefixWord, tailWord_3522631, baseEnd_3522631] using wordTrace_append hprefix tailTrace_3522631
  have hstable : (prefixWord ++ tailWord_3522631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522631).length < 2 ^ (prefixWord ++ tailWord_3522631).sum := by decide
  have hdescent : baseEnd_3522631 < baseStart_3522631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522645 : List Nat := [1, 3, 2, 2, 1, 3, 4, 2, 1, 1, 3]
def baseStart_3522645 : Nat := 118140960795 + 3522645 * 2 ^ 59
def prefixEnd_3522645 : Nat := 4983230072969 + 3 ^ 40 * 3522645 * 2
def baseEnd_3522645 : Nat := 1808810060157475368937157

theorem tailTrace_3522645 : CollatzResearch.WordTrace tailWord_3522645 prefixEnd_3522645 1808810060157475368937157 := by
  unfold tailWord_3522645
  simp only [CollatzResearch.WordTrace]
  refine ⟨128481418323066259713705389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85654278882044173142470259 128481418323066259713705389)
  ·
    refine ⟨48180531871149847392639521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128481418323066259713705389 48180531871149847392639521)
    ·
      refine ⟨36135398903362385544479641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48180531871149847392639521 36135398903362385544479641)
      ·
        refine ⟨27101549177521789158359731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36135398903362385544479641 27101549177521789158359731)
        ·
          refine ⟨40652323766282683737539597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27101549177521789158359731 40652323766282683737539597)
          ·
            refine ⟨15244621412356006401577349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40652323766282683737539597 15244621412356006401577349)
            ·
              refine ⟨2858366514816751200295753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15244621412356006401577349 2858366514816751200295753)
              ·
                refine ⟨2143774886112563400221815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2858366514816751200295753 2143774886112563400221815)
                ·
                  refine ⟨3215662329168845100332723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143774886112563400221815 3215662329168845100332723)
                  ·
                    refine ⟨4823493493753267650499085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3215662329168845100332723 4823493493753267650499085)
                    ·
                      refine ⟨1808810060157475368937157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4823493493753267650499085 1808810060157475368937157)
                      ·
                        rfl

theorem cell23_3522645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_3522645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522645 prefixEnd_3522645 := by exact prefixLift 3522645
  have htrace : WordTrace (prefixWord ++ tailWord_3522645) baseStart_3522645 baseEnd_3522645 := by
    simpa [prefixWord, tailWord_3522645, baseEnd_3522645] using wordTrace_append hprefix tailTrace_3522645
  have hstable : (prefixWord ++ tailWord_3522645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522645).length < 2 ^ (prefixWord ++ tailWord_3522645).sum := by decide
  have hdescent : baseEnd_3522645 < baseStart_3522645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522647 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 6]
def baseStart_3522647 : Nat := 118140960795 + 3522647 * 2 ^ 59
def prefixEnd_3522647 : Nat := 4983230072969 + 3 ^ 40 * 3522647 * 2
def baseEnd_3522647 : Nat := 1808811087118784361112147

theorem tailTrace_3522647 : CollatzResearch.WordTrace tailWord_3522647 prefixEnd_3522647 1808811087118784361112147 := by
  unfold tailWord_3522647
  simp only [CollatzResearch.WordTrace]
  refine ⟨128481491269059014055278195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85654327512706009370185463 128481491269059014055278195)
  ·
    refine ⟨192722236903588521082917293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128481491269059014055278195 192722236903588521082917293)
    ·
      refine ⟨72270838838845695406093985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192722236903588521082917293 72270838838845695406093985)
      ·
        refine ⟨54203129129134271554570489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72270838838845695406093985 54203129129134271554570489)
        ·
          refine ⟨40652346846850703665927867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54203129129134271554570489 40652346846850703665927867)
          ·
            refine ⟨60978520270276055498891801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40652346846850703665927867 60978520270276055498891801)
            ·
              refine ⟨45733890202707041624168851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60978520270276055498891801 45733890202707041624168851)
              ·
                refine ⟨68600835304060562436253277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45733890202707041624168851 68600835304060562436253277)
                ·
                  refine ⟨25725313239022710913594979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68600835304060562436253277 25725313239022710913594979)
                  ·
                    refine ⟨38587969858534066370392469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25725313239022710913594979 38587969858534066370392469)
                    ·
                      refine ⟨1808811087118784361112147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38587969858534066370392469 1808811087118784361112147)
                      ·
                        rfl

theorem cell23_3522647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_3522647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522647 prefixEnd_3522647 := by exact prefixLift 3522647
  have htrace : WordTrace (prefixWord ++ tailWord_3522647) baseStart_3522647 baseEnd_3522647 := by
    simpa [prefixWord, tailWord_3522647, baseEnd_3522647] using wordTrace_append hprefix tailTrace_3522647
  have hstable : (prefixWord ++ tailWord_3522647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522647).length < 2 ^ (prefixWord ++ tailWord_3522647).sum := by decide
  have hdescent : baseEnd_3522647 < baseStart_3522647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522661 : List Nat := [1, 3, 1, 3, 2, 2, 2, 3, 2, 4]
def baseStart_3522661 : Nat := 118140960795 + 3522661 * 2 ^ 59
def prefixEnd_3522661 : Nat := 4983230072969 + 3 ^ 40 * 3522661 * 2
def baseEnd_3522661 : Nat := 602939425282649102112361

theorem tailTrace_3522661 : CollatzResearch.WordTrace tailWord_3522661 prefixEnd_3522661 602939425282649102112361 := by
  unfold tailWord_3522661
  simp only [CollatzResearch.WordTrace]
  refine ⟨128482001891008294446287837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85654667927338862964191891 128482001891008294446287837)
  ·
    refine ⟨48180750709128110417357939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128482001891008294446287837 48180750709128110417357939)
    ·
      refine ⟨72271126063692165626036909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48180750709128110417357939 72271126063692165626036909)
      ·
        refine ⟨27101672273884562109763841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72271126063692165626036909 27101672273884562109763841)
        ·
          refine ⟨20326254205413421582322881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27101672273884562109763841 20326254205413421582322881)
          ·
            refine ⟨15244690654060066186742161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20326254205413421582322881 15244690654060066186742161)
            ·
              refine ⟨11433517990545049640056621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15244690654060066186742161 11433517990545049640056621)
              ·
                refine ⟨4287569246454393615021233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11433517990545049640056621 4287569246454393615021233)
                ·
                  refine ⟨3215676934840795211265925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4287569246454393615021233 3215676934840795211265925)
                  ·
                    refine ⟨602939425282649102112361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3215676934840795211265925 602939425282649102112361)
                    ·
                      rfl

theorem cell23_3522661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_3522661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522661 prefixEnd_3522661 := by exact prefixLift 3522661
  have htrace : WordTrace (prefixWord ++ tailWord_3522661) baseStart_3522661 baseEnd_3522661 := by
    simpa [prefixWord, tailWord_3522661, baseEnd_3522661] using wordTrace_append hprefix tailTrace_3522661
  have hstable : (prefixWord ++ tailWord_3522661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522661).length < 2 ^ (prefixWord ++ tailWord_3522661).sum := by decide
  have hdescent : baseEnd_3522661 < baseStart_3522661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522668 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 3, 2, 2]
def baseStart_3522668 : Nat := 118140960795 + 3522668 * 2 ^ 59
def prefixEnd_3522668 : Nat := 4983230072969 + 3 ^ 40 * 3522668 * 2
def baseEnd_3522668 : Nat := 1808821870212528778949551

theorem tailTrace_3522668 : CollatzResearch.WordTrace tailWord_3522668 prefixEnd_3522668 1808821870212528778949551 := by
  unfold tailWord_3522668
  simp only [CollatzResearch.WordTrace]
  refine ⟨64241128600991467320896329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85654838134655289761195105 64241128600991467320896329)
  ·
    refine ⟨48180846450743600490672247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64241128600991467320896329 48180846450743600490672247)
    ·
      refine ⟨72271269676115400736008371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48180846450743600490672247 72271269676115400736008371)
      ·
        refine ⟨108406904514173101104012557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72271269676115400736008371 108406904514173101104012557)
        ·
          refine ⟨40652589192814912914004709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108406904514173101104012557 40652589192814912914004709)
          ·
            refine ⟨7622360473652796171375883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40652589192814912914004709 7622360473652796171375883)
            ·
              refine ⟨11433540710479194257063825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7622360473652796171375883 11433540710479194257063825)
              ·
                refine ⟨8575155532859395692797869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11433540710479194257063825 8575155532859395692797869)
                ·
                  refine ⟨3215683324822273384799201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8575155532859395692797869 3215683324822273384799201)
                  ·
                    refine ⟨2411762493616705038599401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3215683324822273384799201 2411762493616705038599401)
                    ·
                      refine ⟨1808821870212528778949551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2411762493616705038599401 1808821870212528778949551)
                      ·
                        rfl

theorem cell23_3522668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 2, 2].length) (baseStart_3522668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522668 prefixEnd_3522668 := by exact prefixLift 3522668
  have htrace : WordTrace (prefixWord ++ tailWord_3522668) baseStart_3522668 baseEnd_3522668 := by
    simpa [prefixWord, tailWord_3522668, baseEnd_3522668] using wordTrace_append hprefix tailTrace_3522668
  have hstable : (prefixWord ++ tailWord_3522668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522668).length < 2 ^ (prefixWord ++ tailWord_3522668).sum := by decide
  have hdescent : baseEnd_3522668 < baseStart_3522668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522685 : List Nat := [1, 4, 1, 1, 3, 2, 1, 5, 1, 2, 2]
def baseStart_3522685 : Nat := 118140960795 + 3522685 * 2 ^ 59
def prefixEnd_3522685 : Nat := 4983230072969 + 3 ^ 40 * 3522685 * 2
def baseEnd_3522685 : Nat := 1808830599383655212436973

theorem tailTrace_3522685 : CollatzResearch.WordTrace tailWord_3522685 prefixEnd_3522685 1808830599383655212436973 := by
  unfold tailWord_3522685
  simp only [CollatzResearch.WordTrace]
  refine ⟨128482877242921346545161509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85655251495280897696774339 128482877242921346545161509)
  ·
    refine ⟨24090539483047752477217783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128482877242921346545161509 24090539483047752477217783)
    ·
      refine ⟨36135809224571628715826675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24090539483047752477217783 36135809224571628715826675)
      ·
        refine ⟨54203713836857443073740013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36135809224571628715826675 54203713836857443073740013)
        ·
          refine ⟨20326392688821541152652505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54203713836857443073740013 20326392688821541152652505)
          ·
            refine ⟨15244794516616155864489379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20326392688821541152652505 15244794516616155864489379)
            ·
              refine ⟨22867191774924233796734069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15244794516616155864489379 22867191774924233796734069)
              ·
                refine ⟨2143799228899146918443819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22867191774924233796734069 2143799228899146918443819)
                ·
                  refine ⟨3215698843348720377665729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143799228899146918443819 3215698843348720377665729)
                  ·
                    refine ⟨2411774132511540283249297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3215698843348720377665729 2411774132511540283249297)
                    ·
                      refine ⟨1808830599383655212436973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2411774132511540283249297 1808830599383655212436973)
                      ·
                        rfl

theorem cell23_3522685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_3522685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522685 prefixEnd_3522685 := by exact prefixLift 3522685
  have htrace : WordTrace (prefixWord ++ tailWord_3522685) baseStart_3522685 baseEnd_3522685 := by
    simpa [prefixWord, tailWord_3522685, baseEnd_3522685] using wordTrace_append hprefix tailTrace_3522685
  have hstable : (prefixWord ++ tailWord_3522685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522685).length < 2 ^ (prefixWord ++ tailWord_3522685).sum := by decide
  have hdescent : baseEnd_3522685 < baseStart_3522685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522744 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 2, 1, 5]
def baseStart_3522744 : Nat := 118140960795 + 3522744 * 2 ^ 59
def prefixEnd_3522744 : Nat := 4983230072969 + 3 ^ 40 * 3522744 * 2
def baseEnd_3522744 : Nat := 1808860894742270481599201

theorem tailTrace_3522744 : CollatzResearch.WordTrace tailWord_3522744 prefixEnd_3522744 1808860894742270481599201 := by
  unfold tailWord_3522744
  simp only [CollatzResearch.WordTrace]
  refine ⟨64242514574853799810779643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85656686099805066414372857 64242514574853799810779643)
  ·
    refine ⟨96363771862280699716169465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64242514574853799810779643 96363771862280699716169465)
    ·
      refine ⟨72272828896710524787127099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96363771862280699716169465 72272828896710524787127099)
      ·
        refine ⟨108409243345065787180690649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72272828896710524787127099 108409243345065787180690649)
        ·
          refine ⟨81306932508799340385517987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108409243345065787180690649 81306932508799340385517987)
          ·
            refine ⟨121960398763199010578276981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81306932508799340385517987 121960398763199010578276981)
            ·
              refine ⟨11433787384049907241713467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121960398763199010578276981 11433787384049907241713467)
              ·
                refine ⟨17150681076074860862570201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11433787384049907241713467 17150681076074860862570201)
                ·
                  refine ⟨12863010807056145646927651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17150681076074860862570201 12863010807056145646927651)
                  ·
                    refine ⟨19294516210584218470391477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12863010807056145646927651 19294516210584218470391477)
                    ·
                      refine ⟨1808860894742270481599201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19294516210584218470391477 1808860894742270481599201)
                      ·
                        rfl

theorem cell23_3522744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_3522744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522744 prefixEnd_3522744 := by exact prefixLift 3522744
  have htrace : WordTrace (prefixWord ++ tailWord_3522744) baseStart_3522744 baseEnd_3522744 := by
    simpa [prefixWord, tailWord_3522744, baseEnd_3522744] using wordTrace_append hprefix tailTrace_3522744
  have hstable : (prefixWord ++ tailWord_3522744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522744).length < 2 ^ (prefixWord ++ tailWord_3522744).sum := by decide
  have hdescent : baseEnd_3522744 < baseStart_3522744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522845 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 2, 5]
def baseStart_3522845 : Nat := 118140960795 + 3522845 * 2 ^ 59
def prefixEnd_3522845 : Nat := 4983230072969 + 3 ^ 40 * 3522845 * 2
def baseEnd_3522845 : Nat := 602970918762791528812079

theorem tailTrace_3522845 : CollatzResearch.WordTrace tailWord_3522845 prefixEnd_3522845 602970918762791528812079 := by
  unfold tailWord_3522845
  simp only [CollatzResearch.WordTrace]
  refine ⟨128488712922341693870985989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85659141948227795913990659 128488712922341693870985989)
  ·
    refine ⟨24091633672939067600809873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128488712922341693870985989 24091633672939067600809873)
    ·
      refine ⟨18068725254704300700607405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24091633672939067600809873 18068725254704300700607405)
      ·
        refine ⟨6775771970514112762727777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18068725254704300700607405 6775771970514112762727777)
        ·
          refine ⟨5081828977885584572045833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6775771970514112762727777 5081828977885584572045833)
          ·
            refine ⟨3811371733414188429034375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5081828977885584572045833 3811371733414188429034375)
            ·
              refine ⟨5717057600121282643551563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3811371733414188429034375 5717057600121282643551563)
              ·
                refine ⟨8575586400181923965327345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5717057600121282643551563 8575586400181923965327345)
                ·
                  refine ⟨6431689800136442973995509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8575586400181923965327345 6431689800136442973995509)
                  ·
                    refine ⟨602970918762791528812079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6431689800136442973995509 602970918762791528812079)
                    ·
                      rfl

theorem cell23_3522845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_3522845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522845 prefixEnd_3522845 := by exact prefixLift 3522845
  have htrace : WordTrace (prefixWord ++ tailWord_3522845) baseStart_3522845 baseEnd_3522845 := by
    simpa [prefixWord, tailWord_3522845, baseEnd_3522845] using wordTrace_append hprefix tailTrace_3522845
  have hstable : (prefixWord ++ tailWord_3522845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522845).length < 2 ^ (prefixWord ++ tailWord_3522845).sum := by decide
  have hdescent : baseEnd_3522845 < baseStart_3522845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522848 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 4]
def baseStart_3522848 : Nat := 118140960795 + 3522848 * 2 ^ 59
def prefixEnd_3522848 : Nat := 4983230072969 + 3 ^ 40 * 3522848 * 2
def baseEnd_3522848 : Nat := 1808914296730338074698723

theorem tailTrace_3522848 : CollatzResearch.WordTrace tailWord_3522848 prefixEnd_3522848 1808914296730338074698723 := by
  unfold tailWord_3522848
  simp only [CollatzResearch.WordTrace]
  refine ⟨64244411170665412691672599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85659214894220550255563465 64244411170665412691672599)
  ·
    refine ⟨96366616755998119037508899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64244411170665412691672599 96366616755998119037508899)
    ·
      refine ⟨144549925133997178556263349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96366616755998119037508899 144549925133997178556263349)
      ·
        refine ⟨13551555481312235489649689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144549925133997178556263349 13551555481312235489649689)
        ·
          refine ⟨10163666610984176617237267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13551555481312235489649689 10163666610984176617237267)
          ·
            refine ⟨15245499916476264925855901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10163666610984176617237267 15245499916476264925855901)
            ·
              refine ⟨5717062468678599347195963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15245499916476264925855901 5717062468678599347195963)
              ·
                refine ⟨8575593703017899020793945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5717062468678599347195963 8575593703017899020793945)
                ·
                  refine ⟨6431695277263424265595459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8575593703017899020793945 6431695277263424265595459)
                  ·
                    refine ⟨9647542915895136398393189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6431695277263424265595459 9647542915895136398393189)
                    ·
                      refine ⟨1808914296730338074698723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9647542915895136398393189 1808914296730338074698723)
                      ·
                        rfl

theorem cell23_3522848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_3522848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522848 prefixEnd_3522848 := by exact prefixLift 3522848
  have htrace : WordTrace (prefixWord ++ tailWord_3522848) baseStart_3522848 baseEnd_3522848 := by
    simpa [prefixWord, tailWord_3522848, baseEnd_3522848] using wordTrace_append hprefix tailTrace_3522848
  have hstable : (prefixWord ++ tailWord_3522848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522848).length < 2 ^ (prefixWord ++ tailWord_3522848).sum := by decide
  have hdescent : baseEnd_3522848 < baseStart_3522848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522851 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 3]
def baseStart_3522851 : Nat := 118140960795 + 3522851 * 2 ^ 59
def prefixEnd_3522851 : Nat := 4983230072969 + 3 ^ 40 * 3522851 * 2
def baseEnd_3522851 : Nat := 1808915837172301562961209

theorem tailTrace_3522851 : CollatzResearch.WordTrace tailWord_3522851 prefixEnd_3522851 1808915837172301562961209 := by
  unfold tailWord_3522851
  simp only [CollatzResearch.WordTrace]
  refine ⟨128488931760319956895704407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85659287840213304597136271 128488931760319956895704407)
  ·
    refine ⟨192733397640479935343556611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128488931760319956895704407 192733397640479935343556611)
    ·
      refine ⟨289100096460719903015334917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192733397640479935343556611 289100096460719903015334917)
      ·
        refine ⟨54206268086384981815375297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289100096460719903015334917 54206268086384981815375297)
        ·
          refine ⟨40654701064788736361531473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54206268086384981815375297 40654701064788736361531473)
          ·
            refine ⟨30491025798591552271148605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40654701064788736361531473 30491025798591552271148605)
            ·
              refine ⟨11434134674471832101680727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30491025798591552271148605 11434134674471832101680727)
              ·
                refine ⟨17151202011707748152521091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11434134674471832101680727 17151202011707748152521091)
                ·
                  refine ⟨25726803017561622228781637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17151202011707748152521091 25726803017561622228781637)
                  ·
                    refine ⟨4823775565792804167896557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25726803017561622228781637 4823775565792804167896557)
                    ·
                      refine ⟨1808915837172301562961209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4823775565792804167896557 1808915837172301562961209)
                      ·
                        rfl

theorem cell23_3522851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_3522851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522851 prefixEnd_3522851 := by exact prefixLift 3522851
  have htrace : WordTrace (prefixWord ++ tailWord_3522851) baseStart_3522851 baseEnd_3522851 := by
    simpa [prefixWord, tailWord_3522851, baseEnd_3522851] using wordTrace_append hprefix tailTrace_3522851
  have hstable : (prefixWord ++ tailWord_3522851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522851).length < 2 ^ (prefixWord ++ tailWord_3522851).sum := by decide
  have hdescent : baseEnd_3522851 < baseStart_3522851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522925 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 2, 3, 2]
def baseStart_3522925 : Nat := 118140960795 + 3522925 * 2 ^ 59
def prefixEnd_3522925 : Nat := 4983230072969 + 3 ^ 40 * 3522925 * 2
def baseEnd_3522925 : Nat := 1808953834740734273435869

theorem tailTrace_3522925 : CollatzResearch.WordTrace tailWord_3522925 prefixEnd_3522925 1808953834740734273435869 := by
  unfold tailWord_3522925
  simp only [CollatzResearch.WordTrace]
  refine ⟨128491630762051867533898229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85661087174701245022598819 128491630762051867533898229)
  ·
    refine ⟨12046090383942362581302959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128491630762051867533898229 12046090383942362581302959)
    ·
      refine ⟨18069135575913543871954439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12046090383942362581302959 18069135575913543871954439)
      ·
        refine ⟨27103703363870315807931659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18069135575913543871954439 27103703363870315807931659)
        ·
          refine ⟨40655555045805473711897489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27103703363870315807931659 40655555045805473711897489)
          ·
            refine ⟨30491666284354105283923117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40655555045805473711897489 30491666284354105283923117)
            ·
              refine ⟨11434374856632789481471169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30491666284354105283923117 11434374856632789481471169)
              ·
                refine ⟨8575781142474592111103377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11434374856632789481471169 8575781142474592111103377)
                ·
                  refine ⟨6431835856855944083327533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8575781142474592111103377 6431835856855944083327533)
                  ·
                    refine ⟨2411938446320979031247825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6431835856855944083327533 2411938446320979031247825)
                    ·
                      refine ⟨1808953834740734273435869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2411938446320979031247825 1808953834740734273435869)
                      ·
                        rfl

theorem cell23_3522925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_3522925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522925 prefixEnd_3522925 := by exact prefixLift 3522925
  have htrace : WordTrace (prefixWord ++ tailWord_3522925) baseStart_3522925 baseEnd_3522925 := by
    simpa [prefixWord, tailWord_3522925, baseEnd_3522925] using wordTrace_append hprefix tailTrace_3522925
  have hstable : (prefixWord ++ tailWord_3522925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522925).length < 2 ^ (prefixWord ++ tailWord_3522925).sum := by decide
  have hdescent : baseEnd_3522925 < baseStart_3522925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522951 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_3522951 : Nat := 118140960795 + 3522951 * 2 ^ 59
def prefixEnd_3522951 : Nat := 4983230072969 + 3 ^ 40 * 3522951 * 2
def baseEnd_3522951 : Nat := 1808967185237751171710749

theorem tailTrace_3522951 : CollatzResearch.WordTrace tailWord_3522951 prefixEnd_3522951 1808967185237751171710749 := by
  unfold tailWord_3522951
  simp only [CollatzResearch.WordTrace]
  refine ⟨128492579059957673974344707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85661719373305115982896471 128492579059957673974344707)
  ·
    refine ⟨192738868589936510961517061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128492579059957673974344707 192738868589936510961517061)
    ·
      refine ⟨36138537860613095805284449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192738868589936510961517061 36138537860613095805284449)
      ·
        refine ⟨27103903395459821853963337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36138537860613095805284449 27103903395459821853963337)
        ·
          refine ⟨20327927546594866390472503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27103903395459821853963337 20327927546594866390472503)
          ·
            refine ⟨30491891319892299585708755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20327927546594866390472503 30491891319892299585708755)
            ·
              refine ⟨45737836979838449378563133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30491891319892299585708755 45737836979838449378563133)
              ·
                refine ⟨17151688867439418516961175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45737836979838449378563133 17151688867439418516961175)
                ·
                  refine ⟨25727533301159127775441763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17151688867439418516961175 25727533301159127775441763)
                  ·
                    refine ⟨38591299951738691663162645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25727533301159127775441763 38591299951738691663162645)
                    ·
                      refine ⟨1808967185237751171710749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38591299951738691663162645 1808967185237751171710749)
                      ·
                        rfl

theorem cell23_3522951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_3522951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522951 prefixEnd_3522951 := by exact prefixLift 3522951
  have htrace : WordTrace (prefixWord ++ tailWord_3522951) baseStart_3522951 baseEnd_3522951 := by
    simpa [prefixWord, tailWord_3522951, baseEnd_3522951] using wordTrace_append hprefix tailTrace_3522951
  have hstable : (prefixWord ++ tailWord_3522951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522951).length < 2 ^ (prefixWord ++ tailWord_3522951).sum := by decide
  have hdescent : baseEnd_3522951 < baseStart_3522951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522955 : List Nat := [1, 1, 1, 1, 4, 6, 1, 2, 1, 1, 4]
def baseStart_3522955 : Nat := 118140960795 + 3522955 * 2 ^ 59
def prefixEnd_3522955 : Nat := 4983230072969 + 3 ^ 40 * 3522955 * 2
def baseEnd_3522955 : Nat := 1808969239160369156060731

theorem tailTrace_3522955 : CollatzResearch.WordTrace tailWord_3522955 prefixEnd_3522955 1808969239160369156060731 := by
  unfold tailWord_3522955
  simp only [CollatzResearch.WordTrace]
  refine ⟨128492724951943182657490319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85661816634628788438326879 128492724951943182657490319)
  ·
    refine ⟨192739087427914773986235479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128492724951943182657490319 192739087427914773986235479)
    ·
      refine ⟨289108631141872160979353219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192739087427914773986235479 289108631141872160979353219)
      ·
        refine ⟨433662946712808241469029829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289108631141872160979353219 433662946712808241469029829)
        ·
          refine ⟨81311802508651545275443093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 433662946712808241469029829 81311802508651545275443093)
          ·
            refine ⟨3811490742593041184786395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81311802508651545275443093 3811490742593041184786395)
            ·
              refine ⟨5717236113889561777179593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3811490742593041184786395 5717236113889561777179593)
              ·
                refine ⟨4287927085417171332884695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5717236113889561777179593 4287927085417171332884695)
                ·
                  refine ⟨6431890628125756999327043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4287927085417171332884695 6431890628125756999327043)
                  ·
                    refine ⟨9647835942188635498990565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6431890628125756999327043 9647835942188635498990565)
                    ·
                      refine ⟨1808969239160369156060731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9647835942188635498990565 1808969239160369156060731)
                      ·
                        rfl

theorem cell23_3522955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 1, 4].length) (baseStart_3522955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522955 prefixEnd_3522955 := by exact prefixLift 3522955
  have htrace : WordTrace (prefixWord ++ tailWord_3522955) baseStart_3522955 baseEnd_3522955 := by
    simpa [prefixWord, tailWord_3522955, baseEnd_3522955] using wordTrace_append hprefix tailTrace_3522955
  have hstable : (prefixWord ++ tailWord_3522955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522955).length < 2 ^ (prefixWord ++ tailWord_3522955).sum := by decide
  have hdescent : baseEnd_3522955 < baseStart_3522955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522968 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 3, 2, 4]
def baseStart_3522968 : Nat := 118140960795 + 3522968 * 2 ^ 59
def prefixEnd_3522968 : Nat := 4983230072969 + 3 ^ 40 * 3522968 * 2
def baseEnd_3522968 : Nat := 1808975914408877605198171

theorem tailTrace_3522968 : CollatzResearch.WordTrace tailWord_3522968 prefixEnd_3522968 1808975914408877605198171 := by
  unfold tailWord_3522968
  simp only [CollatzResearch.WordTrace]
  refine ⟨64246599550448042938856779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85662132733930723918475705 64246599550448042938856779)
  ·
    refine ⟨96369899325672064408285169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64246599550448042938856779 96369899325672064408285169)
    ·
      refine ⟨72277424494254048306213877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96369899325672064408285169 72277424494254048306213877)
      ·
        refine ⟨6776008546336317028707551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72277424494254048306213877 6776008546336317028707551)
        ·
          refine ⟨10164012819504475543061327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6776008546336317028707551 10164012819504475543061327)
          ·
            refine ⟨15246019229256713314591991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10164012819504475543061327 15246019229256713314591991)
            ·
              refine ⟨22869028843885069971887987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15246019229256713314591991 22869028843885069971887987)
              ·
                refine ⟨34303543265827604957831981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22869028843885069971887987 34303543265827604957831981)
                ·
                  refine ⟨12863828724685351859186993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34303543265827604957831981 12863828724685351859186993)
                  ·
                    refine ⟨9647871543514013894390245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12863828724685351859186993 9647871543514013894390245)
                    ·
                      refine ⟨1808975914408877605198171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9647871543514013894390245 1808975914408877605198171)
                      ·
                        rfl

theorem cell23_3522968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_3522968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3522968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3522968 prefixEnd_3522968 := by exact prefixLift 3522968
  have htrace : WordTrace (prefixWord ++ tailWord_3522968) baseStart_3522968 baseEnd_3522968 := by
    simpa [prefixWord, tailWord_3522968, baseEnd_3522968] using wordTrace_append hprefix tailTrace_3522968
  have hstable : (prefixWord ++ tailWord_3522968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522968).length < 2 ^ (prefixWord ++ tailWord_3522968).sum := by decide
  have hdescent : baseEnd_3522968 < baseStart_3522968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523005 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 1, 3, 3]
def baseStart_3523005 : Nat := 118140960795 + 3523005 * 2 ^ 59
def prefixEnd_3523005 : Nat := 4983230072969 + 3 ^ 40 * 3523005 * 2
def baseEnd_3523005 : Nat := 1808994913193093960435501

theorem tailTrace_3523005 : CollatzResearch.WordTrace tailWord_3523005 prefixEnd_3523005 1808994913193093960435501 := by
  unfold tailWord_3523005
  simp only [CollatzResearch.WordTrace]
  refine ⟨128494548601762041196810469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85663032401174694131206979 128494548601762041196810469)
  ·
    refine ⟨24092727862830382724401963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128494548601762041196810469 24092727862830382724401963)
    ·
      refine ⟨36139091794245574086602945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24092727862830382724401963 36139091794245574086602945)
      ·
        refine ⟨27104318845684180564952209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36139091794245574086602945 27104318845684180564952209)
        ·
          refine ⟨20328239134263135423714157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27104318845684180564952209 20328239134263135423714157)
          ·
            refine ⟨7623089675348675783892809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20328239134263135423714157 7623089675348675783892809)
            ·
              refine ⟨5717317256511506837919607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7623089675348675783892809 5717317256511506837919607)
              ·
                refine ⟨8575975884767260256879411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5717317256511506837919607 8575975884767260256879411)
                ·
                  refine ⟨12863963827150890385319117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8575975884767260256879411 12863963827150890385319117)
                  ·
                    refine ⟨4823986435181583894494669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12863963827150890385319117 4823986435181583894494669)
                    ·
                      refine ⟨1808994913193093960435501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4823986435181583894494669 1808994913193093960435501)
                      ·
                        rfl

theorem cell23_3523005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_3523005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523005 prefixEnd_3523005 := by exact prefixLift 3523005
  have htrace : WordTrace (prefixWord ++ tailWord_3523005) baseStart_3523005 baseEnd_3523005 := by
    simpa [prefixWord, tailWord_3523005, baseEnd_3523005] using wordTrace_append hprefix tailTrace_3523005
  have hstable : (prefixWord ++ tailWord_3523005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523005).length < 2 ^ (prefixWord ++ tailWord_3523005).sum := by decide
  have hdescent : baseEnd_3523005 < baseStart_3523005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523011 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 4]
def baseStart_3523011 : Nat := 118140960795 + 3523011 * 2 ^ 59
def prefixEnd_3523011 : Nat := 4983230072969 + 3 ^ 40 * 3523011 * 2
def baseEnd_3523011 : Nat := 1808997994077020936960473

theorem tailTrace_3523011 : CollatzResearch.WordTrace tailWord_3523011 prefixEnd_3523011 1808997994077020936960473 := by
  unfold tailWord_3523011
  simp only [CollatzResearch.WordTrace]
  refine ⟨128494767439740304221528887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85663178293160202814352591 128494767439740304221528887)
  ·
    refine ⟨192742151159610456332293331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128494767439740304221528887 192742151159610456332293331)
    ·
      refine ⟨289113226739415684498439997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192742151159610456332293331 289113226739415684498439997)
      ·
        refine ⟨108417460027280881686914999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289113226739415684498439997 108417460027280881686914999)
        ·
          refine ⟨162626190040921322530372499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108417460027280881686914999 162626190040921322530372499)
          ·
            refine ⟨243939285061381983795558749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162626190040921322530372499 243939285061381983795558749)
            ·
              refine ⟨91477231898018243923334531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243939285061381983795558749 91477231898018243923334531)
              ·
                refine ⟨137215847847027365885001797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91477231898018243923334531 137215847847027365885001797)
                ·
                  refine ⟨25727971471317631103437837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137215847847027365885001797 25727971471317631103437837)
                  ·
                    refine ⟨9647989301744111663789189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25727971471317631103437837 9647989301744111663789189)
                    ·
                      refine ⟨1808997994077020936960473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9647989301744111663789189 1808997994077020936960473)
                      ·
                        rfl

theorem cell23_3523011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_3523011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523011 prefixEnd_3523011 := by exact prefixLift 3523011
  have htrace : WordTrace (prefixWord ++ tailWord_3523011) baseStart_3523011 baseEnd_3523011 := by
    simpa [prefixWord, tailWord_3523011, baseEnd_3523011] using wordTrace_append hprefix tailTrace_3523011
  have hstable : (prefixWord ++ tailWord_3523011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523011).length < 2 ^ (prefixWord ++ tailWord_3523011).sum := by decide
  have hdescent : baseEnd_3523011 < baseStart_3523011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523015 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 3, 3, 2]
def baseStart_3523015 : Nat := 118140960795 + 3523015 * 2 ^ 59
def prefixEnd_3523015 : Nat := 4983230072969 + 3 ^ 40 * 3523015 * 2
def baseEnd_3523015 : Nat := 1809000047999638921310455

theorem tailTrace_3523015 : CollatzResearch.WordTrace tailWord_3523015 prefixEnd_3523015 1809000047999638921310455 := by
  unfold tailWord_3523015
  simp only [CollatzResearch.WordTrace]
  refine ⟨128494913331725812904674499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85663275554483875269782999 128494913331725812904674499)
  ·
    refine ⟨192742369997588719357011749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128494913331725812904674499 192742369997588719357011749)
    ·
      refine ⟨36139194374547884879439703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192742369997588719357011749 36139194374547884879439703)
      ·
        refine ⟨54208791561821827319159555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36139194374547884879439703 54208791561821827319159555)
        ·
          refine ⟨81313187342732740978739333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54208791561821827319159555 81313187342732740978739333)
          ·
            refine ⟨15246222626762388933513625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81313187342732740978739333 15246222626762388933513625)
            ·
              refine ⟨11434666970071791700135219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15246222626762388933513625 11434666970071791700135219)
              ·
                refine ⟨17152000455107687550202829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11434666970071791700135219 17152000455107687550202829)
                ·
                  refine ⟨6432000170665382831326061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17152000455107687550202829 6432000170665382831326061)
                  ·
                    refine ⟨2412000063999518561747273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6432000170665382831326061 2412000063999518561747273)
                    ·
                      refine ⟨1809000047999638921310455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2412000063999518561747273 1809000047999638921310455)
                      ·
                        rfl

theorem cell23_3523015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_3523015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523015 prefixEnd_3523015 := by exact prefixLift 3523015
  have htrace : WordTrace (prefixWord ++ tailWord_3523015) baseStart_3523015 baseEnd_3523015 := by
    simpa [prefixWord, tailWord_3523015, baseEnd_3523015] using wordTrace_append hprefix tailTrace_3523015
  have hstable : (prefixWord ++ tailWord_3523015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523015).length < 2 ^ (prefixWord ++ tailWord_3523015).sum := by decide
  have hdescent : baseEnd_3523015 < baseStart_3523015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523026 : List Nat := [3, 2, 2, 4, 1, 2, 2, 1, 1, 2, 3]
def baseStart_3523026 : Nat := 118140960795 + 3523026 * 2 ^ 59
def prefixEnd_3523026 : Nat := 4983230072969 + 3 ^ 40 * 3523026 * 2
def baseEnd_3523026 : Nat := 1809005696286838378272905

theorem tailTrace_3523026 : CollatzResearch.WordTrace tailWord_3523026 prefixEnd_3523026 1809005696286838378272905 := by
  unfold tailWord_3523026
  simp only [CollatzResearch.WordTrace]
  refine ⟨32123828633671490445831233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85663543023123974522216621 32123828633671490445831233)
  ·
    refine ⟨24092871475253617834373425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32123828633671490445831233 24092871475253617834373425)
    ·
      refine ⟨18069653606440213375780069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24092871475253617834373425 18069653606440213375780069)
      ·
        refine ⟨3388060051207540007958763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18069653606440213375780069 3388060051207540007958763)
        ·
          refine ⟨5082090076811310011938145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3388060051207540007958763 5082090076811310011938145)
          ·
            refine ⟨3811567557608482508953609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5082090076811310011938145 3811567557608482508953609)
            ·
              refine ⟨2858675668206361881715207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3811567557608482508953609 2858675668206361881715207)
              ·
                refine ⟨4288013502309542822572811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2858675668206361881715207 4288013502309542822572811)
                ·
                  refine ⟨6432020253464314233859217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4288013502309542822572811 6432020253464314233859217)
                  ·
                    refine ⟨4824015190098235675394413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6432020253464314233859217 4824015190098235675394413)
                    ·
                      refine ⟨1809005696286838378272905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4824015190098235675394413 1809005696286838378272905)
                      ·
                        rfl

theorem cell23_3523026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_3523026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523026 prefixEnd_3523026 := by exact prefixLift 3523026
  have htrace : WordTrace (prefixWord ++ tailWord_3523026) baseStart_3523026 baseEnd_3523026 := by
    simpa [prefixWord, tailWord_3523026, baseEnd_3523026] using wordTrace_append hprefix tailTrace_3523026
  have hstable : (prefixWord ++ tailWord_3523026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523026).length < 2 ^ (prefixWord ++ tailWord_3523026).sum := by decide
  have hdescent : baseEnd_3523026 < baseStart_3523026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523098 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 4, 5]
def baseStart_3523098 : Nat := 118140960795 + 3523098 * 2 ^ 59
def prefixEnd_3523098 : Nat := 4983230072969 + 3 ^ 40 * 3523098 * 2
def baseEnd_3523098 : Nat := 603014222297987365524191

theorem tailTrace_3523098 : CollatzResearch.WordTrace tailWord_3523098 prefixEnd_3523098 603014222297987365524191 := by
  unfold tailWord_3523098
  simp only [CollatzResearch.WordTrace]
  refine ⟨32124485147606279519986487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85665293726950078719963965 32124485147606279519986487)
  ·
    refine ⟨48186727721409419279979731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32124485147606279519986487 48186727721409419279979731)
    ·
      refine ⟨72280091582114128919969597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48186727721409419279979731 72280091582114128919969597)
      ·
        refine ⟨27105034343292798344988599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72280091582114128919969597 27105034343292798344988599)
        ·
          refine ⟨40657551514939197517482899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27105034343292798344988599 40657551514939197517482899)
          ·
            refine ⟨60986327272408796276224349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40657551514939197517482899 60986327272408796276224349)
            ·
              refine ⟨22869872727153298603584131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60986327272408796276224349 22869872727153298603584131)
              ·
                refine ⟨34304809090729947905376197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22869872727153298603584131 34304809090729947905376197)
                ·
                  refine ⟨6432151704511865232258037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34304809090729947905376197 6432151704511865232258037)
                  ·
                    refine ⟨603014222297987365524191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6432151704511865232258037 603014222297987365524191)
                    ·
                      rfl

theorem cell23_3523098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_3523098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523098 prefixEnd_3523098 := by exact prefixLift 3523098
  have htrace : WordTrace (prefixWord ++ tailWord_3523098) baseStart_3523098 baseEnd_3523098 := by
    simpa [prefixWord, tailWord_3523098, baseEnd_3523098] using wordTrace_append hprefix tailTrace_3523098
  have hstable : (prefixWord ++ tailWord_3523098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523098).length < 2 ^ (prefixWord ++ tailWord_3523098).sum := by decide
  have hdescent : baseEnd_3523098 < baseStart_3523098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523105 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 2, 5, 2]
def baseStart_3523105 : Nat := 118140960795 + 3523105 * 2 ^ 59
def prefixEnd_3523105 : Nat := 4983230072969 + 3 ^ 40 * 3523105 * 2
def baseEnd_3523105 : Nat := 1809046261258543569185041

theorem tailTrace_3523105 : CollatzResearch.WordTrace tailWord_3523105 prefixEnd_3523105 1809046261258543569185041 := by
  unfold tailWord_3523105
  simp only [CollatzResearch.WordTrace]
  refine ⟨128498195901399758275450769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85665463934266505516967179 128498195901399758275450769)
  ·
    refine ⟨96373646926049818706588077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128498195901399758275450769 96373646926049818706588077)
    ·
      refine ⟨36140117597268682014970529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96373646926049818706588077 36140117597268682014970529)
      ·
        refine ⟨27105088197951511511227897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36140117597268682014970529 27105088197951511511227897)
        ·
          refine ⟨20328816148463633633420923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27105088197951511511227897 20328816148463633633420923)
          ·
            refine ⟨30493224222695450450131385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20328816148463633633420923 30493224222695450450131385)
            ·
              refine ⟨22869918167021587837598539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30493224222695450450131385 22869918167021587837598539)
              ·
                refine ⟨34304877250532381756397809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22869918167021587837598539 34304877250532381756397809)
                ·
                  refine ⟨25728657937899286317298357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34304877250532381756397809 25728657937899286317298357)
                  ·
                    refine ⟨2412061681678058092246721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25728657937899286317298357 2412061681678058092246721)
                    ·
                      refine ⟨1809046261258543569185041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2412061681678058092246721 1809046261258543569185041)
                      ·
                        rfl

theorem cell23_3523105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_3523105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523105 prefixEnd_3523105 := by exact prefixLift 3523105
  have htrace : WordTrace (prefixWord ++ tailWord_3523105) baseStart_3523105 baseEnd_3523105 := by
    simpa [prefixWord, tailWord_3523105, baseEnd_3523105] using wordTrace_append hprefix tailTrace_3523105
  have hstable : (prefixWord ++ tailWord_3523105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523105).length < 2 ^ (prefixWord ++ tailWord_3523105).sum := by decide
  have hdescent : baseEnd_3523105 < baseStart_3523105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523135 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 4]
def baseStart_3523135 : Nat := 118140960795 + 3523135 * 2 ^ 59
def prefixEnd_3523135 : Nat := 4983230072969 + 3 ^ 40 * 3523135 * 2
def baseEnd_3523135 : Nat := 1809061665678178451809903

theorem tailTrace_3523135 : CollatzResearch.WordTrace tailWord_3523135 prefixEnd_3523135 1809061665678178451809903 := by
  unfold tailWord_3523135
  simp only [CollatzResearch.WordTrace]
  refine ⟨128499290091291073399042859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85666193394194048932695239 128499290091291073399042859)
  ·
    refine ⟨192748935136936610098564289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128499290091291073399042859 192748935136936610098564289)
    ·
      refine ⟨144561701352702457573923217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192748935136936610098564289 144561701352702457573923217)
      ·
        refine ⟨108421276014526843180442413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144561701352702457573923217 108421276014526843180442413)
        ·
          refine ⟨40657978505447566192665905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108421276014526843180442413 40657978505447566192665905)
          ·
            refine ⟨30493483879085674644499429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40657978505447566192665905 30493483879085674644499429)
            ·
              refine ⟨5717528227328563995843643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30493483879085674644499429 5717528227328563995843643)
              ·
                refine ⟨8576292340992845993765465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5717528227328563995843643 8576292340992845993765465)
                ·
                  refine ⟨6432219255744634495324099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8576292340992845993765465 6432219255744634495324099)
                  ·
                    refine ⟨9648328883616951742986149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6432219255744634495324099 9648328883616951742986149)
                    ·
                      refine ⟨1809061665678178451809903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9648328883616951742986149 1809061665678178451809903)
                      ·
                        rfl

theorem cell23_3523135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_3523135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523135 prefixEnd_3523135 := by exact prefixLift 3523135
  have htrace : WordTrace (prefixWord ++ tailWord_3523135) baseStart_3523135 baseEnd_3523135 := by
    simpa [prefixWord, tailWord_3523135, baseEnd_3523135] using wordTrace_append hprefix tailTrace_3523135
  have hstable : (prefixWord ++ tailWord_3523135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523135).length < 2 ^ (prefixWord ++ tailWord_3523135).sum := by decide
  have hdescent : baseEnd_3523135 < baseStart_3523135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523142 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3523142 : Nat := 118140960795 + 3523142 * 2 ^ 59
def prefixEnd_3523142 : Nat := 4983230072969 + 3 ^ 40 * 3523142 * 2
def baseEnd_3523142 : Nat := 1809065260042759924422371

theorem tailTrace_3523142 : CollatzResearch.WordTrace tailWord_3523142 prefixEnd_3523142 1809065260042759924422371 := by
  unfold tailWord_3523142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015610793820803549829615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85666363601510475729698453 4015610793820803549829615)
  ·
    refine ⟨6023416190731205324744423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4015610793820803549829615 6023416190731205324744423)
    ·
      refine ⟨9035124286096807987116635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6023416190731205324744423 9035124286096807987116635)
      ·
        refine ⟨13552686429145211980674953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9035124286096807987116635 13552686429145211980674953)
        ·
          refine ⟨10164514821858908985506215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13552686429145211980674953 10164514821858908985506215)
          ·
            refine ⟨15246772232788363478259323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10164514821858908985506215 15246772232788363478259323)
            ·
              refine ⟨22870158349182545217388985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15246772232788363478259323 22870158349182545217388985)
              ·
                refine ⟨17152618761886908913041739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22870158349182545217388985 17152618761886908913041739)
                ·
                  refine ⟨25728928142830363369562609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17152618761886908913041739 25728928142830363369562609)
                  ·
                    refine ⟨19296696107122772527171957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25728928142830363369562609 19296696107122772527171957)
                    ·
                      refine ⟨1809065260042759924422371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19296696107122772527171957 1809065260042759924422371)
                      ·
                        rfl

theorem cell23_3523142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3523142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523142 prefixEnd_3523142 := by exact prefixLift 3523142
  have htrace : WordTrace (prefixWord ++ tailWord_3523142) baseStart_3523142 baseEnd_3523142 := by
    simpa [prefixWord, tailWord_3523142, baseEnd_3523142] using wordTrace_append hprefix tailTrace_3523142
  have hstable : (prefixWord ++ tailWord_3523142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523142).length < 2 ^ (prefixWord ++ tailWord_3523142).sum := by decide
  have hdescent : baseEnd_3523142 < baseStart_3523142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523148 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 2, 1, 6]
def baseStart_3523148 : Nat := 118140960795 + 3523148 * 2 ^ 59
def prefixEnd_3523148 : Nat := 4983230072969 + 3 ^ 40 * 3523148 * 2
def baseEnd_3523148 : Nat := 1809068340926686900947343

theorem tailTrace_3523148 : CollatzResearch.WordTrace tailWord_3523148 prefixEnd_3523148 1809068340926686900947343 := by
  unfold tailWord_3523148
  simp only [CollatzResearch.WordTrace]
  refine ⟨64249882120121988309633049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85666509493495984412844065 64249882120121988309633049)
  ·
    refine ⟨48187411590091491232224787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64249882120121988309633049 48187411590091491232224787)
    ·
      refine ⟨72281117385137236848337181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48187411590091491232224787 72281117385137236848337181)
      ·
        refine ⟨27105419019426463818126443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72281117385137236848337181 27105419019426463818126443)
        ·
          refine ⟨40658128529139695727189665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27105419019426463818126443 40658128529139695727189665)
          ·
            refine ⟨30493596396854771795392249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40658128529139695727189665 30493596396854771795392249)
            ·
              refine ⟨22870197297641078846544187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30493596396854771795392249 22870197297641078846544187)
              ·
                refine ⟨34305295946461618269816281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22870197297641078846544187 34305295946461618269816281)
                ·
                  refine ⟨25728971959846213702362211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34305295946461618269816281 25728971959846213702362211)
                  ·
                    refine ⟨38593457939769320553543317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25728971959846213702362211 38593457939769320553543317)
                    ·
                      refine ⟨1809068340926686900947343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38593457939769320553543317 1809068340926686900947343)
                      ·
                        rfl

theorem cell23_3523148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_3523148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523148 prefixEnd_3523148 := by exact prefixLift 3523148
  have htrace : WordTrace (prefixWord ++ tailWord_3523148) baseStart_3523148 baseEnd_3523148 := by
    simpa [prefixWord, tailWord_3523148, baseEnd_3523148] using wordTrace_append hprefix tailTrace_3523148
  have hstable : (prefixWord ++ tailWord_3523148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523148).length < 2 ^ (prefixWord ++ tailWord_3523148).sum := by decide
  have hdescent : baseEnd_3523148 < baseStart_3523148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523253 : List Nat := [1, 3, 3, 3, 1, 3, 1, 3, 1, 1, 3]
def baseStart_3523253 : Nat := 118140960795 + 3523253 * 2 ^ 59
def prefixEnd_3523253 : Nat := 4983230072969 + 3 ^ 40 * 3523253 * 2
def baseEnd_3523253 : Nat := 1809122256395408990134361

theorem tailTrace_3523253 : CollatzResearch.WordTrace tailWord_3523253 prefixEnd_3523253 1809122256395408990134361 := by
  unfold tailWord_3523253
  simp only [CollatzResearch.WordTrace]
  refine ⟨128503593904863579551838413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85669062603242386367892275 128503593904863579551838413)
  ·
    refine ⟨48188847714323842331939405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128503593904863579551838413 48188847714323842331939405)
    ·
      refine ⟨18070817892871440874477277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48188847714323842331939405 18070817892871440874477277)
      ·
        refine ⟨6776556709826790327928979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18070817892871440874477277 6776556709826790327928979)
        ·
          refine ⟨10164835064740185491893469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6776556709826790327928979 10164835064740185491893469)
          ·
            refine ⟨3811813149277569559460051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10164835064740185491893469 3811813149277569559460051)
            ·
              refine ⟨5717719723916354339190077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3811813149277569559460051 5717719723916354339190077)
              ·
                refine ⟨2144144896468632877196279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5717719723916354339190077 2144144896468632877196279)
                ·
                  refine ⟨3216217344702949315794419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2144144896468632877196279 3216217344702949315794419)
                  ·
                    refine ⟨4824326017054423973691629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3216217344702949315794419 4824326017054423973691629)
                    ·
                      refine ⟨1809122256395408990134361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4824326017054423973691629 1809122256395408990134361)
                      ·
                        rfl

theorem cell23_3523253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_3523253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523253 prefixEnd_3523253 := by exact prefixLift 3523253
  have htrace : WordTrace (prefixWord ++ tailWord_3523253) baseStart_3523253 baseEnd_3523253 := by
    simpa [prefixWord, tailWord_3523253, baseEnd_3523253] using wordTrace_append hprefix tailTrace_3523253
  have hstable : (prefixWord ++ tailWord_3523253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523253).length < 2 ^ (prefixWord ++ tailWord_3523253).sum := by decide
  have hdescent : baseEnd_3523253 < baseStart_3523253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523262 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5]
def baseStart_3523262 : Nat := 118140960795 + 3523262 * 2 ^ 59
def prefixEnd_3523262 : Nat := 4983230072969 + 3 ^ 40 * 3523262 * 2
def baseEnd_3523262 : Nat := 1809126877721299454921819

theorem tailTrace_3523262 : CollatzResearch.WordTrace tailWord_3523262 prefixEnd_3523262 1809126877721299454921819 := by
  unfold tailWord_3523262
  simp only [CollatzResearch.WordTrace]
  refine ⟨16062990270228871761114505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85669281441220649392610693 16062990270228871761114505)
  ·
    refine ⟨12047242702671653820835879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16062990270228871761114505 12047242702671653820835879)
    ·
      refine ⟨18070864054007480731253819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12047242702671653820835879 18070864054007480731253819)
      ·
        refine ⟨27106296081011221096880729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18070864054007480731253819 27106296081011221096880729)
        ·
          refine ⟨20329722060758415822660547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27106296081011221096880729 20329722060758415822660547)
          ·
            refine ⟨30494583091137623733990821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20329722060758415822660547 30494583091137623733990821)
            ·
              refine ⟨5717734329588304450123279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30494583091137623733990821 5717734329588304450123279)
              ·
                refine ⟨8576601494382456675184919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5717734329588304450123279 8576601494382456675184919)
                ·
                  refine ⟨12864902241573685012777379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8576601494382456675184919 12864902241573685012777379)
                  ·
                    refine ⟨19297353362360527519166069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12864902241573685012777379 19297353362360527519166069)
                    ·
                      refine ⟨1809126877721299454921819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19297353362360527519166069 1809126877721299454921819)
                      ·
                        rfl

theorem cell23_3523262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_3523262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523262 prefixEnd_3523262 := by exact prefixLift 3523262
  have htrace : WordTrace (prefixWord ++ tailWord_3523262) baseStart_3523262 baseEnd_3523262 := by
    simpa [prefixWord, tailWord_3523262, baseEnd_3523262] using wordTrace_append hprefix tailTrace_3523262
  have hstable : (prefixWord ++ tailWord_3523262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523262).length < 2 ^ (prefixWord ++ tailWord_3523262).sum := by decide
  have hdescent : baseEnd_3523262 < baseStart_3523262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523270 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_3523270 : Nat := 118140960795 + 3523270 * 2 ^ 59
def prefixEnd_3523270 : Nat := 4983230072969 + 3 ^ 40 * 3523270 * 2
def baseEnd_3523270 : Nat := 1809130985566535423621783

theorem tailTrace_3523270 : CollatzResearch.WordTrace tailWord_3523270 prefixEnd_3523270 1809130985566535423621783 := by
  unfold tailWord_3523270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015756685806312232975227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85669475963867994303471509 4015756685806312232975227)
  ·
    refine ⟨6023635028709468349462841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4015756685806312232975227 6023635028709468349462841)
    ·
      refine ⟨4517726271532101262097131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6023635028709468349462841 4517726271532101262097131)
      ·
        refine ⟨6776589407298151893145697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4517726271532101262097131 6776589407298151893145697)
        ·
          refine ⟨5082442055473613919859273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6776589407298151893145697 5082442055473613919859273)
          ·
            refine ⟨3811831541605210439894455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5082442055473613919859273 3811831541605210439894455)
            ·
              refine ⟨5717747312407815659841683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3811831541605210439894455 5717747312407815659841683)
              ·
                refine ⟨8576620968611723489762525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5717747312407815659841683 8576620968611723489762525)
                ·
                  refine ⟨3216232863229396308660947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8576620968611723489762525 3216232863229396308660947)
                  ·
                    refine ⟨4824349294844094462991421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3216232863229396308660947 4824349294844094462991421)
                    ·
                      refine ⟨1809130985566535423621783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4824349294844094462991421 1809130985566535423621783)
                      ·
                        rfl

theorem cell23_3523270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_3523270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523270 prefixEnd_3523270 := by exact prefixLift 3523270
  have htrace : WordTrace (prefixWord ++ tailWord_3523270) baseStart_3523270 baseEnd_3523270 := by
    simpa [prefixWord, tailWord_3523270, baseEnd_3523270] using wordTrace_append hprefix tailTrace_3523270
  have hstable : (prefixWord ++ tailWord_3523270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523270).length < 2 ^ (prefixWord ++ tailWord_3523270).sum := by decide
  have hdescent : baseEnd_3523270 < baseStart_3523270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523276 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 3, 2, 2]
def baseStart_3523276 : Nat := 118140960795 + 3523276 * 2 ^ 59
def prefixEnd_3523276 : Nat := 4983230072969 + 3 ^ 40 * 3523276 * 2
def baseEnd_3523276 : Nat := 1809134066450462400146755

theorem tailTrace_3523276 : CollatzResearch.WordTrace tailWord_3523276 prefixEnd_3523276 1809134066450462400146755 := by
  unfold tailWord_3523276
  simp only [CollatzResearch.WordTrace]
  refine ⟨64252216391890127239962841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85669621855853502986617121 64252216391890127239962841)
  ·
    refine ⟨48189162293917595429972131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64252216391890127239962841 48189162293917595429972131)
    ·
      refine ⟨72283743440876393144958197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48189162293917595429972131 72283743440876393144958197)
      ·
        refine ⟨6776600947582161857339831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72283743440876393144958197 6776600947582161857339831)
        ·
          refine ⟨10164901421373242786009747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6776600947582161857339831 10164901421373242786009747)
          ·
            refine ⟨15247352132059864179014621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10164901421373242786009747 15247352132059864179014621)
            ·
              refine ⟨5717757049522449067130483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15247352132059864179014621 5717757049522449067130483)
              ·
                refine ⟨8576635574283673600695725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5717757049522449067130483 8576635574283673600695725)
                ·
                  refine ⟨3216238340356377600260897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8576635574283673600695725 3216238340356377600260897)
                  ·
                    refine ⟨2412178755267283200195673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3216238340356377600260897 2412178755267283200195673)
                    ·
                      refine ⟨1809134066450462400146755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2412178755267283200195673 1809134066450462400146755)
                      ·
                        rfl

theorem cell23_3523276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_3523276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523276 prefixEnd_3523276 := by exact prefixLift 3523276
  have htrace : WordTrace (prefixWord ++ tailWord_3523276) baseStart_3523276 baseEnd_3523276 := by
    simpa [prefixWord, tailWord_3523276, baseEnd_3523276] using wordTrace_append hprefix tailTrace_3523276
  have hstable : (prefixWord ++ tailWord_3523276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523276).length < 2 ^ (prefixWord ++ tailWord_3523276).sum := by decide
  have hdescent : baseEnd_3523276 < baseStart_3523276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523282 : List Nat := [3, 2, 2, 2, 3, 1, 2, 8]
def baseStart_3523282 : Nat := 118140960795 + 3523282 * 2 ^ 59
def prefixEnd_3523282 : Nat := 4983230072969 + 3 ^ 40 * 3523282 * 2
def baseEnd_3523282 : Nat := 67005079530903310247101

theorem tailTrace_3523282 : CollatzResearch.WordTrace tailWord_3523282 prefixEnd_3523282 67005079530903310247101 := by
  unfold tailWord_3523282
  simp only [CollatzResearch.WordTrace]
  refine ⟨32126162905439629376161025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85669767747839011669762733 32126162905439629376161025)
  ·
    refine ⟨24094622179079722032120769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32126162905439629376161025 24094622179079722032120769)
    ·
      refine ⟨18070966634309791524090577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24094622179079722032120769 18070966634309791524090577)
      ·
        refine ⟨13553224975732343643067933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18070966634309791524090577 13553224975732343643067933)
        ·
          refine ⟨5082459365899628866150475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13553224975732343643067933 5082459365899628866150475)
          ·
            refine ⟨7623689048849443299225713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5082459365899628866150475 7623689048849443299225713)
            ·
              refine ⟨5717766786637082474419285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7623689048849443299225713 5717766786637082474419285)
              ·
                refine ⟨67005079530903310247101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5717766786637082474419285 67005079530903310247101)
                ·
                  rfl

theorem cell23_3523282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 8].length) (baseStart_3523282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523282 prefixEnd_3523282 := by exact prefixLift 3523282
  have htrace : WordTrace (prefixWord ++ tailWord_3523282) baseStart_3523282 baseEnd_3523282 := by
    simpa [prefixWord, tailWord_3523282, baseEnd_3523282] using wordTrace_append hprefix tailTrace_3523282
  have hstable : (prefixWord ++ tailWord_3523282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523282).length < 2 ^ (prefixWord ++ tailWord_3523282).sum := by decide
  have hdescent : baseEnd_3523282 < baseStart_3523282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523325 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 2, 6]
def baseStart_3523325 : Nat := 118140960795 + 3523325 * 2 ^ 59
def prefixEnd_3523325 : Nat := 4983230072969 + 3 ^ 40 * 3523325 * 2
def baseEnd_3523325 : Nat := 603053075667510902811343

theorem tailTrace_3523325 : CollatzResearch.WordTrace tailWord_3523325 prefixEnd_3523325 603053075667510902811343 := by
  unfold tailWord_3523325
  simp only [CollatzResearch.WordTrace]
  refine ⟨128506219960602735848459429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85670813307068490565639619 128506219960602735848459429)
  ·
    refine ⟨24094916242613012971586143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128506219960602735848459429 24094916242613012971586143)
    ·
      refine ⟨36142374363919519457379215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24094916242613012971586143 36142374363919519457379215)
      ·
        refine ⟨54213561545879279186068823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36142374363919519457379215 54213561545879279186068823)
        ·
          refine ⟨81320342318818918779103235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54213561545879279186068823 81320342318818918779103235)
          ·
            refine ⟨121980513478228378168654853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81320342318818918779103235 121980513478228378168654853)
            ·
              refine ⟨22871346277167820906622785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121980513478228378168654853 22871346277167820906622785)
              ·
                refine ⟨17153509707875865679967089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22871346277167820906622785 17153509707875865679967089)
                ·
                  refine ⟨12865132280906899259975317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17153509707875865679967089 12865132280906899259975317)
                  ·
                    refine ⟨603053075667510902811343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12865132280906899259975317 603053075667510902811343)
                    ·
                      rfl

theorem cell23_3523325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_3523325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523325 prefixEnd_3523325 := by exact prefixLift 3523325
  have htrace : WordTrace (prefixWord ++ tailWord_3523325) baseStart_3523325 baseEnd_3523325 := by
    simpa [prefixWord, tailWord_3523325, baseEnd_3523325] using wordTrace_append hprefix tailTrace_3523325
  have hstable : (prefixWord ++ tailWord_3523325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523325).length < 2 ^ (prefixWord ++ tailWord_3523325).sum := by decide
  have hdescent : baseEnd_3523325 < baseStart_3523325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523326 : List Nat := [4, 2, 2, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_3523326 : Nat := 118140960795 + 3523326 * 2 ^ 59
def prefixEnd_3523326 : Nat := 4983230072969 + 3 ^ 40 * 3523326 * 2
def baseEnd_3523326 : Nat := 1809159740483187204521525

theorem tailTrace_3523326 : CollatzResearch.WordTrace tailWord_3523326 prefixEnd_3523326 1809159740483187204521525 := by
  unfold tailWord_3523326
  simp only [CollatzResearch.WordTrace]
  refine ⟨16063282054199889127405729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85670837622399408679497221 16063282054199889127405729)
  ·
    refine ⟨12047461540649916845554297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16063282054199889127405729 12047461540649916845554297)
    ·
      refine ⟨9035596155487437634165723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12047461540649916845554297 9035596155487437634165723)
      ·
        refine ⟨13553394233231156451248585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9035596155487437634165723 13553394233231156451248585)
        ·
          refine ⟨10165045674923367338436439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13553394233231156451248585 10165045674923367338436439)
          ·
            refine ⟨15247568512385051007654659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10165045674923367338436439 15247568512385051007654659)
            ·
              refine ⟨22871352768577576511481989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15247568512385051007654659 22871352768577576511481989)
              ·
                refine ⟨4288378644108295595902873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22871352768577576511481989 4288378644108295595902873)
                ·
                  refine ⟨3216283983081221696927155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4288378644108295595902873 3216283983081221696927155)
                  ·
                    refine ⟨4824425974621832545390733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3216283983081221696927155 4824425974621832545390733)
                    ·
                      refine ⟨1809159740483187204521525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4824425974621832545390733 1809159740483187204521525)
                      ·
                        rfl

theorem cell23_3523326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_3523326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523326 prefixEnd_3523326 := by exact prefixLift 3523326
  have htrace : WordTrace (prefixWord ++ tailWord_3523326) baseStart_3523326 baseEnd_3523326 := by
    simpa [prefixWord, tailWord_3523326, baseEnd_3523326] using wordTrace_append hprefix tailTrace_3523326
  have hstable : (prefixWord ++ tailWord_3523326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523326).length < 2 ^ (prefixWord ++ tailWord_3523326).sum := by decide
  have hdescent : baseEnd_3523326 < baseStart_3523326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523345 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 4]
def baseStart_3523345 : Nat := 118140960795 + 3523345 * 2 ^ 59
def prefixEnd_3523345 : Nat := 4983230072969 + 3 ^ 40 * 3523345 * 2
def baseEnd_3523345 : Nat := 1809169496615622630183937

theorem tailTrace_3523345 : CollatzResearch.WordTrace tailWord_3523345 prefixEnd_3523345 1809169496615622630183937 := by
  unfold tailWord_3523345
  simp only [CollatzResearch.WordTrace]
  refine ⟨128506949420530279264187489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85671299613686852842791659 128506949420530279264187489)
  ·
    refine ⟨96380212065397709448140617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128506949420530279264187489 96380212065397709448140617)
    ·
      refine ⟨72285159049048282086105463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96380212065397709448140617 72285159049048282086105463)
      ·
        refine ⟨108427738573572423129158195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72285159049048282086105463 108427738573572423129158195)
        ·
          refine ⟨162641607860358634693737293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108427738573572423129158195 162641607860358634693737293)
          ·
            refine ⟨60990602947634488010151485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162641607860358634693737293 60990602947634488010151485)
            ·
              refine ⟨22871476105362933003806807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60990602947634488010151485 22871476105362933003806807)
              ·
                refine ⟨34307214158044399505710211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22871476105362933003806807 34307214158044399505710211)
                ·
                  refine ⟨51460821237066599258565317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34307214158044399505710211 51460821237066599258565317)
                  ·
                    refine ⟨9648903981949987360980997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51460821237066599258565317 9648903981949987360980997)
                    ·
                      refine ⟨1809169496615622630183937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9648903981949987360980997 1809169496615622630183937)
                      ·
                        rfl

theorem cell23_3523345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_3523345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523345 prefixEnd_3523345 := by exact prefixLift 3523345
  have htrace : WordTrace (prefixWord ++ tailWord_3523345) baseStart_3523345 baseEnd_3523345 := by
    simpa [prefixWord, tailWord_3523345, baseEnd_3523345] using wordTrace_append hprefix tailTrace_3523345
  have hstable : (prefixWord ++ tailWord_3523345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523345).length < 2 ^ (prefixWord ++ tailWord_3523345).sum := by decide
  have hdescent : baseEnd_3523345 < baseStart_3523345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523349 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 1, 4, 2]
def baseStart_3523349 : Nat := 118140960795 + 3523349 * 2 ^ 59
def prefixEnd_3523349 : Nat := 4983230072969 + 3 ^ 40 * 3523349 * 2
def baseEnd_3523349 : Nat := 1809171550538240614533919

theorem tailTrace_3523349 : CollatzResearch.WordTrace tailWord_3523349 prefixEnd_3523349 1809171550538240614533919 := by
  unfold tailWord_3523349
  simp only [CollatzResearch.WordTrace]
  refine ⟨128507095312515787947333101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85671396875010525298222067 128507095312515787947333101)
  ·
    refine ⟨48190160742193420480249913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128507095312515787947333101 48190160742193420480249913)
    ·
      refine ⟨36142620556645065360187435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48190160742193420480249913 36142620556645065360187435)
      ·
        refine ⟨54213930834967598040281153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36142620556645065360187435 54213930834967598040281153)
        ·
          refine ⟨40660448126225698530210865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54213930834967598040281153 40660448126225698530210865)
          ·
            refine ⟨30495336094669273897658149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40660448126225698530210865 30495336094669273897658149)
            ·
              refine ⟨5717875517750488855810903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30495336094669273897658149 5717875517750488855810903)
              ·
                refine ⟨8576813276625733283716355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5717875517750488855810903 8576813276625733283716355)
                ·
                  refine ⟨12865219914938599925574533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8576813276625733283716355 12865219914938599925574533)
                  ·
                    refine ⟨2412228734050987486045225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12865219914938599925574533 2412228734050987486045225)
                    ·
                      refine ⟨1809171550538240614533919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2412228734050987486045225 1809171550538240614533919)
                      ·
                        rfl

theorem cell23_3523349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_3523349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523349 prefixEnd_3523349 := by exact prefixLift 3523349
  have htrace : WordTrace (prefixWord ++ tailWord_3523349) baseStart_3523349 baseEnd_3523349 := by
    simpa [prefixWord, tailWord_3523349, baseEnd_3523349] using wordTrace_append hprefix tailTrace_3523349
  have hstable : (prefixWord ++ tailWord_3523349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523349).length < 2 ^ (prefixWord ++ tailWord_3523349).sum := by decide
  have hdescent : baseEnd_3523349 < baseStart_3523349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523389 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 7]
def baseStart_3523389 : Nat := 118140960795 + 3523389 * 2 ^ 59
def prefixEnd_3523389 : Nat := 4983230072969 + 3 ^ 40 * 3523389 * 2
def baseEnd_3523389 : Nat := 201021343307157828670415

theorem tailTrace_3523389 : CollatzResearch.WordTrace tailWord_3523389 prefixEnd_3523389 201021343307157828670415 := by
  unfold tailWord_3523389
  simp only [CollatzResearch.WordTrace]
  refine ⟨128508554232370874778789221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85672369488247249852526147 128508554232370874778789221)
  ·
    refine ⟨24095353918569539021022979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128508554232370874778789221 24095353918569539021022979)
    ·
      refine ⟨36143030877854308531534469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24095353918569539021022979 36143030877854308531534469)
      ·
        refine ⟨6776818289597682849662713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36143030877854308531534469 6776818289597682849662713)
        ·
          refine ⟨5082613717198262137247035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6776818289597682849662713 5082613717198262137247035)
          ·
            refine ⟨7623920575797393205870553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5082613717198262137247035 7623920575797393205870553)
            ·
              refine ⟨5717940431848044904402915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7623920575797393205870553 5717940431848044904402915)
              ·
                refine ⟨8576910647772067356604373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5717940431848044904402915 8576910647772067356604373)
                ·
                  refine ⟨201021343307157828670415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8576910647772067356604373 201021343307157828670415)
                  ·
                    rfl

theorem cell23_3523389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_3523389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523389 prefixEnd_3523389 := by exact prefixLift 3523389
  have htrace : WordTrace (prefixWord ++ tailWord_3523389) baseStart_3523389 baseEnd_3523389 := by
    simpa [prefixWord, tailWord_3523389, baseEnd_3523389] using wordTrace_append hprefix tailTrace_3523389
  have hstable : (prefixWord ++ tailWord_3523389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523389).length < 2 ^ (prefixWord ++ tailWord_3523389).sum := by decide
  have hdescent : baseEnd_3523389 < baseStart_3523389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523392 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 1, 7, 2]
def baseStart_3523392 : Nat := 118140960795 + 3523392 * 2 ^ 59
def prefixEnd_3523392 : Nat := 4983230072969 + 3 ^ 40 * 3523392 * 2
def baseEnd_3523392 : Nat := 1809193630206383946296221

theorem tailTrace_3523392 : CollatzResearch.WordTrace tailWord_3523392 prefixEnd_3523392 1809193630206383946296221 := by
  unfold tailWord_3523392
  simp only [CollatzResearch.WordTrace]
  refine ⟨64254331825680003145574215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85672442434240004194098953 64254331825680003145574215)
  ·
    refine ⟨96381497738520004718361323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64254331825680003145574215 96381497738520004718361323)
    ·
      refine ⟨144572246607780007077541985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96381497738520004718361323 144572246607780007077541985)
      ·
        refine ⟨108429184955835005308156489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144572246607780007077541985 108429184955835005308156489)
        ·
          refine ⟨81321888716876253981117367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108429184955835005308156489 81321888716876253981117367)
          ·
            refine ⟨121982833075314380971676051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81321888716876253981117367 121982833075314380971676051)
            ·
              refine ⟨182974249612971571457514077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121982833075314380971676051 182974249612971571457514077)
              ·
                refine ⟨68615343604864339296567779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182974249612971571457514077 68615343604864339296567779)
                ·
                  refine ⟨102923015407296508944851669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68615343604864339296567779 102923015407296508944851669)
                  ·
                    refine ⟨2412258173608511928394961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 102923015407296508944851669 2412258173608511928394961)
                    ·
                      refine ⟨1809193630206383946296221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2412258173608511928394961 1809193630206383946296221)
                      ·
                        rfl

theorem cell23_3523392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 7, 2].length) (baseStart_3523392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523392 prefixEnd_3523392 := by exact prefixLift 3523392
  have htrace : WordTrace (prefixWord ++ tailWord_3523392) baseStart_3523392 baseEnd_3523392 := by
    simpa [prefixWord, tailWord_3523392, baseEnd_3523392] using wordTrace_append hprefix tailTrace_3523392
  have hstable : (prefixWord ++ tailWord_3523392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523392).length < 2 ^ (prefixWord ++ tailWord_3523392).sum := by decide
  have hdescent : baseEnd_3523392 < baseStart_3523392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523395 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 7]
def baseStart_3523395 : Nat := 118140960795 + 3523395 * 2 ^ 59
def prefixEnd_3523395 : Nat := 4983230072969 + 3 ^ 40 * 3523395 * 2
def baseEnd_3523395 : Nat := 1809195170648347434558707

theorem tailTrace_3523395 : CollatzResearch.WordTrace tailWord_3523395 prefixEnd_3523395 1809195170648347434558707 := by
  unfold tailWord_3523395
  simp only [CollatzResearch.WordTrace]
  refine ⟨128508773070349137803507639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85672515380232758535671759 128508773070349137803507639)
  ·
    refine ⟨192763159605523706705261459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128508773070349137803507639 192763159605523706705261459)
    ·
      refine ⟨289144739408285560057892189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192763159605523706705261459 289144739408285560057892189)
      ·
        refine ⟨108429277278107085021709571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289144739408285560057892189 108429277278107085021709571)
        ·
          refine ⟨162643915917160627532564357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108429277278107085021709571 162643915917160627532564357)
          ·
            refine ⟨30495734234467617662355817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162643915917160627532564357 30495734234467617662355817)
            ·
              refine ⟨22871800675850713246766863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30495734234467617662355817 22871800675850713246766863)
              ·
                refine ⟨34307701013776069870150295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22871800675850713246766863 34307701013776069870150295)
                ·
                  refine ⟨51461551520664104805225443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34307701013776069870150295 51461551520664104805225443)
                  ·
                    refine ⟨77192327280996157207838165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51461551520664104805225443 77192327280996157207838165)
                    ·
                      refine ⟨1809195170648347434558707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77192327280996157207838165 1809195170648347434558707)
                      ·
                        rfl

theorem cell23_3523395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_3523395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523395 prefixEnd_3523395 := by exact prefixLift 3523395
  have htrace : WordTrace (prefixWord ++ tailWord_3523395) baseStart_3523395 baseEnd_3523395 := by
    simpa [prefixWord, tailWord_3523395, baseEnd_3523395] using wordTrace_append hprefix tailTrace_3523395
  have hstable : (prefixWord ++ tailWord_3523395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523395).length < 2 ^ (prefixWord ++ tailWord_3523395).sum := by decide
  have hdescent : baseEnd_3523395 < baseStart_3523395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523435 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 6]
def baseStart_3523435 : Nat := 118140960795 + 3523435 * 2 ^ 59
def prefixEnd_3523435 : Nat := 4983230072969 + 3 ^ 40 * 3523435 * 2
def baseEnd_3523435 : Nat := 1809215709874527278058523

theorem tailTrace_3523435 : CollatzResearch.WordTrace tailWord_3523435 prefixEnd_3523435 1809215709874527278058523 := by
  unfold tailWord_3523435
  simp only [CollatzResearch.WordTrace]
  refine ⟨128510231990204224634963759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85673487993469483089975839 128510231990204224634963759)
  ·
    refine ⟨192765347985306336952445639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128510231990204224634963759 192765347985306336952445639)
    ·
      refine ⟨289148021977959505428668459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192765347985306336952445639 289148021977959505428668459)
      ·
        refine ⟨433722032966939258143002689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289148021977959505428668459 433722032966939258143002689)
        ·
          refine ⟨325291524725204443607252017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433722032966939258143002689 325291524725204443607252017)
          ·
            refine ⟨243968643543903332705439013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325291524725204443607252017 243968643543903332705439013)
            ·
              refine ⟨45744120664481874882269815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 243968643543903332705439013 45744120664481874882269815)
              ·
                refine ⟨68616180996722812323404723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45744120664481874882269815 68616180996722812323404723)
                ·
                  refine ⟨102924271495084218485107085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68616180996722812323404723 102924271495084218485107085)
                  ·
                    refine ⟨38596601810656581931915157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102924271495084218485107085 38596601810656581931915157)
                    ·
                      refine ⟨1809215709874527278058523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38596601810656581931915157 1809215709874527278058523)
                      ·
                        rfl

theorem cell23_3523435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 6].length) (baseStart_3523435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523435 prefixEnd_3523435 := by exact prefixLift 3523435
  have htrace : WordTrace (prefixWord ++ tailWord_3523435) baseStart_3523435 baseEnd_3523435 := by
    simpa [prefixWord, tailWord_3523435, baseEnd_3523435] using wordTrace_append hprefix tailTrace_3523435
  have hstable : (prefixWord ++ tailWord_3523435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523435).length < 2 ^ (prefixWord ++ tailWord_3523435).sum := by decide
  have hdescent : baseEnd_3523435 < baseStart_3523435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523449 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 3, 4]
def baseStart_3523449 : Nat := 118140960795 + 3523449 * 2 ^ 59
def prefixEnd_3523449 : Nat := 4983230072969 + 3 ^ 40 * 3523449 * 2
def baseEnd_3523449 : Nat := 603074299534563407761153

theorem tailTrace_3523449 : CollatzResearch.WordTrace tailWord_3523449 prefixEnd_3523449 603074299534563407761153 := by
  unfold tailWord_3523449
  simp only [CollatzResearch.WordTrace]
  refine ⟨128510742612153505025973401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85673828408102336683982267 128510742612153505025973401)
  ·
    refine ⟨96383056959115128769480051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128510742612153505025973401 96383056959115128769480051)
    ·
      refine ⟨144574585438672693154220077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96383056959115128769480051 144574585438672693154220077)
      ·
        refine ⟨54215469539502259932832529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144574585438672693154220077 54215469539502259932832529)
        ·
          refine ⟨40661602154626694949624397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54215469539502259932832529 40661602154626694949624397)
          ·
            refine ⟨15248100807985010606109149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40661602154626694949624397 15248100807985010606109149)
            ·
              refine ⟨5718037802994378977290931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15248100807985010606109149 5718037802994378977290931)
              ·
                refine ⟨8577056704491568465936397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5718037802994378977290931 8577056704491568465936397)
                ·
                  refine ⟨3216396264184338174726149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8577056704491568465936397 3216396264184338174726149)
                  ·
                    refine ⟨603074299534563407761153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3216396264184338174726149 603074299534563407761153)
                    ·
                      rfl

theorem cell23_3523449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 3, 4].length) (baseStart_3523449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523449 prefixEnd_3523449 := by exact prefixLift 3523449
  have htrace : WordTrace (prefixWord ++ tailWord_3523449) baseStart_3523449 baseEnd_3523449 := by
    simpa [prefixWord, tailWord_3523449, baseEnd_3523449] using wordTrace_append hprefix tailTrace_3523449
  have hstable : (prefixWord ++ tailWord_3523449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523449).length < 2 ^ (prefixWord ++ tailWord_3523449).sum := by decide
  have hdescent : baseEnd_3523449 < baseStart_3523449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523476 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_3523476 : Nat := 118140960795 + 3523476 * 2 ^ 59
def prefixEnd_3523476 : Nat := 4983230072969 + 3 ^ 40 * 3523476 * 2
def baseEnd_3523476 : Nat := 1809236762581361617645835

theorem tailTrace_3523476 : CollatzResearch.WordTrace tailWord_3523476 prefixEnd_3523476 1809236762581361617645835 := by
  unfold tailWord_3523476
  simp only [CollatzResearch.WordTrace]
  refine ⟨64255863691527844318603141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85674484922037125758137521 64255863691527844318603141)
  ·
    refine ⟨12047974442161470809738089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64255863691527844318603141 12047974442161470809738089)
    ·
      refine ⟨9035980831621103107303567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12047974442161470809738089 9035980831621103107303567)
      ·
        refine ⟨13553971247431654660955351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9035980831621103107303567 13553971247431654660955351)
        ·
          refine ⟨20330956871147481991433027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13553971247431654660955351 20330956871147481991433027)
          ·
            refine ⟨30496435306721222987149541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20330956871147481991433027 30496435306721222987149541)
            ·
              refine ⟨5718081620010229310090539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30496435306721222987149541 5718081620010229310090539)
              ·
                refine ⟨8577122430015343965135809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5718081620010229310090539 8577122430015343965135809)
                ·
                  refine ⟨6432841822511507973851857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8577122430015343965135809 6432841822511507973851857)
                  ·
                    refine ⟨4824631366883630980388893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6432841822511507973851857 4824631366883630980388893)
                    ·
                      refine ⟨1809236762581361617645835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4824631366883630980388893 1809236762581361617645835)
                      ·
                        rfl

theorem cell23_3523476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_3523476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523476 prefixEnd_3523476 := by exact prefixLift 3523476
  have htrace : WordTrace (prefixWord ++ tailWord_3523476) baseStart_3523476 baseEnd_3523476 := by
    simpa [prefixWord, tailWord_3523476, baseEnd_3523476] using wordTrace_append hprefix tailTrace_3523476
  have hstable : (prefixWord ++ tailWord_3523476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523476).length < 2 ^ (prefixWord ++ tailWord_3523476).sum := by decide
  have hdescent : baseEnd_3523476 < baseStart_3523476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523540 : List Nat := [2, 4, 1, 2, 1, 3, 2, 3, 1, 1, 3]
def baseStart_3523540 : Nat := 118140960795 + 3523540 * 2 ^ 59
def prefixEnd_3523540 : Nat := 4983230072969 + 3 ^ 40 * 3523540 * 2
def baseEnd_3523540 : Nat := 1809269625343249367245541

theorem tailTrace_3523540 : CollatzResearch.WordTrace tailWord_3523540 prefixEnd_3523540 1809269625343249367245541 := by
  unfold tailWord_3523540
  simp only [CollatzResearch.WordTrace]
  refine ⟨64257030827411913783768037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85676041103215885045024049 64257030827411913783768037)
  ·
    refine ⟨12048193280139733834456507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64257030827411913783768037 12048193280139733834456507)
    ·
      refine ⟨18072289920209600751684761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12048193280139733834456507 18072289920209600751684761)
      ·
        refine ⟨13554217440157200563763571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18072289920209600751684761 13554217440157200563763571)
        ·
          refine ⟨20331326160235800845645357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13554217440157200563763571 20331326160235800845645357)
          ·
            refine ⟨7624247310088425317117009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20331326160235800845645357 7624247310088425317117009)
            ·
              refine ⟨5718185482566318987837757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7624247310088425317117009 5718185482566318987837757)
              ·
                refine ⟨2144319555962369620439159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5718185482566318987837757 2144319555962369620439159)
                ·
                  refine ⟨3216479333943554430658739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2144319555962369620439159 3216479333943554430658739)
                  ·
                    refine ⟨4824719000915331645988109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3216479333943554430658739 4824719000915331645988109)
                    ·
                      refine ⟨1809269625343249367245541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4824719000915331645988109 1809269625343249367245541)
                      ·
                        rfl

theorem cell23_3523540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_3523540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523540 prefixEnd_3523540 := by exact prefixLift 3523540
  have htrace : WordTrace (prefixWord ++ tailWord_3523540) baseStart_3523540 baseEnd_3523540 := by
    simpa [prefixWord, tailWord_3523540, baseEnd_3523540] using wordTrace_append hprefix tailTrace_3523540
  have hstable : (prefixWord ++ tailWord_3523540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523540).length < 2 ^ (prefixWord ++ tailWord_3523540).sum := by decide
  have hdescent : baseEnd_3523540 < baseStart_3523540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523546 : List Nat := [3, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4]
def baseStart_3523546 : Nat := 118140960795 + 3523546 * 2 ^ 59
def prefixEnd_3523546 : Nat := 4983230072969 + 3 ^ 40 * 3523546 * 2
def baseEnd_3523546 : Nat := 1809272706227176343770513

theorem tailTrace_3523546 : CollatzResearch.WordTrace tailWord_3523546 prefixEnd_3523546 1809272706227176343770513 := by
  unfold tailWord_3523546
  simp only [CollatzResearch.WordTrace]
  refine ⟨32128570123200522648063623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85676186995201393728169661 32128570123200522648063623)
  ·
    refine ⟨48192855184800783972095435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32128570123200522648063623 48192855184800783972095435)
    ·
      refine ⟨72289282777201175958143153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48192855184800783972095435 72289282777201175958143153)
      ·
        refine ⟨54216962082900881968607365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72289282777201175958143153 54216962082900881968607365)
        ·
          refine ⟨10165680390543915369113881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54216962082900881968607365 10165680390543915369113881)
          ·
            refine ⟨7624260292907936526835411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10165680390543915369113881 7624260292907936526835411)
            ·
              refine ⟨11436390439361904790253117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7624260292907936526835411 11436390439361904790253117)
              ·
                refine ⟨4288646414760714296344919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11436390439361904790253117 4288646414760714296344919)
                ·
                  refine ⟨6432969622141071444517379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4288646414760714296344919 6432969622141071444517379)
                  ·
                    refine ⟨9649454433211607166776069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6432969622141071444517379 9649454433211607166776069)
                    ·
                      refine ⟨1809272706227176343770513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9649454433211607166776069 1809272706227176343770513)
                      ·
                        rfl

theorem cell23_3523546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_3523546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523546 prefixEnd_3523546 := by exact prefixLift 3523546
  have htrace : WordTrace (prefixWord ++ tailWord_3523546) baseStart_3523546 baseEnd_3523546 := by
    simpa [prefixWord, tailWord_3523546, baseEnd_3523546] using wordTrace_append hprefix tailTrace_3523546
  have hstable : (prefixWord ++ tailWord_3523546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523546).length < 2 ^ (prefixWord ++ tailWord_3523546).sum := by decide
  have hdescent : baseEnd_3523546 < baseStart_3523546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523566 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_3523566 : Nat := 118140960795 + 3523566 * 2 ^ 59
def prefixEnd_3523566 : Nat := 4983230072969 + 3 ^ 40 * 3523566 * 2
def baseEnd_3523566 : Nat := 1809282975840266265520421

theorem tailTrace_3523566 : CollatzResearch.WordTrace tailWord_3523566 prefixEnd_3523566 1809282975840266265520421 := by
  unfold tailWord_3523566
  simp only [CollatzResearch.WordTrace]
  refine ⟨16064376244091204250997819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85676673301819756005321701 16064376244091204250997819)
  ·
    refine ⟨24096564366136806376496729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16064376244091204250997819 24096564366136806376496729)
    ·
      refine ⟨18072423274602604782372547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24096564366136806376496729 18072423274602604782372547)
      ·
        refine ⟨27108634911903907173558821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18072423274602604782372547 27108634911903907173558821)
        ·
          refine ⟨5082869045981982595042279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27108634911903907173558821 5082869045981982595042279)
          ·
            refine ⟨7624303568972973892563419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5082869045981982595042279 7624303568972973892563419)
            ·
              refine ⟨11436455353459460838845129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7624303568972973892563419 11436455353459460838845129)
              ·
                refine ⟨8577341515094595629133847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11436455353459460838845129 8577341515094595629133847)
                ·
                  refine ⟨12866012272641893443700771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8577341515094595629133847 12866012272641893443700771)
                  ·
                    refine ⟨19299018408962840165551157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12866012272641893443700771 19299018408962840165551157)
                    ·
                      refine ⟨1809282975840266265520421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19299018408962840165551157 1809282975840266265520421)
                      ·
                        rfl

theorem cell23_3523566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_3523566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523566 prefixEnd_3523566 := by exact prefixLift 3523566
  have htrace : WordTrace (prefixWord ++ tailWord_3523566) baseStart_3523566 baseEnd_3523566 := by
    simpa [prefixWord, tailWord_3523566, baseEnd_3523566] using wordTrace_append hprefix tailTrace_3523566
  have hstable : (prefixWord ++ tailWord_3523566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523566).length < 2 ^ (prefixWord ++ tailWord_3523566).sum := by decide
  have hdescent : baseEnd_3523566 < baseStart_3523566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523596 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 4, 1, 3]
def baseStart_3523596 : Nat := 118140960795 + 3523596 * 2 ^ 59
def prefixEnd_3523596 : Nat := 4983230072969 + 3 ^ 40 * 3523596 * 2
def baseEnd_3523596 : Nat := 1809298380259901148145283

theorem tailTrace_3523596 : CollatzResearch.WordTrace tailWord_3523596 prefixEnd_3523596 1809298380259901148145283 := by
  unfold tailWord_3523596
  simp only [CollatzResearch.WordTrace]
  refine ⟨64258052071310474565787321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85677402761747299421049761 64258052071310474565787321)
  ·
    refine ⟨48193539053482855924340491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64258052071310474565787321 48193539053482855924340491)
    ·
      refine ⟨72290308580224283886510737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48193539053482855924340491 72290308580224283886510737)
      ·
        refine ⟨54217731435168212914883053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72290308580224283886510737 54217731435168212914883053)
        ·
          refine ⟨20331649288188079843081145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54217731435168212914883053 20331649288188079843081145)
          ·
            refine ⟨15248736966141059882310859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20331649288188079843081145 15248736966141059882310859)
            ·
              refine ⟨22873105449211589823466289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15248736966141059882310859 22873105449211589823466289)
              ·
                refine ⟨17154829086908692367599717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22873105449211589823466289 17154829086908692367599717)
                ·
                  refine ⟨3216530453795379818924947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17154829086908692367599717 3216530453795379818924947)
                  ·
                    refine ⟨4824795680693069728387421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3216530453795379818924947 4824795680693069728387421)
                    ·
                      refine ⟨1809298380259901148145283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4824795680693069728387421 1809298380259901148145283)
                      ·
                        rfl

theorem cell23_3523596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_3523596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523596 prefixEnd_3523596 := by exact prefixLift 3523596
  have htrace : WordTrace (prefixWord ++ tailWord_3523596) baseStart_3523596 baseEnd_3523596 := by
    simpa [prefixWord, tailWord_3523596, baseEnd_3523596] using wordTrace_append hprefix tailTrace_3523596
  have hstable : (prefixWord ++ tailWord_3523596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523596).length < 2 ^ (prefixWord ++ tailWord_3523596).sum := by decide
  have hdescent : baseEnd_3523596 < baseStart_3523596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523640 : List Nat := [2, 1, 2, 1, 5, 3, 1, 2, 1, 3, 2]
def baseStart_3523640 : Nat := 118140960795 + 3523640 * 2 ^ 59
def prefixEnd_3523640 : Nat := 4983230072969 + 3 ^ 40 * 3523640 * 2
def baseEnd_3523640 : Nat := 1809320973408698975995081

theorem tailTrace_3523640 : CollatzResearch.WordTrace tailWord_3523640 prefixEnd_3523640 1809320973408698975995081 := by
  unfold tailWord_3523640
  simp only [CollatzResearch.WordTrace]
  refine ⟨64258854477230772323088187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85678472636307696430784249 64258854477230772323088187)
  ·
    refine ⟨96388281715846158484632281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64258854477230772323088187 96388281715846158484632281)
    ·
      refine ⟨72291211286884618863474211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96388281715846158484632281 72291211286884618863474211)
      ·
        refine ⟨108436816930326928295211317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72291211286884618863474211 108436816930326928295211317)
        ·
          refine ⟨10165951587218149527676061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108436816930326928295211317 10165951587218149527676061)
          ·
            refine ⟨3812231845206806072878523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10165951587218149527676061 3812231845206806072878523)
            ·
              refine ⟨5718347767810209109317785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3812231845206806072878523 5718347767810209109317785)
              ·
                refine ⟨4288760825857656831988339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5718347767810209109317785 4288760825857656831988339)
                ·
                  refine ⟨6433141238786485247982509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4288760825857656831988339 6433141238786485247982509)
                  ·
                    refine ⟨2412427964544931967993441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6433141238786485247982509 2412427964544931967993441)
                    ·
                      refine ⟨1809320973408698975995081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2412427964544931967993441 1809320973408698975995081)
                      ·
                        rfl

theorem cell23_3523640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 1, 3, 2].length) (baseStart_3523640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523640 prefixEnd_3523640 := by exact prefixLift 3523640
  have htrace : WordTrace (prefixWord ++ tailWord_3523640) baseStart_3523640 baseEnd_3523640 := by
    simpa [prefixWord, tailWord_3523640, baseEnd_3523640] using wordTrace_append hprefix tailTrace_3523640
  have hstable : (prefixWord ++ tailWord_3523640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523640).length < 2 ^ (prefixWord ++ tailWord_3523640).sum := by decide
  have hdescent : baseEnd_3523640 < baseStart_3523640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523696 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 2, 5, 2]
def baseStart_3523696 : Nat := 118140960795 + 3523696 * 2 ^ 59
def prefixEnd_3523696 : Nat := 4983230072969 + 3 ^ 40 * 3523696 * 2
def baseEnd_3523696 : Nat := 1809349728325350756894823

theorem tailTrace_3523696 : CollatzResearch.WordTrace tailWord_3523696 prefixEnd_3523696 1809349728325350756894823 := by
  unfold tailWord_3523696
  simp only [CollatzResearch.WordTrace]
  refine ⟨64259875721129333105107471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85679834294839110806809961 64259875721129333105107471)
  ·
    refine ⟨96389813581693999657661207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64259875721129333105107471 96389813581693999657661207)
    ·
      refine ⟨144584720372540999486491811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96389813581693999657661207 144584720372540999486491811)
      ·
        refine ⟨216877080558811499229737717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144584720372540999486491811 216877080558811499229737717)
        ·
          refine ⟨20332226302388578052787911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216877080558811499229737717 20332226302388578052787911)
          ·
            refine ⟨30498339453582867079181867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20332226302388578052787911 30498339453582867079181867)
            ·
              refine ⟨45747509180374300618772801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30498339453582867079181867 45747509180374300618772801)
              ·
                refine ⟨34310631885280725464079601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45747509180374300618772801 34310631885280725464079601)
                ·
                  refine ⟨25732973913960544098059701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34310631885280725464079601 25732973913960544098059701)
                  ·
                    refine ⟨2412466304433801009193097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25732973913960544098059701 2412466304433801009193097)
                    ·
                      refine ⟨1809349728325350756894823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2412466304433801009193097 1809349728325350756894823)
                      ·
                        rfl

theorem cell23_3523696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 2, 5, 2].length) (baseStart_3523696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523696 prefixEnd_3523696 := by exact prefixLift 3523696
  have htrace : WordTrace (prefixWord ++ tailWord_3523696) baseStart_3523696 baseEnd_3523696 := by
    simpa [prefixWord, tailWord_3523696, baseEnd_3523696] using wordTrace_append hprefix tailTrace_3523696
  have hstable : (prefixWord ++ tailWord_3523696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523696).length < 2 ^ (prefixWord ++ tailWord_3523696).sum := by decide
  have hdescent : baseEnd_3523696 < baseStart_3523696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523780 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_3523780 : Nat := 118140960795 + 3523780 * 2 ^ 59
def prefixEnd_3523780 : Nat := 4983230072969 + 3 ^ 40 * 3523780 * 2
def baseEnd_3523780 : Nat := 1809392860700328428244437

theorem tailTrace_3523780 : CollatzResearch.WordTrace tailWord_3523780 prefixEnd_3523780 1809392860700328428244437 := by
  unfold tailWord_3523780
  simp only [CollatzResearch.WordTrace]
  refine ⟨64261407586977174278136397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85681876782636232370848529 64261407586977174278136397)
  ·
    refine ⟨24098027845116440354301149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64261407586977174278136397 24098027845116440354301149)
    ·
      refine ⟨9036760441918665132862931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24098027845116440354301149 9036760441918665132862931)
      ·
        refine ⟨13555140662877997699294397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9036760441918665132862931 13555140662877997699294397)
        ·
          refine ⟨5083177748579249137235399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13555140662877997699294397 5083177748579249137235399)
          ·
            refine ⟨7624766622868873705853099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5083177748579249137235399 7624766622868873705853099)
            ·
              refine ⟨11437149934303310558779649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7624766622868873705853099 11437149934303310558779649)
              ·
                refine ⟨8577862450727482919084737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11437149934303310558779649 8577862450727482919084737)
                ·
                  refine ⟨6433396838045612189313553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8577862450727482919084737 6433396838045612189313553)
                  ·
                    refine ⟨4825047628534209141985165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6433396838045612189313553 4825047628534209141985165)
                    ·
                      refine ⟨1809392860700328428244437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4825047628534209141985165 1809392860700328428244437)
                      ·
                        rfl

theorem cell23_3523780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_3523780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523780 prefixEnd_3523780 := by exact prefixLift 3523780
  have htrace : WordTrace (prefixWord ++ tailWord_3523780) baseStart_3523780 baseEnd_3523780 := by
    simpa [prefixWord, tailWord_3523780, baseEnd_3523780] using wordTrace_append hprefix tailTrace_3523780
  have hstable : (prefixWord ++ tailWord_3523780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523780).length < 2 ^ (prefixWord ++ tailWord_3523780).sum := by decide
  have hdescent : baseEnd_3523780 < baseStart_3523780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523800 : List Nat := [2, 1, 2, 2, 5, 2, 2, 1, 6]
def baseStart_3523800 : Nat := 118140960795 + 3523800 * 2 ^ 59
def prefixEnd_3523800 : Nat := 4983230072969 + 3 ^ 40 * 3523800 * 2
def baseEnd_3523800 : Nat := 201044792257046483332705

theorem tailTrace_3523800 : CollatzResearch.WordTrace tailWord_3523800 prefixEnd_3523800 201044792257046483332705 := by
  unfold tailWord_3523800
  simp only [CollatzResearch.WordTrace]
  refine ⟨64261772316940945986000427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85682363089254594648000569 64261772316940945986000427)
  ·
    refine ⟨96392658475411418979000641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64261772316940945986000427 96392658475411418979000641)
    ·
      refine ⟨72294493856558564234250481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96392658475411418979000641 72294493856558564234250481)
      ·
        refine ⟨54220870392418923175687861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72294493856558564234250481 54220870392418923175687861)
        ·
          refine ⟨5083206599289274047720737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54220870392418923175687861 5083206599289274047720737)
          ·
            refine ⟨3812404949466955535790553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5083206599289274047720737 3812404949466955535790553)
            ·
              refine ⟨2859303712100216651842915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3812404949466955535790553 2859303712100216651842915)
              ·
                refine ⟨4288955568150324977764373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2859303712100216651842915 4288955568150324977764373)
                ·
                  refine ⟨201044792257046483332705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4288955568150324977764373 201044792257046483332705)
                  ·
                    rfl

theorem cell23_3523800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 6].length) (baseStart_3523800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523800 prefixEnd_3523800 := by exact prefixLift 3523800
  have htrace : WordTrace (prefixWord ++ tailWord_3523800) baseStart_3523800 baseEnd_3523800 := by
    simpa [prefixWord, tailWord_3523800, baseEnd_3523800] using wordTrace_append hprefix tailTrace_3523800
  have hstable : (prefixWord ++ tailWord_3523800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523800).length < 2 ^ (prefixWord ++ tailWord_3523800).sum := by decide
  have hdescent : baseEnd_3523800 < baseStart_3523800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523813 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 3, 5]
def baseStart_3523813 : Nat := 118140960795 + 3523813 * 2 ^ 59
def prefixEnd_3523813 : Nat := 4983230072969 + 3 ^ 40 * 3523813 * 2
def baseEnd_3523813 : Nat := 603136601853975599710595

theorem tailTrace_3523813 : CollatzResearch.WordTrace tailWord_3523813 prefixEnd_3523813 603136601853975599710595 := by
  unfold tailWord_3523813
  simp only [CollatzResearch.WordTrace]
  refine ⟨128524018782834795192224093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85682679188556530128149395 128524018782834795192224093)
  ·
    refine ⟨48196507043563048197084035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128524018782834795192224093 48196507043563048197084035)
    ·
      refine ⟨72294760565344572295626053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48196507043563048197084035 72294760565344572295626053)
      ·
        refine ⟨13555267606002107305429885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72294760565344572295626053 13555267606002107305429885)
        ·
          refine ⟨5083225352250790239536207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13555267606002107305429885 5083225352250790239536207)
          ·
            refine ⟨7624838028376185359304311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5083225352250790239536207 7624838028376185359304311)
            ·
              refine ⟨11437257042564278038956467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7624838028376185359304311 11437257042564278038956467)
              ·
                refine ⟨17155885563846417058434701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11437257042564278038956467 17155885563846417058434701)
                ·
                  refine ⟨6433457086442406396913013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17155885563846417058434701 6433457086442406396913013)
                  ·
                    refine ⟨603136601853975599710595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6433457086442406396913013 603136601853975599710595)
                    ·
                      rfl

theorem cell23_3523813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_3523813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523813 prefixEnd_3523813 := by exact prefixLift 3523813
  have htrace : WordTrace (prefixWord ++ tailWord_3523813) baseStart_3523813 baseEnd_3523813 := by
    simpa [prefixWord, tailWord_3523813, baseEnd_3523813] using wordTrace_append hprefix tailTrace_3523813
  have hstable : (prefixWord ++ tailWord_3523813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523813).length < 2 ^ (prefixWord ++ tailWord_3523813).sum := by decide
  have hdescent : baseEnd_3523813 < baseStart_3523813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523820 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 2, 3, 2]
def baseStart_3523820 : Nat := 118140960795 + 3523820 * 2 ^ 59
def prefixEnd_3523820 : Nat := 4983230072969 + 3 ^ 40 * 3523820 * 2
def baseEnd_3523820 : Nat := 1809413399926508271744253

theorem tailTrace_3523820 : CollatzResearch.WordTrace tailWord_3523820 prefixEnd_3523820 1809413399926508271744253 := by
  unfold tailWord_3523820
  simp only [CollatzResearch.WordTrace]
  refine ⟨64262137046904717693864457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85682849395872956925152609 64262137046904717693864457)
  ·
    refine ⟨48196602785178538270398343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64262137046904717693864457 48196602785178538270398343)
    ·
      refine ⟨72294904177767807405597515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48196602785178538270398343 72294904177767807405597515)
      ·
        refine ⟨108442356266651711108396273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72294904177767807405597515 108442356266651711108396273)
        ·
          refine ⟨81331767199988783331297205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108442356266651711108396273 81331767199988783331297205)
          ·
            refine ⟨7624853174998948437309113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81331767199988783331297205 7624853174998948437309113)
            ·
              refine ⟨5718639881249211327981835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7624853174998948437309113 5718639881249211327981835)
              ·
                refine ⟨8577959821873816991972753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5718639881249211327981835 8577959821873816991972753)
                ·
                  refine ⟨6433469866405362743979565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8577959821873816991972753 6433469866405362743979565)
                  ·
                    refine ⟨2412551199902011028992337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6433469866405362743979565 2412551199902011028992337)
                    ·
                      refine ⟨1809413399926508271744253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2412551199902011028992337 1809413399926508271744253)
                      ·
                        rfl

theorem cell23_3523820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 3, 2].length) (baseStart_3523820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523820 prefixEnd_3523820 := by exact prefixLift 3523820
  have htrace : WordTrace (prefixWord ++ tailWord_3523820) baseStart_3523820 baseEnd_3523820 := by
    simpa [prefixWord, tailWord_3523820, baseEnd_3523820] using wordTrace_append hprefix tailTrace_3523820
  have hstable : (prefixWord ++ tailWord_3523820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523820).length < 2 ^ (prefixWord ++ tailWord_3523820).sum := by decide
  have hdescent : baseEnd_3523820 < baseStart_3523820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523839 : List Nat := [1, 1, 2, 2, 1, 16]
def baseStart_3523839 : Nat := 118140960795 + 3523839 * 2 ^ 59
def prefixEnd_3523839 : Nat := 4983230072969 + 3 ^ 40 * 3523839 * 2
def baseEnd_3523839 : Nat := 7446185827403060483155

theorem tailTrace_3523839 : CollatzResearch.WordTrace tailWord_3523839 prefixEnd_3523839 7446185827403060483155 := by
  unfold tailWord_3523839
  simp only [CollatzResearch.WordTrace]
  refine ⟨128524967080740601632670571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85683311387160401088447047 128524967080740601632670571)
  ·
    refine ⟨192787450621110902449005857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128524967080740601632670571 192787450621110902449005857)
    ·
      refine ⟨144590587965833176836754393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192787450621110902449005857 144590587965833176836754393)
      ·
        refine ⟨108442940974374882627565795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144590587965833176836754393 108442940974374882627565795)
        ·
          refine ⟨162664411461562323941348693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108442940974374882627565795 162664411461562323941348693)
          ·
            refine ⟨7446185827403060483155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 162664411461562323941348693 7446185827403060483155)
            ·
              rfl

theorem cell23_3523839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 16].length) (baseStart_3523839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523839 prefixEnd_3523839 := by exact prefixLift 3523839
  have htrace : WordTrace (prefixWord ++ tailWord_3523839) baseStart_3523839 baseEnd_3523839 := by
    simpa [prefixWord, tailWord_3523839, baseEnd_3523839] using wordTrace_append hprefix tailTrace_3523839
  have hstable : (prefixWord ++ tailWord_3523839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523839).length < 2 ^ (prefixWord ++ tailWord_3523839).sum := by decide
  have hdescent : baseEnd_3523839 < baseStart_3523839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523843 : List Nat := [1, 1, 1, 3, 2, 4, 1, 4, 2, 4]
def baseStart_3523843 : Nat := 118140960795 + 3523843 * 2 ^ 59
def prefixEnd_3523843 : Nat := 4983230072969 + 3 ^ 40 * 3523843 * 2
def baseEnd_3523843 : Nat := 603141736660520560585549

theorem tailTrace_3523843 : CollatzResearch.WordTrace tailWord_3523843 prefixEnd_3523843 603141736660520560585549 := by
  unfold tailWord_3523843
  simp only [CollatzResearch.WordTrace]
  refine ⟨128525112972726110315816183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85683408648484073543877455 128525112972726110315816183)
  ·
    refine ⟨192787669459089165473724275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128525112972726110315816183 192787669459089165473724275)
    ·
      refine ⟨289181504188633748210586413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192787669459089165473724275 289181504188633748210586413)
      ·
        refine ⟨108443064070737655578969905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289181504188633748210586413 108443064070737655578969905)
        ·
          refine ⟨81332298053053241684227429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108443064070737655578969905 81332298053053241684227429)
          ·
            refine ⟨15249805884947482815792643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81332298053053241684227429 15249805884947482815792643)
            ·
              refine ⟨22874708827421224223688965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15249805884947482815792643 22874708827421224223688965)
              ·
                refine ⟨4289007905141479541941681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22874708827421224223688965 4289007905141479541941681)
                ·
                  refine ⟨3216755928856109656456261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4289007905141479541941681 3216755928856109656456261)
                  ·
                    refine ⟨603141736660520560585549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3216755928856109656456261 603141736660520560585549)
                    ·
                      rfl

theorem cell23_3523843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 4].length) (baseStart_3523843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523843 prefixEnd_3523843 := by exact prefixLift 3523843
  have htrace : WordTrace (prefixWord ++ tailWord_3523843) baseStart_3523843 baseEnd_3523843 := by
    simpa [prefixWord, tailWord_3523843, baseEnd_3523843] using wordTrace_append hprefix tailTrace_3523843
  have hstable : (prefixWord ++ tailWord_3523843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523843).length < 2 ^ (prefixWord ++ tailWord_3523843).sum := by decide
  have hdescent : baseEnd_3523843 < baseStart_3523843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523844 : List Nat := [2, 3, 2, 2, 2, 1, 4, 2, 1, 1, 3]
def baseStart_3523844 : Nat := 118140960795 + 3523844 * 2 ^ 59
def prefixEnd_3523844 : Nat := 4983230072969 + 3 ^ 40 * 3523844 * 2
def baseEnd_3523844 : Nat := 1809425723462216177844143

theorem tailTrace_3523844 : CollatzResearch.WordTrace tailWord_3523844 prefixEnd_3523844 1809425723462216177844143 := by
  unfold tailWord_3523844
  simp only [CollatzResearch.WordTrace]
  refine ⟨64262574722861243743301293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85683432963814991657735057 64262574722861243743301293)
  ·
    refine ⟨24098465521072966403737985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64262574722861243743301293 24098465521072966403737985)
    ·
      refine ⟨18073849140804724802803489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24098465521072966403737985 18073849140804724802803489)
      ·
        refine ⟨13555386855603543602102617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18073849140804724802803489 13555386855603543602102617)
        ·
          refine ⟨10166540141702657701576963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13555386855603543602102617 10166540141702657701576963)
          ·
            refine ⟨15249810212553986552365445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10166540141702657701576963 15249810212553986552365445)
            ·
              refine ⟨2859339414853872478568521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15249810212553986552365445 2859339414853872478568521)
              ·
                refine ⟨2144504561140404358926391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2859339414853872478568521 2144504561140404358926391)
                ·
                  refine ⟨3216756841710606538389587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2144504561140404358926391 3216756841710606538389587)
                  ·
                    refine ⟨4825135262565909807584381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3216756841710606538389587 4825135262565909807584381)
                    ·
                      refine ⟨1809425723462216177844143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4825135262565909807584381 1809425723462216177844143)
                      ·
                        rfl

theorem cell23_3523844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_3523844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523844 prefixEnd_3523844 := by exact prefixLift 3523844
  have htrace : WordTrace (prefixWord ++ tailWord_3523844) baseStart_3523844 baseEnd_3523844 := by
    simpa [prefixWord, tailWord_3523844, baseEnd_3523844] using wordTrace_append hprefix tailTrace_3523844
  have hstable : (prefixWord ++ tailWord_3523844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523844).length < 2 ^ (prefixWord ++ tailWord_3523844).sum := by decide
  have hdescent : baseEnd_3523844 < baseStart_3523844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523850 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2]
def baseStart_3523850 : Nat := 118140960795 + 3523850 * 2 ^ 59
def prefixEnd_3523850 : Nat := 4983230072969 + 3 ^ 40 * 3523850 * 2
def baseEnd_3523850 : Nat := 1809428804346143154369115

theorem tailTrace_3523850 : CollatzResearch.WordTrace tailWord_3523850 prefixEnd_3523850 1809428804346143154369115 := by
  unfold tailWord_3523850
  simp only [CollatzResearch.WordTrace]
  refine ⟨32131342070925187627830251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85683578855800500340880669 32131342070925187627830251)
  ·
    refine ⟨48197013106387781441745377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32131342070925187627830251 48197013106387781441745377)
    ·
      refine ⟨36147759829790836081309033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48197013106387781441745377 36147759829790836081309033)
      ·
        refine ⟨27110819872343127060981775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36147759829790836081309033 27110819872343127060981775)
        ·
          refine ⟨40666229808514690591472663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27110819872343127060981775 40666229808514690591472663)
          ·
            refine ⟨60999344712772035887208995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40666229808514690591472663 60999344712772035887208995)
            ·
              refine ⟨91499017069158053830813493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60999344712772035887208995 91499017069158053830813493)
              ·
                refine ⟨8578032850233567546638765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91499017069158053830813493 8578032850233567546638765)
                ·
                  refine ⟨3216762318837587829989537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8578032850233567546638765 3216762318837587829989537)
                  ·
                    refine ⟨2412571739128190872492153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3216762318837587829989537 2412571739128190872492153)
                    ·
                      refine ⟨1809428804346143154369115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2412571739128190872492153 1809428804346143154369115)
                      ·
                        rfl

theorem cell23_3523850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_3523850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523850 prefixEnd_3523850 := by exact prefixLift 3523850
  have htrace : WordTrace (prefixWord ++ tailWord_3523850) baseStart_3523850 baseEnd_3523850 := by
    simpa [prefixWord, tailWord_3523850, baseEnd_3523850] using wordTrace_append hprefix tailTrace_3523850
  have hstable : (prefixWord ++ tailWord_3523850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523850).length < 2 ^ (prefixWord ++ tailWord_3523850).sum := by decide
  have hdescent : baseEnd_3523850 < baseStart_3523850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523863 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 4]
def baseStart_3523863 : Nat := 118140960795 + 3523863 * 2 ^ 59
def prefixEnd_3523863 : Nat := 4983230072969 + 3 ^ 40 * 3523863 * 2
def baseEnd_3523863 : Nat := 1809435479594651603506555

theorem tailTrace_3523863 : CollatzResearch.WordTrace tailWord_3523863 prefixEnd_3523863 1809435479594651603506555 := by
  unfold tailWord_3523863
  simp only [CollatzResearch.WordTrace]
  refine ⟨128525842432653653731544243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85683894955102435821029495 128525842432653653731544243)
  ·
    refine ⟨192788763648980480597316365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128525842432653653731544243 192788763648980480597316365)
    ·
      refine ⟨72295786368367680223993637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192788763648980480597316365 72295786368367680223993637)
      ·
        refine ⟨13555459944068940041998807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72295786368367680223993637 13555459944068940041998807)
        ·
          refine ⟨20333189916103410062998211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13555459944068940041998807 20333189916103410062998211)
          ·
            refine ⟨30499784874155115094497317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20333189916103410062998211 30499784874155115094497317)
            ·
              refine ⟨5718709663904084080218247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30499784874155115094497317 5718709663904084080218247)
              ·
                refine ⟨8578064495856126120327371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5718709663904084080218247 8578064495856126120327371)
                ·
                  refine ⟨12867096743784189180491057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8578064495856126120327371 12867096743784189180491057)
                  ·
                    refine ⟨9650322557838141885368293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12867096743784189180491057 9650322557838141885368293)
                    ·
                      refine ⟨1809435479594651603506555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9650322557838141885368293 1809435479594651603506555)
                      ·
                        rfl

theorem cell23_3523863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_3523863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523863 prefixEnd_3523863 := by exact prefixLift 3523863
  have htrace : WordTrace (prefixWord ++ tailWord_3523863) baseStart_3523863 baseEnd_3523863 := by
    simpa [prefixWord, tailWord_3523863, baseEnd_3523863] using wordTrace_append hprefix tailTrace_3523863
  have hstable : (prefixWord ++ tailWord_3523863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523863).length < 2 ^ (prefixWord ++ tailWord_3523863).sum := by decide
  have hdescent : baseEnd_3523863 < baseStart_3523863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523900 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 4, 1, 3]
def baseStart_3523900 : Nat := 118140960795 + 3523900 * 2 ^ 59
def prefixEnd_3523900 : Nat := 4983230072969 + 3 ^ 40 * 3523900 * 2
def baseEnd_3523900 : Nat := 1809454478378867958743885

theorem tailTrace_3523900 : CollatzResearch.WordTrace tailWord_3523900 prefixEnd_3523900 1809454478378867958743885 := by
  unfold tailWord_3523900
  simp only [CollatzResearch.WordTrace]
  refine ⟨64263595966759804525320577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85684794622346406033760769 64263595966759804525320577)
  ·
    refine ⟨48197696975069853393990433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64263595966759804525320577 48197696975069853393990433)
    ·
      refine ⟨36148272731302390045492825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48197696975069853393990433 36148272731302390045492825)
      ·
        refine ⟨27111204548476792534119619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36148272731302390045492825 27111204548476792534119619)
        ·
          refine ⟨40666806822715188801179429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27111204548476792534119619 40666806822715188801179429)
          ·
            refine ⟨7625026279259097900221143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40666806822715188801179429 7625026279259097900221143)
            ·
              refine ⟨11437539418888646850331715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7625026279259097900221143 11437539418888646850331715)
              ·
                refine ⟨17156309128332970275497573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11437539418888646850331715 17156309128332970275497573)
                ·
                  refine ⟨3216807961562431926655795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17156309128332970275497573 3216807961562431926655795)
                  ·
                    refine ⟨4825211942343647889983693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3216807961562431926655795 4825211942343647889983693)
                    ·
                      refine ⟨1809454478378867958743885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4825211942343647889983693 1809454478378867958743885)
                      ·
                        rfl

theorem cell23_3523900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_3523900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523900 prefixEnd_3523900 := by exact prefixLift 3523900
  have htrace : WordTrace (prefixWord ++ tailWord_3523900) baseStart_3523900 baseEnd_3523900 := by
    simpa [prefixWord, tailWord_3523900, baseEnd_3523900] using wordTrace_append hprefix tailTrace_3523900
  have hstable : (prefixWord ++ tailWord_3523900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523900).length < 2 ^ (prefixWord ++ tailWord_3523900).sum := by decide
  have hdescent : baseEnd_3523900 < baseStart_3523900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523927 : List Nat := [1, 1, 3, 2, 3, 3, 2, 2, 1, 3, 2]
def baseStart_3523927 : Nat := 118140960795 + 3523927 * 2 ^ 59
def prefixEnd_3523927 : Nat := 4983230072969 + 3 ^ 40 * 3523927 * 2
def baseEnd_3523927 : Nat := 1809468342356539353106261

theorem tailTrace_3523927 : CollatzResearch.WordTrace tailWord_3523927 prefixEnd_3523927 1809468342356539353106261 := by
  unfold tailWord_3523927
  simp only [CollatzResearch.WordTrace]
  refine ⟨128528176704421792661874035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85685451136281195107916023 128528176704421792661874035)
  ·
    refine ⟨192792265056632688992811053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128528176704421792661874035 192792265056632688992811053)
    ·
      refine ⟨72297099396237258372304145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192792265056632688992811053 72297099396237258372304145)
      ·
        refine ⟨54222824547177943779228109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72297099396237258372304145 54222824547177943779228109)
        ·
          refine ⟨20333559205191728917210541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54222824547177943779228109 20333559205191728917210541)
          ·
            refine ⟨7625084701946898343953953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20333559205191728917210541 7625084701946898343953953)
            ·
              refine ⟨5718813526460173757965465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7625084701946898343953953 5718813526460173757965465)
              ·
                refine ⟨4289110144845130318474099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5718813526460173757965465 4289110144845130318474099)
                ·
                  refine ⟨6433665217267695477711149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4289110144845130318474099 6433665217267695477711149)
                  ·
                    refine ⟨2412624456475385804141681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6433665217267695477711149 2412624456475385804141681)
                    ·
                      refine ⟨1809468342356539353106261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2412624456475385804141681 1809468342356539353106261)
                      ·
                        rfl

theorem cell23_3523927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_3523927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523927 prefixEnd_3523927 := by exact prefixLift 3523927
  have htrace : WordTrace (prefixWord ++ tailWord_3523927) baseStart_3523927 baseEnd_3523927 := by
    simpa [prefixWord, tailWord_3523927, baseEnd_3523927] using wordTrace_append hprefix tailTrace_3523927
  have hstable : (prefixWord ++ tailWord_3523927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523927).length < 2 ^ (prefixWord ++ tailWord_3523927).sum := by decide
  have hdescent : baseEnd_3523927 < baseStart_3523927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523973 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 2, 3, 3]
def baseStart_3523973 : Nat := 118140960795 + 3523973 * 2 ^ 59
def prefixEnd_3523973 : Nat := 4983230072969 + 3 ^ 40 * 3523973 * 2
def baseEnd_3523973 : Nat := 1809491962466646173131049

theorem tailTrace_3523973 : CollatzResearch.WordTrace tailWord_3523973 prefixEnd_3523973 1809491962466646173131049 := by
  unfold tailWord_3523973
  simp only [CollatzResearch.WordTrace]
  refine ⟨128529854462255142518048573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85686569641503428345365715 128529854462255142518048573)
  ·
    refine ⟨48198695423345678444268215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128529854462255142518048573 48198695423345678444268215)
    ·
      refine ⟨72298043135018517666402323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48198695423345678444268215 72298043135018517666402323)
      ·
        refine ⟨108447064702527776499603485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72298043135018517666402323 108447064702527776499603485)
        ·
          refine ⟨40667649263447916187351307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108447064702527776499603485 40667649263447916187351307)
          ·
            refine ⟨61001473895171874281026961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40667649263447916187351307 61001473895171874281026961)
            ·
              refine ⟨45751105421378905710770221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61001473895171874281026961 45751105421378905710770221)
              ·
                refine ⟨17156664533017089641538833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45751105421378905710770221 17156664533017089641538833)
                ·
                  refine ⟨12867498399762817231154125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17156664533017089641538833 12867498399762817231154125)
                  ·
                    refine ⟨4825311899911056461682797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12867498399762817231154125 4825311899911056461682797)
                    ·
                      refine ⟨1809491962466646173131049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4825311899911056461682797 1809491962466646173131049)
                      ·
                        rfl

theorem cell23_3523973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_3523973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523973 prefixEnd_3523973 := by exact prefixLift 3523973
  have htrace : WordTrace (prefixWord ++ tailWord_3523973) baseStart_3523973 baseEnd_3523973 := by
    simpa [prefixWord, tailWord_3523973, baseEnd_3523973] using wordTrace_append hprefix tailTrace_3523973
  have hstable : (prefixWord ++ tailWord_3523973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523973).length < 2 ^ (prefixWord ++ tailWord_3523973).sum := by decide
  have hdescent : baseEnd_3523973 < baseStart_3523973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523993 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 2, 5]
def baseStart_3523993 : Nat := 118140960795 + 3523993 * 2 ^ 59
def prefixEnd_3523993 : Nat := 4983230072969 + 3 ^ 40 * 3523993 * 2
def baseEnd_3523993 : Nat := 603167410693245364960319

theorem tailTrace_3523993 : CollatzResearch.WordTrace tailWord_3523993 prefixEnd_3523993 603167410693245364960319 := by
  unfold tailWord_3523993
  simp only [CollatzResearch.WordTrace]
  refine ⟨128530583922182685933776633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85687055948121790622517755 128530583922182685933776633)
  ·
    refine ⟨96397937941637014450332475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128530583922182685933776633 96397937941637014450332475)
    ·
      refine ⟨144596906912455521675498713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96397937941637014450332475 144596906912455521675498713)
      ·
        refine ⟨108447680184341641256624035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144596906912455521675498713 108447680184341641256624035)
        ·
          refine ⟨162671520276512461884936053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108447680184341641256624035 162671520276512461884936053)
          ·
            refine ⟨15250455025923043301712755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162671520276512461884936053 15250455025923043301712755)
            ·
              refine ⟨22875682538884564952569133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15250455025923043301712755 22875682538884564952569133)
              ·
                refine ⟨8578380952081711857213425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22875682538884564952569133 8578380952081711857213425)
                ·
                  refine ⟨6433785714061283892910069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8578380952081711857213425 6433785714061283892910069)
                  ·
                    refine ⟨603167410693245364960319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6433785714061283892910069 603167410693245364960319)
                    ·
                      rfl

theorem cell23_3523993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 5].length) (baseStart_3523993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3523993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3523993 prefixEnd_3523993 := by exact prefixLift 3523993
  have htrace : WordTrace (prefixWord ++ tailWord_3523993) baseStart_3523993 baseEnd_3523993 := by
    simpa [prefixWord, tailWord_3523993, baseEnd_3523993] using wordTrace_append hprefix tailTrace_3523993
  have hstable : (prefixWord ++ tailWord_3523993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523993).length < 2 ^ (prefixWord ++ tailWord_3523993).sum := by decide
  have hdescent : baseEnd_3523993 < baseStart_3523993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524040 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 3, 4]
def baseStart_3524040 : Nat := 118140960795 + 3524040 * 2 ^ 59
def prefixEnd_3524040 : Nat := 4983230072969 + 3 ^ 40 * 3524040 * 2
def baseEnd_3524040 : Nat := 603175455223499136997747

theorem tailTrace_3524040 : CollatzResearch.WordTrace tailWord_3524040 prefixEnd_3524040 603175455223499136997747 := by
  unfold tailWord_3524040
  simp only [CollatzResearch.WordTrace]
  refine ⟨64266149076506206480368787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85688198768674941973825049 64266149076506206480368787)
  ·
    refine ⟨96399223614759309720553181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64266149076506206480368787 96399223614759309720553181)
    ·
      refine ⟨36149708855534741145207443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96399223614759309720553181 36149708855534741145207443)
      ·
        refine ⟨54224563283302111717811165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36149708855534741145207443 54224563283302111717811165)
        ·
          refine ⟨20334211231238291894179187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54224563283302111717811165 20334211231238291894179187)
          ·
            refine ⟨30501316846857437841268781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20334211231238291894179187 30501316846857437841268781)
            ·
              refine ⟨11437993817571539190475793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30501316846857437841268781 11437993817571539190475793)
              ·
                refine ⟨8578495363178654392856845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11437993817571539190475793 8578495363178654392856845)
                ·
                  refine ⟨3216935761191995397321317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8578495363178654392856845 3216935761191995397321317)
                  ·
                    refine ⟨603175455223499136997747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3216935761191995397321317 603175455223499136997747)
                    ·
                      rfl

theorem cell23_3524040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_3524040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524040 prefixEnd_3524040 := by exact prefixLift 3524040
  have htrace : WordTrace (prefixWord ++ tailWord_3524040) baseStart_3524040 baseEnd_3524040 := by
    simpa [prefixWord, tailWord_3524040, baseEnd_3524040] using wordTrace_append hprefix tailTrace_3524040
  have hstable : (prefixWord ++ tailWord_3524040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524040).length < 2 ^ (prefixWord ++ tailWord_3524040).sum := by decide
  have hdescent : baseEnd_3524040 < baseStart_3524040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524053 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 8]
def baseStart_3524053 : Nat := 118140960795 + 3524053 * 2 ^ 59
def prefixEnd_3524053 : Nat := 4983230072969 + 3 ^ 40 * 3524053 * 2
def baseEnd_3524053 : Nat := 201059226768778428903409

theorem tailTrace_3524053 : CollatzResearch.WordTrace tailWord_3524053 prefixEnd_3524053 201059226768778428903409 := by
  unfold tailWord_3524053
  simp only [CollatzResearch.WordTrace]
  refine ⟨128532772301965316180960813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85688514867976877453973875 128532772301965316180960813)
  ·
    refine ⟨48199789613236993567860305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128532772301965316180960813 48199789613236993567860305)
    ·
      refine ⟨36149842209927745175895229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48199789613236993567860305 36149842209927745175895229)
      ·
        refine ⟨13556190828722904440960711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36149842209927745175895229 13556190828722904440960711)
        ·
          refine ⟨20334286243084356661441067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13556190828722904440960711 20334286243084356661441067)
          ·
            refine ⟨30501429364626534992161601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20334286243084356661441067 30501429364626534992161601)
            ·
              refine ⟨22876072023469901244121201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30501429364626534992161601 22876072023469901244121201)
              ·
                refine ⟨17157054017602425933090901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22876072023469901244121201 17157054017602425933090901)
                ·
                  refine ⟨201059226768778428903409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17157054017602425933090901 201059226768778428903409)
                  ·
                    rfl

theorem cell23_3524053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 8].length) (baseStart_3524053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524053 prefixEnd_3524053 := by exact prefixLift 3524053
  have htrace : WordTrace (prefixWord ++ tailWord_3524053) baseStart_3524053 baseEnd_3524053 := by
    simpa [prefixWord, tailWord_3524053, baseEnd_3524053] using wordTrace_append hprefix tailTrace_3524053
  have hstable : (prefixWord ++ tailWord_3524053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524053).length < 2 ^ (prefixWord ++ tailWord_3524053).sum := by decide
  have hdescent : baseEnd_3524053 < baseStart_3524053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524057 : List Nat := [1, 2, 1, 2, 4, 2, 1, 5, 1, 4]
def baseStart_3524057 : Nat := 118140960795 + 3524057 * 2 ^ 59
def prefixEnd_3524057 : Nat := 4983230072969 + 3 ^ 40 * 3524057 * 2
def baseEnd_3524057 : Nat := 603178364947207948160221

theorem tailTrace_3524057 : CollatzResearch.WordTrace tailWord_3524057 prefixEnd_3524057 603178364947207948160221 := by
  unfold tailWord_3524057
  simp only [CollatzResearch.WordTrace]
  refine ⟨128532918193950824864106425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85688612129300549909404283 128532918193950824864106425)
  ·
    refine ⟨96399688645463118648079819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128532918193950824864106425 96399688645463118648079819)
    ·
      refine ⟨144599532968194677972119729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96399688645463118648079819 144599532968194677972119729)
      ·
        refine ⟨108449649726146008479089797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144599532968194677972119729 108449649726146008479089797)
        ·
          refine ⟨20334309323652376589829337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108449649726146008479089797 20334309323652376589829337)
          ·
            refine ⟨15250731992739282442372003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20334309323652376589829337 15250731992739282442372003)
            ·
              refine ⟨22876097989108923663558005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15250731992739282442372003 22876097989108923663558005)
              ·
                refine ⟨2144634186478961593458563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22876097989108923663558005 2144634186478961593458563)
                ·
                  refine ⟨3216951279718442390187845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2144634186478961593458563 3216951279718442390187845)
                  ·
                    refine ⟨603178364947207948160221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3216951279718442390187845 603178364947207948160221)
                    ·
                      rfl

theorem cell23_3524057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 1, 4].length) (baseStart_3524057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524057 prefixEnd_3524057 := by exact prefixLift 3524057
  have htrace : WordTrace (prefixWord ++ tailWord_3524057) baseStart_3524057 baseEnd_3524057 := by
    simpa [prefixWord, tailWord_3524057, baseEnd_3524057] using wordTrace_append hprefix tailTrace_3524057
  have hstable : (prefixWord ++ tailWord_3524057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524057).length < 2 ^ (prefixWord ++ tailWord_3524057).sum := by decide
  have hdescent : baseEnd_3524057 < baseStart_3524057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524083 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 3, 5]
def baseStart_3524083 : Nat := 118140960795 + 3524083 * 2 ^ 59
def prefixEnd_3524083 : Nat := 4983230072969 + 3 ^ 40 * 3524083 * 2
def baseEnd_3524083 : Nat := 603182815112880247585181

theorem tailTrace_3524083 : CollatzResearch.WordTrace tailWord_3524083 prefixEnd_3524083 603182815112880247585181 := by
  unfold tailWord_3524083
  simp only [CollatzResearch.WordTrace]
  refine ⟨128533866491856631304552903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85689244327904420869701935 128533866491856631304552903)
  ·
    refine ⟨192800799737784946956829355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128533866491856631304552903 192800799737784946956829355)
    ·
      refine ⟨289201199606677420435244033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192800799737784946956829355 289201199606677420435244033)
      ·
        refine ⟨216900899705008065326433025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289201199606677420435244033 216900899705008065326433025)
        ·
          refine ⟨162675674778756048994824769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216900899705008065326433025 162675674778756048994824769)
          ·
            refine ⟨122006756084067036746118577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162675674778756048994824769 122006756084067036746118577)
            ·
              refine ⟨91505067063050277559588933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122006756084067036746118577 91505067063050277559588933)
              ·
                refine ⟨17157200074321927042422925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91505067063050277559588933 17157200074321927042422925)
                ·
                  refine ⟨6433950027870722640908597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17157200074321927042422925 6433950027870722640908597)
                  ·
                    refine ⟨603182815112880247585181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6433950027870722640908597 603182815112880247585181)
                    ·
                      rfl

theorem cell23_3524083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 5].length) (baseStart_3524083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524083 prefixEnd_3524083 := by exact prefixLift 3524083
  have htrace : WordTrace (prefixWord ++ tailWord_3524083) baseStart_3524083 baseEnd_3524083 := by
    simpa [prefixWord, tailWord_3524083, baseEnd_3524083] using wordTrace_append hprefix tailTrace_3524083
  have hstable : (prefixWord ++ tailWord_3524083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524083).length < 2 ^ (prefixWord ++ tailWord_3524083).sum := by decide
  have hdescent : baseEnd_3524083 < baseStart_3524083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3524090 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2]
def baseStart_3524090 : Nat := 118140960795 + 3524090 * 2 ^ 59
def prefixEnd_3524090 : Nat := 4983230072969 + 3 ^ 40 * 3524090 * 2
def baseEnd_3524090 : Nat := 1809552039703222215368011

theorem tailTrace_3524090 : CollatzResearch.WordTrace tailWord_3524090 prefixEnd_3524090 1809552039703222215368011 := by
  unfold tailWord_3524090
  simp only [CollatzResearch.WordTrace]
  refine ⟨32133530450707817875014431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85689414535220847666705149 32133530450707817875014431)
  ·
    refine ⟨48200295676061726812521647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32133530450707817875014431 48200295676061726812521647)
    ·
      refine ⟨72300443514092590218782471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48200295676061726812521647 72300443514092590218782471)
      ·
        refine ⟨108450665271138885328173707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72300443514092590218782471 108450665271138885328173707)
        ·
          refine ⟨162675997906708327992260561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108450665271138885328173707 162675997906708327992260561)
          ·
            refine ⟨122006998430031245994195421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162675997906708327992260561 122006998430031245994195421)
            ·
              refine ⟨45752624411261717247823283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122006998430031245994195421 45752624411261717247823283)
              ·
                refine ⟨68628936616892575871734925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45752624411261717247823283 68628936616892575871734925)
                ·
                  refine ⟨25735851231334715951900597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68628936616892575871734925 25735851231334715951900597)
                  ·
                    refine ⟨2412736052937629620490681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25735851231334715951900597 2412736052937629620490681)
                    ·
                      refine ⟨1809552039703222215368011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2412736052937629620490681 1809552039703222215368011)
                      ·
                        rfl

theorem cell23_3524090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2].length) (baseStart_3524090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3524090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3524090 prefixEnd_3524090 := by exact prefixLift 3524090
  have htrace : WordTrace (prefixWord ++ tailWord_3524090) baseStart_3524090 baseEnd_3524090 := by
    simpa [prefixWord, tailWord_3524090, baseEnd_3524090] using wordTrace_append hprefix tailTrace_3524090
  have hstable : (prefixWord ++ tailWord_3524090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3524090).length < 2 ^ (prefixWord ++ tailWord_3524090).sum := by decide
  have hdescent : baseEnd_3524090 < baseStart_3524090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3524090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
