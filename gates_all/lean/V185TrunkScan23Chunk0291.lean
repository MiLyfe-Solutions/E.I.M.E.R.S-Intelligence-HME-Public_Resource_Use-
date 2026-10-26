import V185TrunkScan23Chunk0290

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1720743 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 1, 6]
def baseStart_1720743 : Nat := 118140960795 + 1720743 * 2 ^ 59
def prefixEnd_1720743 : Nat := 4983230072969 + 3 ^ 40 * 1720743 * 2
def baseEnd_1720743 : Nat := 294522747286555439599651

theorem tailTrace_1720743 : CollatzResearch.WordTrace tailWord_1720743 prefixEnd_1720743 294522747286555439599651 := by
  unfold tailWord_1720743
  simp only [CollatzResearch.WordTrace]
  refine ⟨62760653205049465352566883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41840435470032976901711255 62760653205049465352566883)
  ·
    refine ⟨94140979807574198028850325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62760653205049465352566883 94140979807574198028850325)
    ·
      refine ⟨4412858428480040532602359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94140979807574198028850325 4412858428480040532602359)
      ·
        refine ⟨6619287642720060798903539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4412858428480040532602359 6619287642720060798903539)
        ·
          refine ⟨9928931464080091198355309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6619287642720060798903539 9928931464080091198355309)
          ·
            refine ⟨3723349299030034199383241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9928931464080091198355309 3723349299030034199383241)
            ·
              refine ⟨2792511974272525649537431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3723349299030034199383241 2792511974272525649537431)
              ·
                refine ⟨4188767961408788474306147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2792511974272525649537431 4188767961408788474306147)
                ·
                  refine ⟨6283151942113182711459221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4188767961408788474306147 6283151942113182711459221)
                  ·
                    refine ⟨294522747286555439599651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6283151942113182711459221 294522747286555439599651)
                    ·
                      rfl

theorem cell23_1720743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_1720743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720743 prefixEnd_1720743 := by exact prefixLift 1720743
  have htrace : WordTrace (prefixWord ++ tailWord_1720743) baseStart_1720743 baseEnd_1720743 := by
    simpa [prefixWord, tailWord_1720743, baseEnd_1720743] using wordTrace_append hprefix tailTrace_1720743
  have hstable : (prefixWord ++ tailWord_1720743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720743).length < 2 ^ (prefixWord ++ tailWord_1720743).sum := by decide
  have hdescent : baseEnd_1720743 < baseStart_1720743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720753 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 3, 2, 3]
def baseStart_1720753 : Nat := 118140960795 + 1720753 * 2 ^ 59
def prefixEnd_1720753 : Nat := 4983230072969 + 3 ^ 40 * 1720753 * 2
def baseEnd_1720753 : Nat := 883573376666211279673907

theorem tailTrace_1720753 : CollatzResearch.WordTrace tailWord_1720753 prefixEnd_1720753 883573376666211279673907 := by
  unfold tailWord_1720753
  simp only [CollatzResearch.WordTrace]
  refine ⟨62761017935013237060430913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41840678623342158040287275 62761017935013237060430913)
  ·
    refine ⟨47070763451259927795323185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62761017935013237060430913 47070763451259927795323185)
    ·
      refine ⟨35303072588444945846492389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47070763451259927795323185 35303072588444945846492389)
      ·
        refine ⟨6619326110333427346217323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35303072588444945846492389 6619326110333427346217323)
        ·
          refine ⟨9928989165500141019325985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6619326110333427346217323 9928989165500141019325985)
          ·
            refine ⟨7446741874125105764494489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9928989165500141019325985 7446741874125105764494489)
            ·
              refine ⟨5585056405593829323370867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7446741874125105764494489 5585056405593829323370867)
              ·
                refine ⟨8377584608390743985056301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5585056405593829323370867 8377584608390743985056301)
                ·
                  refine ⟨3141594228146528994396113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8377584608390743985056301 3141594228146528994396113)
                  ·
                    refine ⟨2356195671109896745797085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3141594228146528994396113 2356195671109896745797085)
                    ·
                      refine ⟨883573376666211279673907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2356195671109896745797085 883573376666211279673907)
                      ·
                        rfl

theorem cell23_1720753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_1720753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720753 prefixEnd_1720753 := by exact prefixLift 1720753
  have htrace : WordTrace (prefixWord ++ tailWord_1720753) baseStart_1720753 baseEnd_1720753 := by
    simpa [prefixWord, tailWord_1720753, baseEnd_1720753] using wordTrace_append hprefix tailTrace_1720753
  have hstable : (prefixWord ++ tailWord_1720753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720753).length < 2 ^ (prefixWord ++ tailWord_1720753).sum := by decide
  have hdescent : baseEnd_1720753 < baseStart_1720753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720813 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1720813 : Nat := 118140960795 + 1720813 * 2 ^ 59
def prefixEnd_1720813 : Nat := 4983230072969 + 3 ^ 40 * 1720813 * 2
def baseEnd_1720813 : Nat := 883604185505481044923631

theorem tailTrace_1720813 : CollatzResearch.WordTrace tailWord_1720813 prefixEnd_1720813 883604185505481044923631 := by
  unfold tailWord_1720813
  simp only [CollatzResearch.WordTrace]
  refine ⟨62763206314795867307615093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41842137543197244871743395 62763206314795867307615093)
  ·
    refine ⟨5884050592012112560088915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62763206314795867307615093 5884050592012112560088915)
    ·
      refine ⟨8826075888018168840133373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5884050592012112560088915 8826075888018168840133373)
      ·
        refine ⟨3309778458006813315050015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8826075888018168840133373 3309778458006813315050015)
        ·
          refine ⟨4964667687010219972575023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3309778458006813315050015 4964667687010219972575023)
          ·
            refine ⟨7447001530515329958862535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4964667687010219972575023 7447001530515329958862535)
            ·
              refine ⟨11170502295772994938293803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7447001530515329958862535 11170502295772994938293803)
              ·
                refine ⟨16755753443659492407440705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11170502295772994938293803 16755753443659492407440705)
                ·
                  refine ⟨12566815082744619305580529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16755753443659492407440705 12566815082744619305580529)
                  ·
                    refine ⟨9425111312058464479185397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12566815082744619305580529 9425111312058464479185397)
                    ·
                      refine ⟨883604185505481044923631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9425111312058464479185397 883604185505481044923631)
                      ·
                        rfl

theorem cell23_1720813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1720813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720813 prefixEnd_1720813 := by exact prefixLift 1720813
  have htrace : WordTrace (prefixWord ++ tailWord_1720813) baseStart_1720813 baseEnd_1720813 := by
    simpa [prefixWord, tailWord_1720813, baseEnd_1720813] using wordTrace_append hprefix tailTrace_1720813
  have hstable : (prefixWord ++ tailWord_1720813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720813).length < 2 ^ (prefixWord ++ tailWord_1720813).sum := by decide
  have hdescent : baseEnd_1720813 < baseStart_1720813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720818 : List Nat := [3, 2, 1, 4, 3, 1, 1, 3, 1, 2, 2]
def baseStart_1720818 : Nat := 118140960795 + 1720818 * 2 ^ 59
def prefixEnd_1720818 : Nat := 4983230072969 + 3 ^ 40 * 1720818 * 2
def baseEnd_1720818 : Nat := 883606752908753525361109

theorem tailTrace_1720818 : CollatzResearch.WordTrace tailWord_1720818 prefixEnd_1720818 883606752908753525361109 := by
  unfold tailWord_1720818
  simp only [CollatzResearch.WordTrace]
  refine ⟨15690847169944438290386777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41842259119851835441031405 15690847169944438290386777)
  ·
    refine ⟨11768135377458328717790083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15690847169944438290386777 11768135377458328717790083)
    ·
      refine ⟨17652203066187493076685125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11768135377458328717790083 17652203066187493076685125)
      ·
        refine ⟨3309788074910154951878461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17652203066187493076685125 3309788074910154951878461)
        ·
          refine ⟨1241170528091308106954423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3309788074910154951878461 1241170528091308106954423)
          ·
            refine ⟨1861755792136962160431635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241170528091308106954423 1861755792136962160431635)
            ·
              refine ⟨2792633688205443240647453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1861755792136962160431635 2792633688205443240647453)
              ·
                refine ⟨1047237633077041215242795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2792633688205443240647453 1047237633077041215242795)
                ·
                  refine ⟨1570856449615561822864193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047237633077041215242795 1570856449615561822864193)
                  ·
                    refine ⟨1178142337211671367148145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1570856449615561822864193 1178142337211671367148145)
                    ·
                      refine ⟨883606752908753525361109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1178142337211671367148145 883606752908753525361109)
                      ·
                        rfl

theorem cell23_1720818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_1720818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720818 prefixEnd_1720818 := by exact prefixLift 1720818
  have htrace : WordTrace (prefixWord ++ tailWord_1720818) baseStart_1720818 baseEnd_1720818 := by
    simpa [prefixWord, tailWord_1720818, baseEnd_1720818] using wordTrace_append hprefix tailTrace_1720818
  have hstable : (prefixWord ++ tailWord_1720818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720818).length < 2 ^ (prefixWord ++ tailWord_1720818).sum := by decide
  have hdescent : baseEnd_1720818 < baseStart_1720818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720876 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 1, 7]
def baseStart_1720876 : Nat := 118140960795 + 1720876 * 2 ^ 59
def prefixEnd_1720876 : Nat := 4983230072969 + 3 ^ 40 * 1720876 * 2
def baseEnd_1720876 : Nat := 294545511595571432811947

theorem tailTrace_1720876 : CollatzResearch.WordTrace tailWord_1720876 prefixEnd_1720876 294545511595571432811947 := by
  unfold tailWord_1720876
  simp only [CollatzResearch.WordTrace]
  refine ⟨31382752056783814533579241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41843669409045086044772321 31382752056783814533579241)
  ·
    refine ⟨23537064042587860900184431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31382752056783814533579241 23537064042587860900184431)
    ·
      refine ⟨35305596063881791350276647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23537064042587860900184431 35305596063881791350276647)
      ·
        refine ⟨52958394095822687025414971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35305596063881791350276647 52958394095822687025414971)
        ·
          refine ⟨79437591143734030538122457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52958394095822687025414971 79437591143734030538122457)
          ·
            refine ⟨59578193357800522903591843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79437591143734030538122457 59578193357800522903591843)
            ·
              refine ⟨89367290036700784355387765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59578193357800522903591843 89367290036700784355387765)
              ·
                refine ⟨8378183440940698533317603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89367290036700784355387765 8378183440940698533317603)
                ·
                  refine ⟨12567275161411047799976405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8378183440940698533317603 12567275161411047799976405)
                  ·
                    refine ⟨294545511595571432811947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12567275161411047799976405 294545511595571432811947)
                    ·
                      rfl

theorem cell23_1720876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_1720876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720876 prefixEnd_1720876 := by exact prefixLift 1720876
  have htrace : WordTrace (prefixWord ++ tailWord_1720876) baseStart_1720876 baseEnd_1720876 := by
    simpa [prefixWord, tailWord_1720876, baseEnd_1720876] using wordTrace_append hprefix tailTrace_1720876
  have hstable : (prefixWord ++ tailWord_1720876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720876).length < 2 ^ (prefixWord ++ tailWord_1720876).sum := by decide
  have hdescent : baseEnd_1720876 < baseStart_1720876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720897 : List Nat := [1, 2, 5, 1, 1, 2, 4, 2, 5]
def baseStart_1720897 : Nat := 118140960795 + 1720897 * 2 ^ 59
def prefixEnd_1720897 : Nat := 4983230072969 + 3 ^ 40 * 1720897 * 2
def baseEnd_1720897 : Nat := 98183035320050968474805

theorem tailTrace_1720897 : CollatzResearch.WordTrace tailWord_1720897 prefixEnd_1720897 98183035320050968474805 := by
  unfold tailWord_1720897
  simp only [CollatzResearch.WordTrace]
  refine ⟨62766270046491549653672945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41844180030994366435781963 62766270046491549653672945)
  ·
    refine ⟨47074702534868662240254709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62766270046491549653672945 47074702534868662240254709)
    ·
      refine ⟨4413253362643937085023879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47074702534868662240254709 4413253362643937085023879)
      ·
        refine ⟨6619880043965905627535819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4413253362643937085023879 6619880043965905627535819)
        ·
          refine ⟨9929820065948858441303729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6619880043965905627535819 9929820065948858441303729)
          ·
            refine ⟨7447365049461643830977797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9929820065948858441303729 7447365049461643830977797)
            ·
              refine ⟨1396380946774058218308337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7447365049461643830977797 1396380946774058218308337)
              ·
                refine ⟨1047285710080543663731253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1396380946774058218308337 1047285710080543663731253)
                ·
                  refine ⟨98183035320050968474805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1047285710080543663731253 98183035320050968474805)
                  ·
                    rfl

theorem cell23_1720897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 5].length) (baseStart_1720897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720897 prefixEnd_1720897 := by exact prefixLift 1720897
  have htrace : WordTrace (prefixWord ++ tailWord_1720897) baseStart_1720897 baseEnd_1720897 := by
    simpa [prefixWord, tailWord_1720897, baseEnd_1720897] using wordTrace_append hprefix tailTrace_1720897
  have hstable : (prefixWord ++ tailWord_1720897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720897).length < 2 ^ (prefixWord ++ tailWord_1720897).sum := by decide
  have hdescent : baseEnd_1720897 < baseStart_1720897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720903 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_1720903 : Nat := 118140960795 + 1720903 * 2 ^ 59
def prefixEnd_1720903 : Nat := 4983230072969 + 3 ^ 40 * 1720903 * 2
def baseEnd_1720903 : Nat := 883650398764385692798217

theorem tailTrace_1720903 : CollatzResearch.WordTrace tailWord_1720903 prefixEnd_1720903 883650398764385692798217 := by
  unfold tailWord_1720903
  simp only [CollatzResearch.WordTrace]
  refine ⟨62766488884469812678391363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41844325922979875118927575 62766488884469812678391363)
  ·
    refine ⟨94149733326704719017587045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62766488884469812678391363 94149733326704719017587045)
    ·
      refine ⟨17653074998757134815797571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94149733326704719017587045 17653074998757134815797571)
      ·
        refine ⟨26479612498135702223696357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17653074998757134815797571 26479612498135702223696357)
        ·
          refine ⟨4964927343400444166943067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26479612498135702223696357 4964927343400444166943067)
          ·
            refine ⟨7447391015100666250414601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4964927343400444166943067 7447391015100666250414601)
            ·
              refine ⟨5585543261325499687810951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7447391015100666250414601 5585543261325499687810951)
              ·
                refine ⟨8378314891988249531716427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5585543261325499687810951 8378314891988249531716427)
                ·
                  refine ⟨12567472337982374297574641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8378314891988249531716427 12567472337982374297574641)
                  ·
                    refine ⟨9425604253486780723180981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12567472337982374297574641 9425604253486780723180981)
                    ·
                      refine ⟨883650398764385692798217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9425604253486780723180981 883650398764385692798217)
                      ·
                        rfl

theorem cell23_1720903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_1720903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720903 prefixEnd_1720903 := by exact prefixLift 1720903
  have htrace : WordTrace (prefixWord ++ tailWord_1720903) baseStart_1720903 baseEnd_1720903 := by
    simpa [prefixWord, tailWord_1720903, baseEnd_1720903] using wordTrace_append hprefix tailTrace_1720903
  have hstable : (prefixWord ++ tailWord_1720903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720903).length < 2 ^ (prefixWord ++ tailWord_1720903).sum := by decide
  have hdescent : baseEnd_1720903 < baseStart_1720903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720953 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 8]
def baseStart_1720953 : Nat := 118140960795 + 1720953 * 2 ^ 59
def prefixEnd_1720953 : Nat := 4983230072969 + 3 ^ 40 * 1720953 * 2
def baseEnd_1720953 : Nat := 98186230310790055241443

theorem tailTrace_1720953 : CollatzResearch.WordTrace tailWord_1720953 prefixEnd_1720953 98186230310790055241443 := by
  unfold tailWord_1720953
  simp only [CollatzResearch.WordTrace]
  refine ⟨62768312534288671217711513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41845541689525780811807675 62768312534288671217711513)
  ·
    refine ⟨47076234400716503413283635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62768312534288671217711513 47076234400716503413283635)
    ·
      refine ⟨70614351601074755119925453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47076234400716503413283635 70614351601074755119925453)
      ·
        refine ⟨26480381850403033169972045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70614351601074755119925453 26480381850403033169972045)
        ·
          refine ⟨9930143193901137438739517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26480381850403033169972045 9930143193901137438739517)
          ·
            refine ⟨3723803697712926539527319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9930143193901137438739517 3723803697712926539527319)
            ·
              refine ⟨5585705546569389809290979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3723803697712926539527319 5585705546569389809290979)
              ·
                refine ⟨8378558319854084713936469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5585705546569389809290979 8378558319854084713936469)
                ·
                  refine ⟨98186230310790055241443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8378558319854084713936469 98186230310790055241443)
                  ·
                    rfl

theorem cell23_1720953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 8].length) (baseStart_1720953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720953 prefixEnd_1720953 := by exact prefixLift 1720953
  have htrace : WordTrace (prefixWord ++ tailWord_1720953) baseStart_1720953 baseEnd_1720953 := by
    simpa [prefixWord, tailWord_1720953, baseEnd_1720953] using wordTrace_append hprefix tailTrace_1720953
  have hstable : (prefixWord ++ tailWord_1720953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720953).length < 2 ^ (prefixWord ++ tailWord_1720953).sum := by decide
  have hdescent : baseEnd_1720953 < baseStart_1720953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1720957 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 3, 4]
def baseStart_1720957 : Nat := 118140960795 + 1720957 * 2 ^ 59
def prefixEnd_1720957 : Nat := 4983230072969 + 3 ^ 40 * 1720957 * 2
def baseEnd_1720957 : Nat := 294559375573242827174323

theorem tailTrace_1720957 : CollatzResearch.WordTrace tailWord_1720957 prefixEnd_1720957 294559375573242827174323 := by
  unfold tailWord_1720957
  simp only [CollatzResearch.WordTrace]
  refine ⟨62768458426274179900857125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41845638950849453267238083 62768458426274179900857125)
  ·
    refine ⟨11769085954926408731410711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62768458426274179900857125 11769085954926408731410711)
    ·
      refine ⟨17653628932389613097116067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11769085954926408731410711 17653628932389613097116067)
      ·
        refine ⟨26480443398584419645674101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17653628932389613097116067 26480443398584419645674101)
        ·
          refine ⟨2482541568617289341781947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26480443398584419645674101 2482541568617289341781947)
          ·
            refine ⟨3723812352925934012672921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2482541568617289341781947 3723812352925934012672921)
            ·
              refine ⟨2792859264694450509504691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3723812352925934012672921 2792859264694450509504691)
              ·
                refine ⟨4189288897041675764257037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2792859264694450509504691 4189288897041675764257037)
                ·
                  refine ⟨1570983336390628411596389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4189288897041675764257037 1570983336390628411596389)
                  ·
                    refine ⟨294559375573242827174323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1570983336390628411596389 294559375573242827174323)
                    ·
                      rfl

theorem cell23_1720957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_1720957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1720957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1720957 prefixEnd_1720957 := by exact prefixLift 1720957
  have htrace : WordTrace (prefixWord ++ tailWord_1720957) baseStart_1720957 baseEnd_1720957 := by
    simpa [prefixWord, tailWord_1720957, baseEnd_1720957] using wordTrace_append hprefix tailTrace_1720957
  have hstable : (prefixWord ++ tailWord_1720957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1720957).length < 2 ^ (prefixWord ++ tailWord_1720957).sum := by decide
  have hdescent : baseEnd_1720957 < baseStart_1720957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1720957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721007 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 2, 3, 2]
def baseStart_1721007 : Nat := 118140960795 + 1721007 * 2 ^ 59
def prefixEnd_1721007 : Nat := 4983230072969 + 3 ^ 40 * 1721007 * 2
def baseEnd_1721007 : Nat := 883703800752453285897739

theorem tailTrace_1721007 : CollatzResearch.WordTrace tailWord_1721007 prefixEnd_1721007 883703800752453285897739 := by
  unfold tailWord_1721007
  simp only [CollatzResearch.WordTrace]
  refine ⟨62770282076093038440177275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41846854717395358960118183 62770282076093038440177275)
  ·
    refine ⟨94155423114139557660265913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62770282076093038440177275 94155423114139557660265913)
    ·
      refine ⟨70616567335604668245199435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94155423114139557660265913 70616567335604668245199435)
      ·
        refine ⟨105924851003407002367799153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70616567335604668245199435 105924851003407002367799153)
        ·
          refine ⟨79443638252555251775849365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105924851003407002367799153 79443638252555251775849365)
          ·
            refine ⟨3723920543088527426992939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79443638252555251775849365 3723920543088527426992939)
            ·
              refine ⟨5585880814632791140489409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3723920543088527426992939 5585880814632791140489409)
              ·
                refine ⟨4189410610974593355367057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5585880814632791140489409 4189410610974593355367057)
                ·
                  refine ⟨3142057958230945016525293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4189410610974593355367057 3142057958230945016525293)
                  ·
                    refine ⟨1178271734336604381196985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3142057958230945016525293 1178271734336604381196985)
                    ·
                      refine ⟨883703800752453285897739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1178271734336604381196985 883703800752453285897739)
                      ·
                        rfl

theorem cell23_1721007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 3, 2].length) (baseStart_1721007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721007 prefixEnd_1721007 := by exact prefixLift 1721007
  have htrace : WordTrace (prefixWord ++ tailWord_1721007) baseStart_1721007 baseEnd_1721007 := by
    simpa [prefixWord, tailWord_1721007, baseEnd_1721007] using wordTrace_append hprefix tailTrace_1721007
  have hstable : (prefixWord ++ tailWord_1721007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721007).length < 2 ^ (prefixWord ++ tailWord_1721007).sum := by decide
  have hdescent : baseEnd_1721007 < baseStart_1721007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721020 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_1721020 : Nat := 118140960795 + 1721020 * 2 ^ 59
def prefixEnd_1721020 : Nat := 4983230072969 + 3 ^ 40 * 1721020 * 2
def baseEnd_1721020 : Nat := 883710476000961735035179

theorem tailTrace_1721020 : CollatzResearch.WordTrace tailWord_1721020 prefixEnd_1721020 883710476000961735035179 := by
  unfold tailWord_1721020
  simp only [CollatzResearch.WordTrace]
  refine ⟨31385378112522970830200257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41847170816697294440267009 31385378112522970830200257)
  ·
    refine ⟨23539033584392228122650193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31385378112522970830200257 23539033584392228122650193)
    ·
      refine ⟨17654275188294171091987645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23539033584392228122650193 17654275188294171091987645)
      ·
        refine ⟨6620353195610314159495367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17654275188294171091987645 6620353195610314159495367)
        ·
          refine ⟨9930529793415471239243051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6620353195610314159495367 9930529793415471239243051)
          ·
            refine ⟨14895794690123206858864577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9930529793415471239243051 14895794690123206858864577)
            ·
              refine ⟨11171846017592405144148433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14895794690123206858864577 11171846017592405144148433)
              ·
                refine ⟨8378884513194303858111325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11171846017592405144148433 8378884513194303858111325)
                ·
                  refine ⟨3142081692447863946791747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8378884513194303858111325 3142081692447863946791747)
                  ·
                    refine ⟨4713122538671795920187621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3142081692447863946791747 4713122538671795920187621)
                    ·
                      refine ⟨883710476000961735035179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4713122538671795920187621 883710476000961735035179)
                      ·
                        rfl

theorem cell23_1721020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_1721020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721020 prefixEnd_1721020 := by exact prefixLift 1721020
  have htrace : WordTrace (prefixWord ++ tailWord_1721020) baseStart_1721020 baseEnd_1721020 := by
    simpa [prefixWord, tailWord_1721020, baseEnd_1721020] using wordTrace_append hprefix tailTrace_1721020
  have hstable : (prefixWord ++ tailWord_1721020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721020).length < 2 ^ (prefixWord ++ tailWord_1721020).sum := by decide
  have hdescent : baseEnd_1721020 < baseStart_1721020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721033 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 7, 2, 4]
def baseStart_1721033 : Nat := 118140960795 + 1721033 * 2 ^ 59
def prefixEnd_1721033 : Nat := 4983230072969 + 3 ^ 40 * 1721033 * 2
def baseEnd_1721033 : Nat := 883717151249470184172619

theorem tailTrace_1721033 : CollatzResearch.WordTrace tailWord_1721033 prefixEnd_1721033 883717151249470184172619 := by
  unfold tailWord_1721033
  simp only [CollatzResearch.WordTrace]
  refine ⟨62771230373998844880623753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41847486915999229920415835 62771230373998844880623753)
  ·
    refine ⟨47078422780499133660467815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62771230373998844880623753 47078422780499133660467815)
    ·
      refine ⟨70617634170748700490701723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47078422780499133660467815 70617634170748700490701723)
      ·
        refine ⟨105926451256123050736052585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70617634170748700490701723 105926451256123050736052585)
        ·
          refine ⟨79444838442092288052039439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105926451256123050736052585 79444838442092288052039439)
          ·
            refine ⟨119167257663138432078059159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79444838442092288052039439 119167257663138432078059159)
            ·
              refine ⟨178750886494707648117088739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119167257663138432078059159 178750886494707648117088739)
              ·
                refine ⟨268126329742061472175633109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178750886494707648117088739 268126329742061472175633109)
                ·
                  refine ⟨6284210853329565754116401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 268126329742061472175633109 6284210853329565754116401)
                  ·
                    refine ⟨4713158139997174315587301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6284210853329565754116401 4713158139997174315587301)
                    ·
                      refine ⟨883717151249470184172619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4713158139997174315587301 883717151249470184172619)
                      ·
                        rfl

theorem cell23_1721033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_1721033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721033 prefixEnd_1721033 := by exact prefixLift 1721033
  have htrace : WordTrace (prefixWord ++ tailWord_1721033) baseStart_1721033 baseEnd_1721033 := by
    simpa [prefixWord, tailWord_1721033, baseEnd_1721033] using wordTrace_append hprefix tailTrace_1721033
  have hstable : (prefixWord ++ tailWord_1721033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721033).length < 2 ^ (prefixWord ++ tailWord_1721033).sum := by decide
  have hdescent : baseEnd_1721033 < baseStart_1721033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721050 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4]
def baseStart_1721050 : Nat := 118140960795 + 1721050 * 2 ^ 59
def prefixEnd_1721050 : Nat := 4983230072969 + 3 ^ 40 * 1721050 * 2
def baseEnd_1721050 : Nat := 883725880420596617660041

theorem tailTrace_1721050 : CollatzResearch.WordTrace tailWord_1721050 prefixEnd_1721050 883725880420596617660041 := by
  unfold tailWord_1721050
  simp only [CollatzResearch.WordTrace]
  refine ⟨15692962603734314195998151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41847900276624837855995069 15692962603734314195998151)
  ·
    refine ⟨23539443905601471293997227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15692962603734314195998151 23539443905601471293997227)
    ·
      refine ⟨35309165858402206940995841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23539443905601471293997227 35309165858402206940995841)
      ·
        refine ⟨26481874393801655205746881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35309165858402206940995841 26481874393801655205746881)
        ·
          refine ⟨19861405795351241404310161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26481874393801655205746881 19861405795351241404310161)
          ·
            refine ⟨14896054346513431053232621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19861405795351241404310161 14896054346513431053232621)
            ·
              refine ⟨5586020379942536644962233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14896054346513431053232621 5586020379942536644962233)
              ·
                refine ⟨4189515284956902483721675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5586020379942536644962233 4189515284956902483721675)
                ·
                  refine ⟨6284272927435353725582513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4189515284956902483721675 6284272927435353725582513)
                  ·
                    refine ⟨4713204695576515294186885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6284272927435353725582513 4713204695576515294186885)
                    ·
                      refine ⟨883725880420596617660041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4713204695576515294186885 883725880420596617660041)
                      ·
                        rfl

theorem cell23_1721050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_1721050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721050 prefixEnd_1721050 := by exact prefixLift 1721050
  have htrace : WordTrace (prefixWord ++ tailWord_1721050) baseStart_1721050 baseEnd_1721050 := by
    simpa [prefixWord, tailWord_1721050, baseEnd_1721050] using wordTrace_append hprefix tailTrace_1721050
  have hstable : (prefixWord ++ tailWord_1721050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721050).length < 2 ^ (prefixWord ++ tailWord_1721050).sum := by decide
  have hdescent : baseEnd_1721050 < baseStart_1721050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721057 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 1, 1, 5]
def baseStart_1721057 : Nat := 118140960795 + 1721057 * 2 ^ 59
def prefixEnd_1721057 : Nat := 4983230072969 + 3 ^ 40 * 1721057 * 2
def baseEnd_1721057 : Nat := 883729474785178090272509

theorem tailTrace_1721057 : CollatzResearch.WordTrace tailWord_1721057 prefixEnd_1721057 883729474785178090272509 := by
  unfold tailWord_1721057
  simp only [CollatzResearch.WordTrace]
  refine ⟨62772105725911896979497425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41848070483941264652998283 62772105725911896979497425)
  ·
    refine ⟨47079079294433922734623069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62772105725911896979497425 47079079294433922734623069)
    ·
      refine ⟨17654654735412721025483651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47079079294433922734623069 17654654735412721025483651)
      ·
        refine ⟨26481982103119081538225477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17654654735412721025483651 26481982103119081538225477)
        ·
          refine ⟨4965371644334827788417277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26481982103119081538225477 4965371644334827788417277)
          ·
            refine ⟨1862014366625560420656479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4965371644334827788417277 1862014366625560420656479)
            ·
              refine ⟨2793021549938340630984719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1862014366625560420656479 2793021549938340630984719)
              ·
                refine ⟨4189532324907510946477079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2793021549938340630984719 4189532324907510946477079)
                ·
                  refine ⟨6284298487361266419715619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4189532324907510946477079 6284298487361266419715619)
                  ·
                    refine ⟨9426447731041899629573429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6284298487361266419715619 9426447731041899629573429)
                    ·
                      refine ⟨883729474785178090272509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9426447731041899629573429 883729474785178090272509)
                      ·
                        rfl

theorem cell23_1721057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_1721057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721057 prefixEnd_1721057 := by exact prefixLift 1721057
  have htrace : WordTrace (prefixWord ++ tailWord_1721057) baseStart_1721057 baseEnd_1721057 := by
    simpa [prefixWord, tailWord_1721057, baseEnd_1721057] using wordTrace_append hprefix tailTrace_1721057
  have hstable : (prefixWord ++ tailWord_1721057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721057).length < 2 ^ (prefixWord ++ tailWord_1721057).sum := by decide
  have hdescent : baseEnd_1721057 < baseStart_1721057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721064 : List Nat := [2, 1, 4, 1, 4, 1, 2, 2, 2, 4]
def baseStart_1721064 : Nat := 118140960795 + 1721064 * 2 ^ 59
def prefixEnd_1721064 : Nat := 4983230072969 + 3 ^ 40 * 1721064 * 2
def baseEnd_1721064 : Nat := 294577689716586520961659

theorem tailTrace_1721064 : CollatzResearch.WordTrace tailWord_1721064 prefixEnd_1721064 294577689716586520961659 := by
  unfold tailWord_1721064
  simp only [CollatzResearch.WordTrace]
  refine ⟨31386180518443268587501123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41848240691257691450001497 31386180518443268587501123)
  ·
    refine ⟨47079270777664902881251685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31386180518443268587501123 47079270777664902881251685)
    ·
      refine ⟨8827363270812169290234691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47079270777664902881251685 8827363270812169290234691)
      ·
        refine ⟨13241044906218253935352037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8827363270812169290234691 13241044906218253935352037)
        ·
          refine ⟨2482695919915922612878507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13241044906218253935352037 2482695919915922612878507)
          ·
            refine ⟨3724043879873883919317761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2482695919915922612878507 3724043879873883919317761)
            ·
              refine ⟨2793032909905412939488321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3724043879873883919317761 2793032909905412939488321)
              ·
                refine ⟨2094774682429059704616241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2793032909905412939488321 2094774682429059704616241)
                ·
                  refine ⟨1571081011821794778462181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2094774682429059704616241 1571081011821794778462181)
                  ·
                    refine ⟨294577689716586520961659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1571081011821794778462181 294577689716586520961659)
                    ·
                      rfl

theorem cell23_1721064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_1721064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721064 prefixEnd_1721064 := by exact prefixLift 1721064
  have htrace : WordTrace (prefixWord ++ tailWord_1721064) baseStart_1721064 baseEnd_1721064 := by
    simpa [prefixWord, tailWord_1721064, baseEnd_1721064] using wordTrace_append hprefix tailTrace_1721064
  have hstable : (prefixWord ++ tailWord_1721064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721064).length < 2 ^ (prefixWord ++ tailWord_1721064).sum := by decide
  have hdescent : baseEnd_1721064 < baseStart_1721064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721071 : List Nat := [1, 1, 2, 1, 5, 3, 1, 4, 1, 2, 2]
def baseStart_1721071 : Nat := 118140960795 + 1721071 * 2 ^ 59
def prefixEnd_1721071 : Nat := 4983230072969 + 3 ^ 40 * 1721071 * 2
def baseEnd_1721071 : Nat := 883736663514341035497445

theorem tailTrace_1721071 : CollatzResearch.WordTrace tailWord_1721071 prefixEnd_1721071 883736663514341035497445 := by
  unfold tailWord_1721071
  simp only [CollatzResearch.WordTrace]
  refine ⟨62772616347861177370507067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41848410898574118247004711 62772616347861177370507067)
  ·
    refine ⟨94158924521791766055760601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62772616347861177370507067 94158924521791766055760601)
    ·
      refine ⟨70619193391343824541820451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94158924521791766055760601 70619193391343824541820451)
      ·
        refine ⟨105928790087015736812730677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70619193391343824541820451 105928790087015736812730677)
        ·
          refine ⟨9930824070657725326193501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105928790087015736812730677 9930824070657725326193501)
          ·
            refine ⟨3724059026496646997322563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9930824070657725326193501 3724059026496646997322563)
            ·
              refine ⟨5586088539744970495983845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3724059026496646997322563 5586088539744970495983845)
              ·
                refine ⟨1047391601202181967996971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5586088539744970495983845 1047391601202181967996971)
                ·
                  refine ⟨1571087401803272951995457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047391601202181967996971 1571087401803272951995457)
                  ·
                    refine ⟨1178315551352454713996593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1571087401803272951995457 1178315551352454713996593)
                    ·
                      refine ⟨883736663514341035497445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1178315551352454713996593 883736663514341035497445)
                      ·
                        rfl

theorem cell23_1721071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 1, 2, 2].length) (baseStart_1721071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721071 prefixEnd_1721071 := by exact prefixLift 1721071
  have htrace : WordTrace (prefixWord ++ tailWord_1721071) baseStart_1721071 baseEnd_1721071 := by
    simpa [prefixWord, tailWord_1721071, baseEnd_1721071] using wordTrace_append hprefix tailTrace_1721071
  have hstable : (prefixWord ++ tailWord_1721071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721071).length < 2 ^ (prefixWord ++ tailWord_1721071).sum := by decide
  have hdescent : baseEnd_1721071 < baseStart_1721071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721073 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 1, 9]
def baseStart_1721073 : Nat := 118140960795 + 1721073 * 2 ^ 59
def prefixEnd_1721073 : Nat := 4983230072969 + 3 ^ 40 * 1721073 * 2
def baseEnd_1721073 : Nat := 294579230158550009224145

theorem tailTrace_1721073 : CollatzResearch.WordTrace tailWord_1721073 prefixEnd_1721073 294579230158550009224145 := by
  unfold tailWord_1721073
  simp only [CollatzResearch.WordTrace]
  refine ⟨62772689293853931712079873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41848459529235954474719915 62772689293853931712079873)
  ·
    refine ⟨47079516970390448784059905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62772689293853931712079873 47079516970390448784059905)
    ·
      refine ⟨35309637727792836588044929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47079516970390448784059905 35309637727792836588044929)
      ·
        refine ⟨26482228295844627441033697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35309637727792836588044929 26482228295844627441033697)
        ·
          refine ⟨19861671221883470580775273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26482228295844627441033697 19861671221883470580775273)
          ·
            refine ⟨14896253416412602935581455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19861671221883470580775273 14896253416412602935581455)
            ·
              refine ⟨22344380124618904403372183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14896253416412602935581455 22344380124618904403372183)
              ·
                refine ⟨33516570186928356605058275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22344380124618904403372183 33516570186928356605058275)
                ·
                  refine ⟨50274855280392534907587413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33516570186928356605058275 50274855280392534907587413)
                  ·
                    refine ⟨294579230158550009224145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 50274855280392534907587413 294579230158550009224145)
                    ·
                      rfl

theorem cell23_1721073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_1721073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721073 prefixEnd_1721073 := by exact prefixLift 1721073
  have htrace : WordTrace (prefixWord ++ tailWord_1721073) baseStart_1721073 baseEnd_1721073 := by
    simpa [prefixWord, tailWord_1721073, baseEnd_1721073] using wordTrace_append hprefix tailTrace_1721073
  have hstable : (prefixWord ++ tailWord_1721073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721073).length < 2 ^ (prefixWord ++ tailWord_1721073).sum := by decide
  have hdescent : baseEnd_1721073 < baseStart_1721073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721097 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 3, 3, 2]
def baseStart_1721097 : Nat := 118140960795 + 1721097 * 2 ^ 59
def prefixEnd_1721097 : Nat := 4983230072969 + 3 ^ 40 * 1721097 * 2
def baseEnd_1721097 : Nat := 883750014011357933772325

theorem tailTrace_1721097 : CollatzResearch.WordTrace tailWord_1721097 prefixEnd_1721097 883750014011357933772325 := by
  unfold tailWord_1721097
  simp only [CollatzResearch.WordTrace]
  refine ⟨62773564645766983810953545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41849043097177989207302363 62773564645766983810953545)
  ·
    refine ⟨47080173484325237858215159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62773564645766983810953545 47080173484325237858215159)
    ·
      refine ⟨70620260226487856787322739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47080173484325237858215159 70620260226487856787322739)
      ·
        refine ⟨105930390339731785180984109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70620260226487856787322739 105930390339731785180984109)
        ·
          refine ⟨39723896377399419442869041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105930390339731785180984109 39723896377399419442869041)
          ·
            refine ⟨29792922283049564582151781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39723896377399419442869041 29792922283049564582151781)
            ·
              refine ⟨5586172928071793359153459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29792922283049564582151781 5586172928071793359153459)
              ·
                refine ⟨8379259392107690038730189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5586172928071793359153459 8379259392107690038730189)
                ·
                  refine ⟨3142222272040383764523821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8379259392107690038730189 3142222272040383764523821)
                  ·
                    refine ⟨1178333352015143911696433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3142222272040383764523821 1178333352015143911696433)
                    ·
                      refine ⟨883750014011357933772325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1178333352015143911696433 883750014011357933772325)
                      ·
                        rfl

theorem cell23_1721097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 3, 2].length) (baseStart_1721097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721097 prefixEnd_1721097 := by exact prefixLift 1721097
  have htrace : WordTrace (prefixWord ++ tailWord_1721097) baseStart_1721097 baseEnd_1721097 := by
    simpa [prefixWord, tailWord_1721097, baseEnd_1721097] using wordTrace_append hprefix tailTrace_1721097
  have hstable : (prefixWord ++ tailWord_1721097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721097).length < 2 ^ (prefixWord ++ tailWord_1721097).sum := by decide
  have hdescent : baseEnd_1721097 < baseStart_1721097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721103 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 1, 8]
def baseStart_1721103 : Nat := 118140960795 + 1721103 * 2 ^ 59
def prefixEnd_1721103 : Nat := 4983230072969 + 3 ^ 40 * 1721103 * 2
def baseEnd_1721103 : Nat := 294584364965094970099099

theorem tailTrace_1721103 : CollatzResearch.WordTrace tailWord_1721103 prefixEnd_1721103 294584364965094970099099 := by
  unfold tailWord_1721103
  simp only [CollatzResearch.WordTrace]
  refine ⟨62773783483745246835671963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41849188989163497890447975 62773783483745246835671963)
  ·
    refine ⟨94160675225617870253507945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62773783483745246835671963 94160675225617870253507945)
    ·
      refine ⟨70620506419213402690130959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94160675225617870253507945 70620506419213402690130959)
      ·
        refine ⟨105930759628820104035196439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70620506419213402690130959 105930759628820104035196439)
        ·
          refine ⟨158896139443230156052794659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105930759628820104035196439 158896139443230156052794659)
          ·
            refine ⟨238344209164845234079191989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158896139443230156052794659 238344209164845234079191989)
            ·
              refine ⟨22344769609204240694924249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238344209164845234079191989 22344769609204240694924249)
              ·
                refine ⟨16758577206903180521193187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22344769609204240694924249 16758577206903180521193187)
                ·
                  refine ⟨25137865810354770781789781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16758577206903180521193187 25137865810354770781789781)
                  ·
                    refine ⟨294584364965094970099099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25137865810354770781789781 294584364965094970099099)
                    ·
                      rfl

theorem cell23_1721103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 8].length) (baseStart_1721103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721103 prefixEnd_1721103 := by exact prefixLift 1721103
  have htrace : WordTrace (prefixWord ++ tailWord_1721103) baseStart_1721103 baseEnd_1721103 := by
    simpa [prefixWord, tailWord_1721103, baseEnd_1721103] using wordTrace_append hprefix tailTrace_1721103
  have hstable : (prefixWord ++ tailWord_1721103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721103).length < 2 ^ (prefixWord ++ tailWord_1721103).sum := by decide
  have hdescent : baseEnd_1721103 < baseStart_1721103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721114 : List Nat := [3, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2]
def baseStart_1721114 : Nat := 118140960795 + 1721114 * 2 ^ 59
def prefixEnd_1721114 : Nat := 4983230072969 + 3 ^ 40 * 1721114 * 2
def baseEnd_1721114 : Nat := 883758743182484367259747

theorem tailTrace_1721114 : CollatzResearch.WordTrace tailWord_1721114 prefixEnd_1721114 883758743182484367259747 := by
  unfold tailWord_1721114
  simp only [CollatzResearch.WordTrace]
  refine ⟨15693546171676348928580599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41849456457803597142881597 15693546171676348928580599)
  ·
    refine ⟨23540319257514523392870899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15693546171676348928580599 23540319257514523392870899)
    ·
      refine ⟨35310478886271785089306349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23540319257514523392870899 35310478886271785089306349)
      ·
        refine ⟨13241429582351919408489881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35310478886271785089306349 13241429582351919408489881)
        ·
          refine ⟨9931072186763939556367411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13241429582351919408489881 9931072186763939556367411)
          ·
            refine ⟨14896608280145909334551117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9931072186763939556367411 14896608280145909334551117)
            ·
              refine ⟨5586228105054716000456669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14896608280145909334551117 5586228105054716000456669)
              ·
                refine ⟨2094835539395518500171251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5586228105054716000456669 2094835539395518500171251)
                ·
                  refine ⟨3142253309093277750256877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2094835539395518500171251 3142253309093277750256877)
                  ·
                    refine ⟨1178344990909979156346329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3142253309093277750256877 1178344990909979156346329)
                    ·
                      refine ⟨883758743182484367259747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1178344990909979156346329 883758743182484367259747)
                      ·
                        rfl

theorem cell23_1721114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_1721114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721114 prefixEnd_1721114 := by exact prefixLift 1721114
  have htrace : WordTrace (prefixWord ++ tailWord_1721114) baseStart_1721114 baseEnd_1721114 := by
    simpa [prefixWord, tailWord_1721114, baseEnd_1721114] using wordTrace_append hprefix tailTrace_1721114
  have hstable : (prefixWord ++ tailWord_1721114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721114).length < 2 ^ (prefixWord ++ tailWord_1721114).sum := by decide
  have hdescent : baseEnd_1721114 < baseStart_1721114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721120 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 2, 6]
def baseStart_1721120 : Nat := 118140960795 + 1721120 * 2 ^ 59
def prefixEnd_1721120 : Nat := 4983230072969 + 3 ^ 40 * 1721120 * 2
def baseEnd_1721120 : Nat := 294587274688803781261573

theorem tailTrace_1721120 : CollatzResearch.WordTrace tailWord_1721120 prefixEnd_1721120 294587274688803781261573 := by
  unfold tailWord_1721120
  simp only [CollatzResearch.WordTrace]
  refine ⟨31387201762341829369520407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41849602349789105826027209 31387201762341829369520407)
  ·
    refine ⟨47080802643512744054280611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31387201762341829369520407 47080802643512744054280611)
    ·
      refine ⟨70621203965269116081420917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47080802643512744054280611 70621203965269116081420917)
      ·
        refine ⟨6620737871743979632633211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70621203965269116081420917 6620737871743979632633211)
        ·
          refine ⟨9931106807615969448949817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6620737871743979632633211 9931106807615969448949817)
          ·
            refine ⟨7448330105711977086712363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9931106807615969448949817 7448330105711977086712363)
            ·
              refine ⟨11172495158567965630068545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7448330105711977086712363 11172495158567965630068545)
              ·
                refine ⟨8379371368925974222551409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11172495158567965630068545 8379371368925974222551409)
                ·
                  refine ⟨6284528526694480666913557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8379371368925974222551409 6284528526694480666913557)
                  ·
                    refine ⟨294587274688803781261573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6284528526694480666913557 294587274688803781261573)
                    ·
                      rfl

theorem cell23_1721120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 2, 6].length) (baseStart_1721120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721120 prefixEnd_1721120 := by exact prefixLift 1721120
  have htrace : WordTrace (prefixWord ++ tailWord_1721120) baseStart_1721120 baseEnd_1721120 := by
    simpa [prefixWord, tailWord_1721120, baseEnd_1721120] using wordTrace_append hprefix tailTrace_1721120
  have hstable : (prefixWord ++ tailWord_1721120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721120).length < 2 ^ (prefixWord ++ tailWord_1721120).sum := by decide
  have hdescent : baseEnd_1721120 < baseStart_1721120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721184 : List Nat := [2, 1, 1, 3, 3, 1, 5, 2, 5]
def baseStart_1721184 : Nat := 118140960795 + 1721184 * 2 ^ 59
def prefixEnd_1721184 : Nat := 4983230072969 + 3 ^ 40 * 1721184 * 2
def baseEnd_1721184 : Nat := 98199409647588788153825

theorem tailTrace_1721184 : CollatzResearch.WordTrace tailWord_1721184 prefixEnd_1721184 98199409647588788153825 := by
  unfold tailWord_1721184
  simp only [CollatzResearch.WordTrace]
  refine ⟨31388368898225898834685303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41851158530967865112913737 31388368898225898834685303)
  ·
    refine ⟨47082553347338848252027955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31388368898225898834685303 47082553347338848252027955)
    ·
      refine ⟨70623830021008272378041933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47082553347338848252027955 70623830021008272378041933)
      ·
        refine ⟨26483936257878102141765725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70623830021008272378041933 26483936257878102141765725)
        ·
          refine ⟨9931476096704288303162147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26483936257878102141765725 9931476096704288303162147)
          ·
            refine ⟨14897214145056432454743221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9931476096704288303162147 14897214145056432454743221)
            ·
              refine ⟨1396613826099040542632177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14897214145056432454743221 1396613826099040542632177)
              ·
                refine ⟨1047460369574280406974133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1396613826099040542632177 1047460369574280406974133)
                ·
                  refine ⟨98199409647588788153825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1047460369574280406974133 98199409647588788153825)
                  ·
                    rfl

theorem cell23_1721184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 5].length) (baseStart_1721184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721184 prefixEnd_1721184 := by exact prefixLift 1721184
  have htrace : WordTrace (prefixWord ++ tailWord_1721184) baseStart_1721184 baseEnd_1721184 := by
    simpa [prefixWord, tailWord_1721184, baseEnd_1721184] using wordTrace_append hprefix tailTrace_1721184
  have hstable : (prefixWord ++ tailWord_1721184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721184).length < 2 ^ (prefixWord ++ tailWord_1721184).sum := by decide
  have hdescent : baseEnd_1721184 < baseStart_1721184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721200 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 4]
def baseStart_1721200 : Nat := 118140960795 + 1721200 * 2 ^ 59
def prefixEnd_1721200 : Nat := 4983230072969 + 3 ^ 40 * 1721200 * 2
def baseEnd_1721200 : Nat := 883802902518771030784351

theorem tailTrace_1721200 : CollatzResearch.WordTrace tailWord_1721200 prefixEnd_1721200 883802902518771030784351 := by
  unfold tailWord_1721200
  simp only [CollatzResearch.WordTrace]
  refine ⟨31388660682196916200976527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41851547576262554934635369 31388660682196916200976527)
  ·
    refine ⟨47082991023295374301464791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31388660682196916200976527 47082991023295374301464791)
    ·
      refine ⟨70624486534943061452197187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47082991023295374301464791 70624486534943061452197187)
      ·
        refine ⟨105936729802414592178295781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70624486534943061452197187 105936729802414592178295781)
        ·
          refine ⟨19863136837952736033430459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105936729802414592178295781 19863136837952736033430459)
          ·
            refine ⟨29794705256929104050145689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19863136837952736033430459 29794705256929104050145689)
            ·
              refine ⟨22346028942696828037609267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29794705256929104050145689 22346028942696828037609267)
              ·
                refine ⟨33519043414045242056413901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22346028942696828037609267 33519043414045242056413901)
                ·
                  refine ⟨12569641280266965771155213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33519043414045242056413901 12569641280266965771155213)
                  ·
                    refine ⟨4713615480100112164183205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12569641280266965771155213 4713615480100112164183205)
                    ·
                      refine ⟨883802902518771030784351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4713615480100112164183205 883802902518771030784351)
                      ·
                        rfl

theorem cell23_1721200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_1721200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721200 prefixEnd_1721200 := by exact prefixLift 1721200
  have htrace : WordTrace (prefixWord ++ tailWord_1721200) baseStart_1721200 baseEnd_1721200 := by
    simpa [prefixWord, tailWord_1721200, baseEnd_1721200] using wordTrace_append hprefix tailTrace_1721200
  have hstable : (prefixWord ++ tailWord_1721200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721200).length < 2 ^ (prefixWord ++ tailWord_1721200).sum := by decide
  have hdescent : baseEnd_1721200 < baseStart_1721200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721238 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_1721238 : Nat := 118140960795 + 1721238 * 2 ^ 59
def prefixEnd_1721238 : Nat := 4983230072969 + 3 ^ 40 * 1721238 * 2
def baseEnd_1721238 : Nat := 883822414783641882109177

theorem tailTrace_1721238 : CollatzResearch.WordTrace tailWord_1721238 prefixEnd_1721238 883822414783641882109177 := by
  unfold tailWord_1721238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3923669208641010305739773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41852471558837443261224245 3923669208641010305739773)
  ·
    refine ⟨1471375953240378864652415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3923669208641010305739773 1471375953240378864652415)
    ·
      refine ⟨2207063929860568296978623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1471375953240378864652415 2207063929860568296978623)
      ·
        refine ⟨3310595894790852445467935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2207063929860568296978623 3310595894790852445467935)
        ·
          refine ⟨4965893842186278668201903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310595894790852445467935 4965893842186278668201903)
          ·
            refine ⟨7448840763279418002302855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4965893842186278668201903 7448840763279418002302855)
            ·
              refine ⟨11173261144919127003454283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7448840763279418002302855 11173261144919127003454283)
              ·
                refine ⟨16759891717378690505181425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11173261144919127003454283 16759891717378690505181425)
                ·
                  refine ⟨12569918788034017878886069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16759891717378690505181425 12569918788034017878886069)
                  ·
                    refine ⟨1178429886378189176145569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12569918788034017878886069 1178429886378189176145569)
                    ·
                      refine ⟨883822414783641882109177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1178429886378189176145569 883822414783641882109177)
                      ·
                        rfl

theorem cell23_1721238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_1721238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721238 prefixEnd_1721238 := by exact prefixLift 1721238
  have htrace : WordTrace (prefixWord ++ tailWord_1721238) baseStart_1721238 baseEnd_1721238 := by
    simpa [prefixWord, tailWord_1721238, baseEnd_1721238] using wordTrace_append hprefix tailTrace_1721238
  have hstable : (prefixWord ++ tailWord_1721238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721238).length < 2 ^ (prefixWord ++ tailWord_1721238).sum := by decide
  have hdescent : baseEnd_1721238 < baseStart_1721238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721260 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 6]
def baseStart_1721260 : Nat := 118140960795 + 1721260 * 2 ^ 59
def prefixEnd_1721260 : Nat := 4983230072969 + 3 ^ 40 * 1721260 * 2
def baseEnd_1721260 : Nat := 883833711358040796034075

theorem tailTrace_1721260 : CollatzResearch.WordTrace tailWord_1721260 prefixEnd_1721260 883833711358040796034075 := by
  unfold tailWord_1721260
  simp only [CollatzResearch.WordTrace]
  refine ⟨31389754872088231324568617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41853006496117641766091489 31389754872088231324568617)
  ·
    refine ⟨23542316154066173493426463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31389754872088231324568617 23542316154066173493426463)
    ·
      refine ⟨35313474231099260240139695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23542316154066173493426463 35313474231099260240139695)
      ·
        refine ⟨52970211346648890360209543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35313474231099260240139695 52970211346648890360209543)
        ·
          refine ⟨79455317019973335540314315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52970211346648890360209543 79455317019973335540314315)
          ·
            refine ⟨119182975529960003310471473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79455317019973335540314315 119182975529960003310471473)
            ·
              refine ⟨89387231647470002482853605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119182975529960003310471473 89387231647470002482853605)
              ·
                refine ⟨16760105933900625465535051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89387231647470002482853605 16760105933900625465535051)
                ·
                  refine ⟨25140158900850938198302577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16760105933900625465535051 25140158900850938198302577)
                  ·
                    refine ⟨18855119175638203648726933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25140158900850938198302577 18855119175638203648726933)
                    ·
                      refine ⟨883833711358040796034075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18855119175638203648726933 883833711358040796034075)
                      ·
                        rfl

theorem cell23_1721260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_1721260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721260 prefixEnd_1721260 := by exact prefixLift 1721260
  have htrace : WordTrace (prefixWord ++ tailWord_1721260) baseStart_1721260 baseEnd_1721260 := by
    simpa [prefixWord, tailWord_1721260, baseEnd_1721260] using wordTrace_append hprefix tailTrace_1721260
  have hstable : (prefixWord ++ tailWord_1721260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721260).length < 2 ^ (prefixWord ++ tailWord_1721260).sum := by decide
  have hdescent : baseEnd_1721260 < baseStart_1721260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721268 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_1721268 : Nat := 118140960795 + 1721268 * 2 ^ 59
def prefixEnd_1721268 : Nat := 4983230072969 + 3 ^ 40 * 1721268 * 2
def baseEnd_1721268 : Nat := 883837819203276764734039

theorem tailTrace_1721268 : CollatzResearch.WordTrace tailWord_1721268 prefixEnd_1721268 883837819203276764734039 := by
  unfold tailWord_1721268
  simp only [CollatzResearch.WordTrace]
  refine ⟨31389900764073740007714229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41853201018764986676952305 31389900764073740007714229)
  ·
    refine ⟨2942803196631913125723209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31389900764073740007714229 2942803196631913125723209)
    ·
      refine ⟨2207102397473934844292407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2942803196631913125723209 2207102397473934844292407)
      ·
        refine ⟨3310653596210902266438611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2207102397473934844292407 3310653596210902266438611)
        ·
          refine ⟨4965980394316353399657917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310653596210902266438611 4965980394316353399657917)
          ·
            refine ⟨1862242647868632524871719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4965980394316353399657917 1862242647868632524871719)
            ·
              refine ⟨2793363971802948787307579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1862242647868632524871719 2793363971802948787307579)
              ·
                refine ⟨4190045957704423180961369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2793363971802948787307579 4190045957704423180961369)
                ·
                  refine ⟨3142534468278317385721027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4190045957704423180961369 3142534468278317385721027)
                  ·
                    refine ⟨4713801702417476078581541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3142534468278317385721027 4713801702417476078581541)
                    ·
                      refine ⟨883837819203276764734039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4713801702417476078581541 883837819203276764734039)
                      ·
                        rfl

theorem cell23_1721268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_1721268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721268 prefixEnd_1721268 := by exact prefixLift 1721268
  have htrace : WordTrace (prefixWord ++ tailWord_1721268) baseStart_1721268 baseEnd_1721268 := by
    simpa [prefixWord, tailWord_1721268, baseEnd_1721268] using wordTrace_append hprefix tailTrace_1721268
  have hstable : (prefixWord ++ tailWord_1721268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721268).length < 2 ^ (prefixWord ++ tailWord_1721268).sum := by decide
  have hdescent : baseEnd_1721268 < baseStart_1721268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721337 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 3, 2, 4]
def baseStart_1721337 : Nat := 118140960795 + 1721337 * 2 ^ 59
def prefixEnd_1721337 : Nat := 4983230072969 + 3 ^ 40 * 1721337 * 2
def baseEnd_1721337 : Nat := 883873249368436994771221

theorem tailTrace_1721337 : CollatzResearch.WordTrace tailWord_1721337 prefixEnd_1721337 883873249368436994771221 := by
  unfold tailWord_1721337
  simp only [CollatzResearch.WordTrace]
  refine ⟨62782318164897504799690265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41854878776598336533126843 62782318164897504799690265)
  ·
    refine ⟨47086738623673128599767699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62782318164897504799690265 47086738623673128599767699)
    ·
      refine ⟨70630107935509692899651549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47086738623673128599767699 70630107935509692899651549)
      ·
        refine ⟨26486290475816134837369331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70630107935509692899651549 26486290475816134837369331)
        ·
          refine ⟨39729435713724202256053997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26486290475816134837369331 39729435713724202256053997)
          ·
            refine ⟨14898538392646575846020249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39729435713724202256053997 14898538392646575846020249)
            ·
              refine ⟨11173903794484931884515187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14898538392646575846020249 11173903794484931884515187)
              ·
                refine ⟨16760855691727397826772781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11173903794484931884515187 16760855691727397826772781)
                ·
                  refine ⟨6285320884397774185039793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16760855691727397826772781 6285320884397774185039793)
                  ·
                    refine ⟨4713990663298330638779845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6285320884397774185039793 4713990663298330638779845)
                    ·
                      refine ⟨883873249368436994771221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4713990663298330638779845 883873249368436994771221)
                      ·
                        rfl

theorem cell23_1721337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_1721337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721337 prefixEnd_1721337 := by exact prefixLift 1721337
  have htrace : WordTrace (prefixWord ++ tailWord_1721337) baseStart_1721337 baseEnd_1721337 := by
    simpa [prefixWord, tailWord_1721337, baseEnd_1721337] using wordTrace_append hprefix tailTrace_1721337
  have hstable : (prefixWord ++ tailWord_1721337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721337).length < 2 ^ (prefixWord ++ tailWord_1721337).sum := by decide
  have hdescent : baseEnd_1721337 < baseStart_1721337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721358 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2]
def baseStart_1721358 : Nat := 118140960795 + 1721358 * 2 ^ 59
def prefixEnd_1721358 : Nat := 4983230072969 + 3 ^ 40 * 1721358 * 2
def baseEnd_1721358 : Nat := 883884032462181412608625

theorem tailTrace_1721358 : CollatzResearch.WordTrace tailWord_1721358 prefixEnd_1721358 883884032462181412608625 := by
  unfold tailWord_1721358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7847885512227678173275591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41855389398547616924136485 7847885512227678173275591)
  ·
    refine ⟨11771828268341517259913387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7847885512227678173275591 11771828268341517259913387)
    ·
      refine ⟨17657742402512275889870081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11771828268341517259913387 17657742402512275889870081)
      ·
        refine ⟨13243306801884206917402561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17657742402512275889870081 13243306801884206917402561)
        ·
          refine ⟨9932480101413155188051921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13243306801884206917402561 9932480101413155188051921)
          ·
            refine ⟨7449360076059866391038941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9932480101413155188051921 7449360076059866391038941)
            ·
              refine ⟨2793510028522449896639603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7449360076059866391038941 2793510028522449896639603)
              ·
                refine ⟨4190265042783674844959405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2793510028522449896639603 4190265042783674844959405)
                ·
                  refine ⟨1571349391043878066859777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4190265042783674844959405 1571349391043878066859777)
                  ·
                    refine ⟨1178512043282908550144833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1571349391043878066859777 1178512043282908550144833)
                    ·
                      refine ⟨883884032462181412608625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1178512043282908550144833 883884032462181412608625)
                      ·
                        rfl

theorem cell23_1721358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_1721358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721358 prefixEnd_1721358 := by exact prefixLift 1721358
  have htrace : WordTrace (prefixWord ++ tailWord_1721358) baseStart_1721358 baseEnd_1721358 := by
    simpa [prefixWord, tailWord_1721358, baseEnd_1721358] using wordTrace_append hprefix tailTrace_1721358
  have hstable : (prefixWord ++ tailWord_1721358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721358).length < 2 ^ (prefixWord ++ tailWord_1721358).sum := by decide
  have hdescent : baseEnd_1721358 < baseStart_1721358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721368 : List Nat := [2, 1, 2, 3, 2, 4, 2, 1, 2, 4]
def baseStart_1721368 : Nat := 118140960795 + 1721368 * 2 ^ 59
def prefixEnd_1721368 : Nat := 4983230072969 + 3 ^ 40 * 1721368 * 2
def baseEnd_1721368 : Nat := 294629722422908791161193

theorem tailTrace_1721368 : CollatzResearch.WordTrace tailWord_1721368 prefixEnd_1721368 294629722422908791161193 := by
  unfold tailWord_1721368
  simp only [CollatzResearch.WordTrace]
  refine ⟨31391724413892598547034379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41855632551856798062712505 31391724413892598547034379)
  ·
    refine ⟨47087586620838897820551569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31391724413892598547034379 47087586620838897820551569)
    ·
      refine ⟨35315689965629173365413677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47087586620838897820551569 35315689965629173365413677)
      ·
        refine ⟨13243383737110940012030129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35315689965629173365413677 13243383737110940012030129)
        ·
          refine ⟨9932537802833205009022597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13243383737110940012030129 9932537802833205009022597)
          ·
            refine ⟨1862350838031225939191737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9932537802833205009022597 1862350838031225939191737)
            ·
              refine ⟨1396763128523419454393803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1862350838031225939191737 1396763128523419454393803)
              ·
                refine ⟨2095144692785129181590705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1396763128523419454393803 2095144692785129181590705)
                ·
                  refine ⟨1571358519588846886193029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2095144692785129181590705 1571358519588846886193029)
                  ·
                    refine ⟨294629722422908791161193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1571358519588846886193029 294629722422908791161193)
                    ·
                      rfl

theorem cell23_1721368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 2, 4].length) (baseStart_1721368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721368 prefixEnd_1721368 := by exact prefixLift 1721368
  have htrace : WordTrace (prefixWord ++ tailWord_1721368) baseStart_1721368 baseEnd_1721368 := by
    simpa [prefixWord, tailWord_1721368, baseEnd_1721368] using wordTrace_append hprefix tailTrace_1721368
  have hstable : (prefixWord ++ tailWord_1721368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721368).length < 2 ^ (prefixWord ++ tailWord_1721368).sum := by decide
  have hdescent : baseEnd_1721368 < baseStart_1721368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721378 : List Nat := [3, 3, 1, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_1721378 : Nat := 118140960795 + 1721378 * 2 ^ 59
def prefixEnd_1721378 : Nat := 4983230072969 + 3 ^ 40 * 1721378 * 2
def baseEnd_1721378 : Nat := 883894302075271334358533

theorem tailTrace_1721378 : CollatzResearch.WordTrace tailWord_1721378 prefixEnd_1721378 883894302075271334358533 := by
  unfold tailWord_1721378
  simp only [CollatzResearch.WordTrace]
  refine ⟨15695953389437242200483197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41855875705165979201288525 15695953389437242200483197)
  ·
    refine ⟨5885982521038965825181199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15695953389437242200483197 5885982521038965825181199)
    ·
      refine ⟨8828973781558448737771799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5885982521038965825181199 8828973781558448737771799)
      ·
        refine ⟨13243460672337673106657699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8828973781558448737771799 13243460672337673106657699)
        ·
          refine ⟨19865191008506509659986549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13243460672337673106657699 19865191008506509659986549)
          ·
            refine ⟨1862361657047485280623739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19865191008506509659986549 1862361657047485280623739)
            ·
              refine ⟨2793542485571227920935609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1862361657047485280623739 2793542485571227920935609)
              ·
                refine ⟨2095156864178420940701707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2793542485571227920935609 2095156864178420940701707)
                ·
                  refine ⟨3142735296267631411052561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2095156864178420940701707 3142735296267631411052561)
                  ·
                    refine ⟨2357051472200723558289421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3142735296267631411052561 2357051472200723558289421)
                    ·
                      refine ⟨883894302075271334358533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2357051472200723558289421 883894302075271334358533)
                      ·
                        rfl

theorem cell23_1721378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_1721378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721378 prefixEnd_1721378 := by exact prefixLift 1721378
  have htrace : WordTrace (prefixWord ++ tailWord_1721378) baseStart_1721378 baseEnd_1721378 := by
    simpa [prefixWord, tailWord_1721378, baseEnd_1721378] using wordTrace_append hprefix tailTrace_1721378
  have hstable : (prefixWord ++ tailWord_1721378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721378).length < 2 ^ (prefixWord ++ tailWord_1721378).sum := by decide
  have hdescent : baseEnd_1721378 < baseStart_1721378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721407 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 2, 6]
def baseStart_1721407 : Nat := 118140960795 + 1721407 * 2 ^ 59
def prefixEnd_1721407 : Nat := 4983230072969 + 3 ^ 40 * 1721407 * 2
def baseEnd_1721407 : Nat := 294636397671417240298633

theorem tailTrace_1721407 : CollatzResearch.WordTrace tailWord_1721407 prefixEnd_1721407 294636397671417240298633 := by
  unfold tailWord_1721407
  simp only [CollatzResearch.WordTrace]
  refine ⟨62784871274643906754738475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41856580849762604503158983 62784871274643906754738475)
  ·
    refine ⟨94177306911965860132107713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62784871274643906754738475 94177306911965860132107713)
    ·
      refine ⟨70632980183974395099080785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94177306911965860132107713 70632980183974395099080785)
      ·
        refine ⟨52974735137980796324310589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70632980183974395099080785 52974735137980796324310589)
        ·
          refine ⟨19865525676742798621616471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52974735137980796324310589 19865525676742798621616471)
          ·
            refine ⟨29798288515114197932424707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19865525676742798621616471 29798288515114197932424707)
            ·
              refine ⟨44697432772671296898637061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29798288515114197932424707 44697432772671296898637061)
              ·
                refine ⟨8380768644875868168494449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44697432772671296898637061 8380768644875868168494449)
                ·
                  refine ⟨6285576483656901126370837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8380768644875868168494449 6285576483656901126370837)
                  ·
                    refine ⟨294636397671417240298633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6285576483656901126370837 294636397671417240298633)
                    ·
                      rfl

theorem cell23_1721407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 6].length) (baseStart_1721407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721407 prefixEnd_1721407 := by exact prefixLift 1721407
  have htrace : WordTrace (prefixWord ++ tailWord_1721407) baseStart_1721407 baseEnd_1721407 := by
    simpa [prefixWord, tailWord_1721407, baseEnd_1721407] using wordTrace_append hprefix tailTrace_1721407
  have hstable : (prefixWord ++ tailWord_1721407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721407).length < 2 ^ (prefixWord ++ tailWord_1721407).sum := by decide
  have hdescent : baseEnd_1721407 < baseStart_1721407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721409 : List Nat := [1, 2, 5, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_1721409 : Nat := 118140960795 + 1721409 * 2 ^ 59
def prefixEnd_1721409 : Nat := 4983230072969 + 3 ^ 40 * 1721409 * 2
def baseEnd_1721409 : Nat := 883910219975560713070891

theorem tailTrace_1721409 : CollatzResearch.WordTrace tailWord_1721409 prefixEnd_1721409 883910219975560713070891 := by
  unfold tailWord_1721409
  simp only [CollatzResearch.WordTrace]
  refine ⟨62784944220636661096311281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41856629480424440730874187 62784944220636661096311281)
  ·
    refine ⟨47088708165477495822233461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62784944220636661096311281 47088708165477495822233461)
    ·
      refine ⟨4414566390513515233334387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47088708165477495822233461 4414566390513515233334387)
      ·
        refine ⟨6621849585770272850001581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4414566390513515233334387 6621849585770272850001581)
        ·
          refine ⟨2483193594663852318750593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6621849585770272850001581 2483193594663852318750593)
          ·
            refine ⟨1862395195997889239062945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2483193594663852318750593 1862395195997889239062945)
            ·
              refine ⟨1396796396998416929297209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1862395195997889239062945 1396796396998416929297209)
              ·
                refine ⟨1047597297748812696972907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1396796396998416929297209 1047597297748812696972907)
                ·
                  refine ⟨1571395946623219045459361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047597297748812696972907 1571395946623219045459361)
                  ·
                    refine ⟨1178546959967414284094521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1571395946623219045459361 1178546959967414284094521)
                    ·
                      refine ⟨883910219975560713070891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1178546959967414284094521 883910219975560713070891)
                      ·
                        rfl

theorem cell23_1721409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_1721409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721409 prefixEnd_1721409 := by exact prefixLift 1721409
  have htrace : WordTrace (prefixWord ++ tailWord_1721409) baseStart_1721409 baseEnd_1721409 := by
    simpa [prefixWord, tailWord_1721409, baseEnd_1721409] using wordTrace_append hprefix tailTrace_1721409
  have hstable : (prefixWord ++ tailWord_1721409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721409).length < 2 ^ (prefixWord ++ tailWord_1721409).sum := by decide
  have hdescent : baseEnd_1721409 < baseStart_1721409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721417 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 4, 1, 5]
def baseStart_1721417 : Nat := 118140960795 + 1721417 * 2 ^ 59
def prefixEnd_1721417 : Nat := 4983230072969 + 3 ^ 40 * 1721417 * 2
def baseEnd_1721417 : Nat := 883914327820796681770853

theorem tailTrace_1721417 : CollatzResearch.WordTrace tailWord_1721417 prefixEnd_1721417 883914327820796681770853 := by
  unfold tailWord_1721417
  simp only [CollatzResearch.WordTrace]
  refine ⟨62785236004607678462602505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41856824003071785641735003 62785236004607678462602505)
  ·
    refine ⟨47088927003455758846951879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62785236004607678462602505 47088927003455758846951879)
    ·
      refine ⟨70633390505183638270427819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47088927003455758846951879 70633390505183638270427819)
      ·
        refine ⟨105950085757775457405641729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70633390505183638270427819 105950085757775457405641729)
        ·
          refine ⟨79462564318331593054231297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105950085757775457405641729 79462564318331593054231297)
          ·
            refine ⟨59596923238748694790673473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79462564318331593054231297 59596923238748694790673473)
            ·
              refine ⟨44697692429061521093005105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59596923238748694790673473 44697692429061521093005105)
              ·
                refine ⟨33523269321796140819753829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44697692429061521093005105 33523269321796140819753829)
                ·
                  refine ⟨6285612997836776403703843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33523269321796140819753829 6285612997836776403703843)
                  ·
                    refine ⟨9428419496755164605555765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6285612997836776403703843 9428419496755164605555765)
                    ·
                      refine ⟨883914327820796681770853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9428419496755164605555765 883914327820796681770853)
                      ·
                        rfl

theorem cell23_1721417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_1721417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721417 prefixEnd_1721417 := by exact prefixLift 1721417
  have htrace : WordTrace (prefixWord ++ tailWord_1721417) baseStart_1721417 baseEnd_1721417 := by
    simpa [prefixWord, tailWord_1721417, baseEnd_1721417] using wordTrace_append hprefix tailTrace_1721417
  have hstable : (prefixWord ++ tailWord_1721417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721417).length < 2 ^ (prefixWord ++ tailWord_1721417).sum := by decide
  have hdescent : baseEnd_1721417 < baseStart_1721417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721427 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 4]
def baseStart_1721427 : Nat := 118140960795 + 1721427 * 2 ^ 59
def prefixEnd_1721427 : Nat := 4983230072969 + 3 ^ 40 * 1721427 * 2
def baseEnd_1721427 : Nat := 883919462627341642645807

theorem tailTrace_1721427 : CollatzResearch.WordTrace tailWord_1721427 prefixEnd_1721427 883919462627341642645807 := by
  unfold tailWord_1721427
  simp only [CollatzResearch.WordTrace]
  refine ⟨62785600734571450170466535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41857067156380966780311023 62785600734571450170466535)
  ·
    refine ⟨94178401101857175255699803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62785600734571450170466535 94178401101857175255699803)
    ·
      refine ⟨141267601652785762883549705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94178401101857175255699803 141267601652785762883549705)
      ·
        refine ⟨105950701239589322162662279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141267601652785762883549705 105950701239589322162662279)
        ·
          refine ⟨158926051859383983243993419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105950701239589322162662279 158926051859383983243993419)
          ·
            refine ⟨238389077789075974865990129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158926051859383983243993419 238389077789075974865990129)
            ·
              refine ⟨178791808341806981149492597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238389077789075974865990129 178791808341806981149492597)
              ·
                refine ⟨16761732032044404482764931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178791808341806981149492597 16761732032044404482764931)
                ·
                  refine ⟨25142598048066606724147397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16761732032044404482764931 25142598048066606724147397)
                  ·
                    refine ⟨4714237134012488760777637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25142598048066606724147397 4714237134012488760777637)
                    ·
                      refine ⟨883919462627341642645807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4714237134012488760777637 883919462627341642645807)
                      ·
                        rfl

theorem cell23_1721427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_1721427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721427 prefixEnd_1721427 := by exact prefixLift 1721427
  have htrace : WordTrace (prefixWord ++ tailWord_1721427) baseStart_1721427 baseEnd_1721427 := by
    simpa [prefixWord, tailWord_1721427, baseEnd_1721427] using wordTrace_append hprefix tailTrace_1721427
  have hstable : (prefixWord ++ tailWord_1721427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721427).length < 2 ^ (prefixWord ++ tailWord_1721427).sum := by decide
  have hdescent : baseEnd_1721427 < baseStart_1721427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721431 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 6, 2, 2]
def baseStart_1721431 : Nat := 118140960795 + 1721431 * 2 ^ 59
def prefixEnd_1721431 : Nat := 4983230072969 + 3 ^ 40 * 1721431 * 2
def baseEnd_1721431 : Nat := 883921516549959626995789

theorem tailTrace_1721431 : CollatzResearch.WordTrace tailWord_1721431 prefixEnd_1721431 883921516549959626995789 := by
  unfold tailWord_1721431
  simp only [CollatzResearch.WordTrace]
  refine ⟨62785746626556958853612147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41857164417704639235741431 62785746626556958853612147)
  ·
    refine ⟨94178619939835438280418221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62785746626556958853612147 94178619939835438280418221)
    ·
      refine ⟨35316982477438289355156833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94178619939835438280418221 35316982477438289355156833)
      ·
        refine ⟨26487736858078717016367625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35316982477438289355156833 26487736858078717016367625)
        ·
          refine ⟨19865802643559037762275719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26487736858078717016367625 19865802643559037762275719)
          ·
            refine ⟨29798703965338556643413579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19865802643559037762275719 29798703965338556643413579)
            ·
              refine ⟨44698055948007834965120369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29798703965338556643413579 44698055948007834965120369)
              ·
                refine ⟨33523541961005876223840277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44698055948007834965120369 33523541961005876223840277)
                ·
                  refine ⟨1571416029422150447992513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33523541961005876223840277 1571416029422150447992513)
                  ·
                    refine ⟨1178562022066612835994385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1571416029422150447992513 1178562022066612835994385)
                    ·
                      refine ⟨883921516549959626995789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1178562022066612835994385 883921516549959626995789)
                      ·
                        rfl

theorem cell23_1721431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_1721431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721431 prefixEnd_1721431 := by exact prefixLift 1721431
  have htrace : WordTrace (prefixWord ++ tailWord_1721431) baseStart_1721431 baseEnd_1721431 := by
    simpa [prefixWord, tailWord_1721431, baseEnd_1721431] using wordTrace_append hprefix tailTrace_1721431
  have hstable : (prefixWord ++ tailWord_1721431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721431).length < 2 ^ (prefixWord ++ tailWord_1721431).sum := by decide
  have hdescent : baseEnd_1721431 < baseStart_1721431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721464 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 2, 3, 3]
def baseStart_1721464 : Nat := 118140960795 + 1721464 * 2 ^ 59
def prefixEnd_1721464 : Nat := 4983230072969 + 3 ^ 40 * 1721464 * 2
def baseEnd_1721464 : Nat := 883938461411557997883137

theorem tailTrace_1721464 : CollatzResearch.WordTrace tailWord_1721464 prefixEnd_1721464 883938461411557997883137 := by
  unfold tailWord_1721464
  simp only [CollatzResearch.WordTrace]
  refine ⟨31393475117718702744781723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41857966823624936993042297 31393475117718702744781723)
  ·
    refine ⟨47090212676578054117172585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31393475117718702744781723 47090212676578054117172585)
    ·
      refine ⟨35317659507433540587879439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47090212676578054117172585 35317659507433540587879439)
      ·
        refine ⟨52976489261150310881819159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35317659507433540587879439 52976489261150310881819159)
        ·
          refine ⟨79464733891725466322728739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52976489261150310881819159 79464733891725466322728739)
          ·
            refine ⟨119197100837588199484093109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79464733891725466322728739 119197100837588199484093109)
            ·
              refine ⟨11174728203523893701633729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119197100837588199484093109 11174728203523893701633729)
              ·
                refine ⟨8381046152642920276225297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11174728203523893701633729 8381046152642920276225297)
                ·
                  refine ⟨6285784614482190207168973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8381046152642920276225297 6285784614482190207168973)
                  ·
                    refine ⟨2357169230430821327688365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6285784614482190207168973 2357169230430821327688365)
                    ·
                      refine ⟨883938461411557997883137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2357169230430821327688365 883938461411557997883137)
                      ·
                        rfl

theorem cell23_1721464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_1721464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721464 prefixEnd_1721464 := by exact prefixLift 1721464
  have htrace : WordTrace (prefixWord ++ tailWord_1721464) baseStart_1721464 baseEnd_1721464 := by
    simpa [prefixWord, tailWord_1721464, baseEnd_1721464] using wordTrace_append hprefix tailTrace_1721464
  have hstable : (prefixWord ++ tailWord_1721464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721464).length < 2 ^ (prefixWord ++ tailWord_1721464).sum := by decide
  have hdescent : baseEnd_1721464 < baseStart_1721464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721504 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 4]
def baseStart_1721504 : Nat := 118140960795 + 1721504 * 2 ^ 59
def prefixEnd_1721504 : Nat := 4983230072969 + 3 ^ 40 * 1721504 * 2
def baseEnd_1721504 : Nat := 883959000637737841382953

theorem tailTrace_1721504 : CollatzResearch.WordTrace tailWord_1721504 prefixEnd_1721504 883959000637737841382953 := by
  unfold tailWord_1721504
  simp only [CollatzResearch.WordTrace]
  refine ⟨31394204577646246160509783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41858939436861661547346377 31394204577646246160509783)
  ·
    refine ⟨47091306866469369240764675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31394204577646246160509783 47091306866469369240764675)
    ·
      refine ⟨70636960299704053861147013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47091306866469369240764675 70636960299704053861147013)
      ·
        refine ⟨13244430056194510098965065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70636960299704053861147013 13244430056194510098965065)
        ·
          refine ⟨9933322542145882574223799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13244430056194510098965065 9933322542145882574223799)
          ·
            refine ⟨14899983813218823861335699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9933322542145882574223799 14899983813218823861335699)
            ·
              refine ⟨22349975719828235792003549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14899983813218823861335699 22349975719828235792003549)
              ·
                refine ⟨8381240894935588422001331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22349975719828235792003549 8381240894935588422001331)
                ·
                  refine ⟨12571861342403382633001997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8381240894935588422001331 12571861342403382633001997)
                  ·
                    refine ⟨4714448003401268487375749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12571861342403382633001997 4714448003401268487375749)
                    ·
                      refine ⟨883959000637737841382953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4714448003401268487375749 883959000637737841382953)
                      ·
                        rfl

theorem cell23_1721504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_1721504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721504 prefixEnd_1721504 := by exact prefixLift 1721504
  have htrace : WordTrace (prefixWord ++ tailWord_1721504) baseStart_1721504 baseEnd_1721504 := by
    simpa [prefixWord, tailWord_1721504, baseEnd_1721504] using wordTrace_append hprefix tailTrace_1721504
  have hstable : (prefixWord ++ tailWord_1721504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721504).length < 2 ^ (prefixWord ++ tailWord_1721504).sum := by decide
  have hdescent : baseEnd_1721504 < baseStart_1721504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721521 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1721521 : Nat := 118140960795 + 1721521 * 2 ^ 59
def prefixEnd_1721521 : Nat := 4983230072969 + 3 ^ 40 * 1721521 * 2
def baseEnd_1721521 : Nat := 883967729808864274870375

theorem tailTrace_1721521 : CollatzResearch.WordTrace tailWord_1721521 prefixEnd_1721521 883967729808864274870375 := by
  unfold tailWord_1721521
  simp only [CollatzResearch.WordTrace]
  refine ⟨62789029196230904224388417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41859352797487269482925611 62789029196230904224388417)
  ·
    refine ⟨47091771897173178168291313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62789029196230904224388417 47091771897173178168291313)
    ·
      refine ⟨35318828922879883626218485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47091771897173178168291313 35318828922879883626218485)
      ·
        refine ⟨3311140211519989089957983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35318828922879883626218485 3311140211519989089957983)
        ·
          refine ⟨4966710317279983634936975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3311140211519989089957983 4966710317279983634936975)
          ·
            refine ⟨7450065475919975452405463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4966710317279983634936975 7450065475919975452405463)
            ·
              refine ⟨11175098213879963178608195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7450065475919975452405463 11175098213879963178608195)
              ·
                refine ⟨16762647320819944767912293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11175098213879963178608195 16762647320819944767912293)
                ·
                  refine ⟨3142996372653739643983555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16762647320819944767912293 3142996372653739643983555)
                  ·
                    refine ⟨4714494558980609465975333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3142996372653739643983555 4714494558980609465975333)
                    ·
                      refine ⟨883967729808864274870375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4714494558980609465975333 883967729808864274870375)
                      ·
                        rfl

theorem cell23_1721521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1721521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721521 prefixEnd_1721521 := by exact prefixLift 1721521
  have htrace : WordTrace (prefixWord ++ tailWord_1721521) baseStart_1721521 baseEnd_1721521 := by
    simpa [prefixWord, tailWord_1721521, baseEnd_1721521] using wordTrace_append hprefix tailTrace_1721521
  have hstable : (prefixWord ++ tailWord_1721521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721521).length < 2 ^ (prefixWord ++ tailWord_1721521).sum := by decide
  have hdescent : baseEnd_1721521 < baseStart_1721521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721611 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 4]
def baseStart_1721611 : Nat := 118140960795 + 1721611 * 2 ^ 59
def prefixEnd_1721611 : Nat := 4983230072969 + 3 ^ 40 * 1721611 * 2
def baseEnd_1721611 : Nat := 884013943067768922744961

theorem tailTrace_1721611 : CollatzResearch.WordTrace tailWord_1721611 prefixEnd_1721611 884013943067768922744961 := by
  unfold tailWord_1721611
  simp only [CollatzResearch.WordTrace]
  refine ⟨62792311765904849595164687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41861541177269899730109791 62792311765904849595164687)
  ·
    refine ⟨94188467648857274392747031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62792311765904849595164687 94188467648857274392747031)
    ·
      refine ⟨141282701473285911589120547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94188467648857274392747031 141282701473285911589120547)
      ·
        refine ⟨211924052209928867383680821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141282701473285911589120547 211924052209928867383680821)
        ·
          refine ⟨19867879894680831317220077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211924052209928867383680821 19867879894680831317220077)
          ·
            refine ⟨7450454960505311743957529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19867879894680831317220077 7450454960505311743957529)
            ·
              refine ⟨5587841220378983807968147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7450454960505311743957529 5587841220378983807968147)
              ·
                refine ⟨8381761830568475711952221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5587841220378983807968147 8381761830568475711952221)
                ·
                  refine ⟨3143160686463178391982083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8381761830568475711952221 3143160686463178391982083)
                  ·
                    refine ⟨4714741029694767587973125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3143160686463178391982083 4714741029694767587973125)
                    ·
                      refine ⟨884013943067768922744961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4714741029694767587973125 884013943067768922744961)
                      ·
                        rfl

theorem cell23_1721611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 4].length) (baseStart_1721611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721611 prefixEnd_1721611 := by exact prefixLift 1721611
  have htrace : WordTrace (prefixWord ++ tailWord_1721611) baseStart_1721611 baseEnd_1721611 := by
    simpa [prefixWord, tailWord_1721611, baseEnd_1721611] using wordTrace_append hprefix tailTrace_1721611
  have hstable : (prefixWord ++ tailWord_1721611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721611).length < 2 ^ (prefixWord ++ tailWord_1721611).sum := by decide
  have hdescent : baseEnd_1721611 < baseStart_1721611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721621 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 4, 4]
def baseStart_1721621 : Nat := 118140960795 + 1721621 * 2 ^ 59
def prefixEnd_1721621 : Nat := 4983230072969 + 3 ^ 40 * 1721621 * 2
def baseEnd_1721621 : Nat := 294673025958104627873305

theorem tailTrace_1721621 : CollatzResearch.WordTrace tailWord_1721621 prefixEnd_1721621 294673025958104627873305 := by
  unfold tailWord_1721621
  simp only [CollatzResearch.WordTrace]
  refine ⟨62792676495868621303028717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41861784330579080868685811 62792676495868621303028717)
  ·
    refine ⟨23547253685950732988635769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62792676495868621303028717 23547253685950732988635769)
    ·
      refine ⟨17660440264463049741476827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23547253685950732988635769 17660440264463049741476827)
      ·
        refine ⟨26490660396694574612215241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17660440264463049741476827 26490660396694574612215241)
        ·
          refine ⟨19867995297520930959161431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26490660396694574612215241 19867995297520930959161431)
          ·
            refine ⟨29801992946281396438742147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19867995297520930959161431 29801992946281396438742147)
            ·
              refine ⟨44702989419422094658113221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29801992946281396438742147 44702989419422094658113221)
              ·
                refine ⟨8381810516141642748396229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44702989419422094658113221 8381810516141642748396229)
                ·
                  refine ⟨1571589471776558015324293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8381810516141642748396229 1571589471776558015324293)
                  ·
                    refine ⟨294673025958104627873305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1571589471776558015324293 294673025958104627873305)
                    ·
                      rfl

theorem cell23_1721621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_1721621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721621 prefixEnd_1721621 := by exact prefixLift 1721621
  have htrace : WordTrace (prefixWord ++ tailWord_1721621) baseStart_1721621 baseEnd_1721621 := by
    simpa [prefixWord, tailWord_1721621, baseEnd_1721621] using wordTrace_append hprefix tailTrace_1721621
  have hstable : (prefixWord ++ tailWord_1721621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721621).length < 2 ^ (prefixWord ++ tailWord_1721621).sum := by decide
  have hdescent : baseEnd_1721621 < baseStart_1721621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721644 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 7]
def baseStart_1721644 : Nat := 118140960795 + 1721644 * 2 ^ 59
def prefixEnd_1721644 : Nat := 4983230072969 + 3 ^ 40 * 1721644 * 2
def baseEnd_1721644 : Nat := 884030887929367293632309

theorem tailTrace_1721644 : CollatzResearch.WordTrace tailWord_1721644 prefixEnd_1721644 884030887929367293632309 := by
  unfold tailWord_1721644
  simp only [CollatzResearch.WordTrace]
  refine ⟨31396757687392648115557993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41862343583190197487410657 31396757687392648115557993)
  ·
    refine ⟨23547568265544486086668495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31396757687392648115557993 23547568265544486086668495)
    ·
      refine ⟨35321352398316729130002743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23547568265544486086668495 35321352398316729130002743)
      ·
        refine ⟨52982028597475093695004115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35321352398316729130002743 52982028597475093695004115)
        ·
          refine ⟨79473042896212640542506173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52982028597475093695004115 79473042896212640542506173)
          ·
            refine ⟨29802391086079740203439815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79473042896212640542506173 29802391086079740203439815)
            ·
              refine ⟨44703586629119610305159723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29802391086079740203439815 44703586629119610305159723)
              ·
                refine ⟨67055379943679415457739585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44703586629119610305159723 67055379943679415457739585)
                ·
                  refine ⟨50291534957759561593304689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67055379943679415457739585 50291534957759561593304689)
                  ·
                    refine ⟨37718651218319671194978517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50291534957759561593304689 37718651218319671194978517)
                    ·
                      refine ⟨884030887929367293632309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37718651218319671194978517 884030887929367293632309)
                      ·
                        rfl

theorem cell23_1721644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_1721644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721644 prefixEnd_1721644 := by exact prefixLift 1721644
  have htrace : WordTrace (prefixWord ++ tailWord_1721644) baseStart_1721644 baseEnd_1721644 := by
    simpa [prefixWord, tailWord_1721644, baseEnd_1721644] using wordTrace_append hprefix tailTrace_1721644
  have hstable : (prefixWord ++ tailWord_1721644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721644).length < 2 ^ (prefixWord ++ tailWord_1721644).sum := by decide
  have hdescent : baseEnd_1721644 < baseStart_1721644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721665 : List Nat := [1, 2, 5, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1721665 : Nat := 118140960795 + 1721665 * 2 ^ 59
def prefixEnd_1721665 : Nat := 4983230072969 + 3 ^ 40 * 1721665 * 2
def baseEnd_1721665 : Nat := 884041671023111711469713

theorem tailTrace_1721665 : CollatzResearch.WordTrace tailWord_1721665 prefixEnd_1721665 884041671023111711469713 := by
  unfold tailWord_1721665
  simp only [CollatzResearch.WordTrace]
  refine ⟨62794281307709216817630449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41862854205139477878420299 62794281307709216817630449)
  ·
    refine ⟨47095710980781912613222837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62794281307709216817630449 47095710980781912613222837)
    ·
      refine ⟨4415222904448304307489641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47095710980781912613222837 4415222904448304307489641)
      ·
        refine ⟨3311417178336228230617231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4415222904448304307489641 3311417178336228230617231)
        ·
          refine ⟨4967125767504342345925847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3311417178336228230617231 4967125767504342345925847)
          ·
            refine ⟨7450688651256513518888771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4967125767504342345925847 7450688651256513518888771)
            ·
              refine ⟨11176032976884770278333157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7450688651256513518888771 11176032976884770278333157)
              ·
                refine ⟨2095506183165894427187467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11176032976884770278333157 2095506183165894427187467)
                ·
                  refine ⟨3143259274748841640781201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2095506183165894427187467 3143259274748841640781201)
                  ·
                    refine ⟨2357444456061631230585901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3143259274748841640781201 2357444456061631230585901)
                    ·
                      refine ⟨884041671023111711469713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2357444456061631230585901 884041671023111711469713)
                      ·
                        rfl

theorem cell23_1721665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1721665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721665 prefixEnd_1721665 := by exact prefixLift 1721665
  have htrace : WordTrace (prefixWord ++ tailWord_1721665) baseStart_1721665 baseEnd_1721665 := by
    simpa [prefixWord, tailWord_1721665, baseEnd_1721665] using wordTrace_append hprefix tailTrace_1721665
  have hstable : (prefixWord ++ tailWord_1721665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721665).length < 2 ^ (prefixWord ++ tailWord_1721665).sum := by decide
  have hdescent : baseEnd_1721665 < baseStart_1721665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721668 : List Nat := [2, 3, 4, 1, 1, 2, 1, 9]
def baseStart_1721668 : Nat := 118140960795 + 1721668 * 2 ^ 59
def prefixEnd_1721668 : Nat := 4983230072969 + 3 ^ 40 * 1721668 * 2
def baseEnd_1721668 : Nat := 32742341165373155545637

theorem tailTrace_1721668 : CollatzResearch.WordTrace tailWord_1721668 prefixEnd_1721668 32742341165373155545637 := by
  unfold tailWord_1721668
  simp only [CollatzResearch.WordTrace]
  refine ⟨31397195363349174164994829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41862927151132232219993105 31397195363349174164994829)
  ·
    refine ⟨11773948261255940311873061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31397195363349174164994829 11773948261255940311873061)
    ·
      refine ⟨2207615298985488808476199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11773948261255940311873061 2207615298985488808476199)
      ·
        refine ⟨3311422948478233212714299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2207615298985488808476199 3311422948478233212714299)
        ·
          refine ⟨4967134422717349819071449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3311422948478233212714299 4967134422717349819071449)
          ·
            refine ⟨3725350817038012364303587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4967134422717349819071449 3725350817038012364303587)
            ·
              refine ⟨5588026225557018546455381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3725350817038012364303587 5588026225557018546455381)
              ·
                refine ⟨32742341165373155545637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5588026225557018546455381 32742341165373155545637)
                ·
                  rfl

theorem cell23_1721668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 9].length) (baseStart_1721668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721668 prefixEnd_1721668 := by exact prefixLift 1721668
  have htrace : WordTrace (prefixWord ++ tailWord_1721668) baseStart_1721668 baseEnd_1721668 := by
    simpa [prefixWord, tailWord_1721668, baseEnd_1721668] using wordTrace_append hprefix tailTrace_1721668
  have hstable : (prefixWord ++ tailWord_1721668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721668).length < 2 ^ (prefixWord ++ tailWord_1721668).sum := by decide
  have hdescent : baseEnd_1721668 < baseStart_1721668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721678 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3]
def baseStart_1721678 : Nat := 118140960795 + 1721678 * 2 ^ 59
def prefixEnd_1721678 : Nat := 4983230072969 + 3 ^ 40 * 1721678 * 2
def baseEnd_1721678 : Nat := 884048346271620160607153

theorem tailTrace_1721678 : CollatzResearch.WordTrace tailWord_1721678 prefixEnd_1721678 884048346271620160607153 := by
  unfold tailWord_1721678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7849344432082765004731711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41863170304441413358569125 7849344432082765004731711)
  ·
    refine ⟨11774016648124147507097567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7849344432082765004731711 11774016648124147507097567)
    ·
      refine ⟨17661024972186221260646351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11774016648124147507097567 17661024972186221260646351)
      ·
        refine ⟨26491537458279331890969527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17661024972186221260646351 26491537458279331890969527)
        ·
          refine ⟨39737306187418997836454291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26491537458279331890969527 39737306187418997836454291)
          ·
            refine ⟨59605959281128496754681437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39737306187418997836454291 59605959281128496754681437)
            ·
              refine ⟨22352234730423186283005539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59605959281128496754681437 22352234730423186283005539)
              ·
                refine ⟨33528352095634779424508309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22352234730423186283005539 33528352095634779424508309)
                ·
                  refine ⟨1571641504482880285523827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33528352095634779424508309 1571641504482880285523827)
                  ·
                    refine ⟨2357462256724320428285741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1571641504482880285523827 2357462256724320428285741)
                    ·
                      refine ⟨884048346271620160607153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2357462256724320428285741 884048346271620160607153)
                      ·
                        rfl

theorem cell23_1721678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_1721678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721678 prefixEnd_1721678 := by exact prefixLift 1721678
  have htrace : WordTrace (prefixWord ++ tailWord_1721678) baseStart_1721678 baseEnd_1721678 := by
    simpa [prefixWord, tailWord_1721678, baseEnd_1721678] using wordTrace_append hprefix tailTrace_1721678
  have hstable : (prefixWord ++ tailWord_1721678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721678).length < 2 ^ (prefixWord ++ tailWord_1721678).sum := by decide
  have hdescent : baseEnd_1721678 < baseStart_1721678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721701 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 2, 3, 4]
def baseStart_1721701 : Nat := 118140960795 + 1721701 * 2 ^ 59
def prefixEnd_1721701 : Nat := 4983230072969 + 3 ^ 40 * 1721701 * 2
def baseEnd_1721701 : Nat := 884060156326673570619547

theorem tailTrace_1721701 : CollatzResearch.WordTrace tailWord_1721701 prefixEnd_1721701 884060156326673570619547 := by
  unfold tailWord_1721701
  simp only [CollatzResearch.WordTrace]
  refine ⟨62795594335578794965940957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41863729557052529977293971 62795594335578794965940957)
  ·
    refine ⟨23548347875842048112227859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62795594335578794965940957 23548347875842048112227859)
    ·
      refine ⟨35322521813763072168341789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23548347875842048112227859 35322521813763072168341789)
      ·
        refine ⟨13245945680161152063128171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35322521813763072168341789 13245945680161152063128171)
        ·
          refine ⟨19868918520241728094692257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13245945680161152063128171 19868918520241728094692257)
          ·
            refine ⟨14901688890181296071019193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19868918520241728094692257 14901688890181296071019193)
            ·
              refine ⟨11176266667635972053264395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14901688890181296071019193 11176266667635972053264395)
              ·
                refine ⟨16764400001453958079896593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11176266667635972053264395 16764400001453958079896593)
                ·
                  refine ⟨12573300001090468559922445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16764400001453958079896593 12573300001090468559922445)
                  ·
                    refine ⟨4714987500408925709970917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12573300001090468559922445 4714987500408925709970917)
                    ·
                      refine ⟨884060156326673570619547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4714987500408925709970917 884060156326673570619547)
                      ·
                        rfl

theorem cell23_1721701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_1721701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721701 prefixEnd_1721701 := by exact prefixLift 1721701
  have htrace : WordTrace (prefixWord ++ tailWord_1721701) baseStart_1721701 baseEnd_1721701 := by
    simpa [prefixWord, tailWord_1721701, baseEnd_1721701] using wordTrace_append hprefix tailTrace_1721701
  have hstable : (prefixWord ++ tailWord_1721701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721701).length < 2 ^ (prefixWord ++ tailWord_1721701).sum := by decide
  have hdescent : baseEnd_1721701 < baseStart_1721701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721721 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 2, 1, 5]
def baseStart_1721721 : Nat := 118140960795 + 1721721 * 2 ^ 59
def prefixEnd_1721721 : Nat := 4983230072969 + 3 ^ 40 * 1721721 * 2
def baseEnd_1721721 : Nat := 884070425939763492369455

theorem tailTrace_1721721 : CollatzResearch.WordTrace tailWord_1721721 prefixEnd_1721721 884070425939763492369455 := by
  unfold tailWord_1721721
  simp only [CollatzResearch.WordTrace]
  refine ⟨62796323795506338381669017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41864215863670892254446011 62796323795506338381669017)
  ·
    refine ⟨47097242846629753786251763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62796323795506338381669017 47097242846629753786251763)
    ·
      refine ⟨70645864269944630679377645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47097242846629753786251763 70645864269944630679377645)
      ·
        refine ⟨26492199101229236504766617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70645864269944630679377645 26492199101229236504766617)
        ·
          refine ⟨19869149325921927378574963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26492199101229236504766617 19869149325921927378574963)
          ·
            refine ⟨29803723988882891067862445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19869149325921927378574963 29803723988882891067862445)
            ·
              refine ⟨11176396495831084150448417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29803723988882891067862445 11176396495831084150448417)
              ·
                refine ⟨8382297371873313112836313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11176396495831084150448417 8382297371873313112836313)
                ·
                  refine ⟨6286723028904984834627235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8382297371873313112836313 6286723028904984834627235)
                  ·
                    refine ⟨9430084543357477251940853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6286723028904984834627235 9430084543357477251940853)
                    ·
                      refine ⟨884070425939763492369455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9430084543357477251940853 884070425939763492369455)
                      ·
                        rfl

theorem cell23_1721721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_1721721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721721 prefixEnd_1721721 := by exact prefixLift 1721721
  have htrace : WordTrace (prefixWord ++ tailWord_1721721) baseStart_1721721 baseEnd_1721721 := by
    simpa [prefixWord, tailWord_1721721, baseEnd_1721721] using wordTrace_append hprefix tailTrace_1721721
  have hstable : (prefixWord ++ tailWord_1721721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721721).length < 2 ^ (prefixWord ++ tailWord_1721721).sum := by decide
  have hdescent : baseEnd_1721721 < baseStart_1721721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721735 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 1, 4, 2]
def baseStart_1721735 : Nat := 118140960795 + 1721735 * 2 ^ 59
def prefixEnd_1721735 : Nat := 4983230072969 + 3 ^ 40 * 1721735 * 2
def baseEnd_1721735 : Nat := 884077614668926437594391

theorem tailTrace_1721735 : CollatzResearch.WordTrace tailWord_1721735 prefixEnd_1721735 884077614668926437594391 := by
  unfold tailWord_1721735
  simp only [CollatzResearch.WordTrace]
  refine ⟨62796834417455618772678659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41864556278303745848452439 62796834417455618772678659)
  ·
    refine ⟨94195251626183428159017989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62796834417455618772678659 94195251626183428159017989)
    ·
      refine ⟨17661609679909392779815873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94195251626183428159017989 17661609679909392779815873)
      ·
        refine ⟨13246207259932044584861905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17661609679909392779815873 13246207259932044584861905)
        ·
          refine ⟨9934655444949033438646429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13246207259932044584861905 9934655444949033438646429)
          ·
            refine ⟨3725495791855887539492411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9934655444949033438646429 3725495791855887539492411)
            ·
              refine ⟨5588243687783831309238617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3725495791855887539492411 5588243687783831309238617)
              ·
                refine ⟨4191182765837873481928963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5588243687783831309238617 4191182765837873481928963)
                ·
                  refine ⟨6286774148756810222893445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4191182765837873481928963 6286774148756810222893445)
                  ·
                    refine ⟨1178770152891901916792521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6286774148756810222893445 1178770152891901916792521)
                    ·
                      refine ⟨884077614668926437594391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1178770152891901916792521 884077614668926437594391)
                      ·
                        rfl

theorem cell23_1721735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_1721735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721735 prefixEnd_1721735 := by exact prefixLift 1721735
  have htrace : WordTrace (prefixWord ++ tailWord_1721735) baseStart_1721735 baseEnd_1721735 := by
    simpa [prefixWord, tailWord_1721735, baseEnd_1721735] using wordTrace_append hprefix tailTrace_1721735
  have hstable : (prefixWord ++ tailWord_1721735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721735).length < 2 ^ (prefixWord ++ tailWord_1721735).sum := by decide
  have hdescent : baseEnd_1721735 < baseStart_1721735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721808 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 3, 6, 2]
def baseStart_1721808 : Nat := 118140960795 + 1721808 * 2 ^ 59
def prefixEnd_1721808 : Nat := 4983230072969 + 3 ^ 40 * 1721808 * 2
def baseEnd_1721808 : Nat := 884115098756704651981555

theorem tailTrace_1721808 : CollatzResearch.WordTrace tailWord_1721808 prefixEnd_1721808 884115098756704651981555 := by
  unfold tailWord_1721808
  simp only [CollatzResearch.WordTrace]
  refine ⟨31399748473095576120043039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41866331297460768160057385 31399748473095576120043039)
  ·
    refine ⟨47099622709643364180064559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31399748473095576120043039 47099622709643364180064559)
    ·
      refine ⟨70649434064465046270096839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47099622709643364180064559 70649434064465046270096839)
      ·
        refine ⟨105974151096697569405145259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70649434064465046270096839 105974151096697569405145259)
        ·
          refine ⟨158961226645046354107717889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105974151096697569405145259 158961226645046354107717889)
          ·
            refine ⟨119220919983784765580788417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158961226645046354107717889 119220919983784765580788417)
            ·
              refine ⟨89415689987838574185591313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119220919983784765580788417 89415689987838574185591313)
              ·
                refine ⟨67061767490878930639193485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89415689987838574185591313 67061767490878930639193485)
                ·
                  refine ⟨25148162809079598989697557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67061767490878930639193485 25148162809079598989697557)
                  ·
                    refine ⟨1178820131675606202642073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25148162809079598989697557 1178820131675606202642073)
                    ·
                      refine ⟨884115098756704651981555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1178820131675606202642073 884115098756704651981555)
                      ·
                        rfl

theorem cell23_1721808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 6, 2].length) (baseStart_1721808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721808 prefixEnd_1721808 := by exact prefixLift 1721808
  have htrace : WordTrace (prefixWord ++ tailWord_1721808) baseStart_1721808 baseEnd_1721808 := by
    simpa [prefixWord, tailWord_1721808, baseEnd_1721808] using wordTrace_append hprefix tailTrace_1721808
  have hstable : (prefixWord ++ tailWord_1721808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721808).length < 2 ^ (prefixWord ++ tailWord_1721808).sum := by decide
  have hdescent : baseEnd_1721808 < baseStart_1721808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721825 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 2, 4, 2]
def baseStart_1721825 : Nat := 118140960795 + 1721825 * 2 ^ 59
def prefixEnd_1721825 : Nat := 4983230072969 + 3 ^ 40 * 1721825 * 2
def baseEnd_1721825 : Nat := 884123827927831085468977

theorem tailTrace_1721825 : CollatzResearch.WordTrace tailWord_1721825 prefixEnd_1721825 884123827927831085468977 := by
  unfold tailWord_1721825
  simp only [CollatzResearch.WordTrace]
  refine ⟨62800116987129564143454929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41866744658086376095636619 62800116987129564143454929)
  ·
    refine ⟨47100087740347173107591197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62800116987129564143454929 47100087740347173107591197)
    ·
      refine ⟨17662532902630189915346699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47100087740347173107591197 17662532902630189915346699)
      ·
        refine ⟨26493799353945284873020049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17662532902630189915346699 26493799353945284873020049)
        ·
          refine ⟨19870349515458963654765037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26493799353945284873020049 19870349515458963654765037)
          ·
            refine ⟨7451381068297111370536889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19870349515458963654765037 7451381068297111370536889)
            ·
              refine ⟨5588535801222833527902667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7451381068297111370536889 5588535801222833527902667)
              ·
                refine ⟨8382803701834250291854001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5588535801222833527902667 8382803701834250291854001)
                ·
                  refine ⟨6287102776375687718890501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8382803701834250291854001 6287102776375687718890501)
                  ·
                    refine ⟨1178831770570441447291969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6287102776375687718890501 1178831770570441447291969)
                    ·
                      refine ⟨884123827927831085468977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1178831770570441447291969 884123827927831085468977)
                      ·
                        rfl

theorem cell23_1721825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_1721825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721825 prefixEnd_1721825 := by exact prefixLift 1721825
  have htrace : WordTrace (prefixWord ++ tailWord_1721825) baseStart_1721825 baseEnd_1721825 := by
    simpa [prefixWord, tailWord_1721825, baseEnd_1721825] using wordTrace_append hprefix tailTrace_1721825
  have hstable : (prefixWord ++ tailWord_1721825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721825).length < 2 ^ (prefixWord ++ tailWord_1721825).sum := by decide
  have hdescent : baseEnd_1721825 < baseStart_1721825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721838 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_1721838 : Nat := 118140960795 + 1721838 * 2 ^ 59
def prefixEnd_1721838 : Nat := 4983230072969 + 3 ^ 40 * 1721838 * 2
def baseEnd_1721838 : Nat := 884130503176339534606417

theorem tailTrace_1721838 : CollatzResearch.WordTrace tailWord_1721838 prefixEnd_1721838 884130503176339534606417 := by
  unfold tailWord_1721838
  simp only [CollatzResearch.WordTrace]
  refine ⟨7850073892010308420459771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41867060757388311575785445 7850073892010308420459771)
  ·
    refine ⟨11775110838015462630689657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7850073892010308420459771 11775110838015462630689657)
    ·
      refine ⟨8831333128511596973017243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11775110838015462630689657 8831333128511596973017243)
      ·
        refine ⟨13246999692767395459525865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8831333128511596973017243 13246999692767395459525865)
        ·
          refine ⟨9935249769575546594644399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13246999692767395459525865 9935249769575546594644399)
          ·
            refine ⟨14902874654363319891966599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9935249769575546594644399 14902874654363319891966599)
            ·
              refine ⟨22354311981544979837949899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14902874654363319891966599 22354311981544979837949899)
              ·
                refine ⟨33531467972317469756924849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22354311981544979837949899 33531467972317469756924849)
                ·
                  refine ⟨25148600979238102317693637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33531467972317469756924849 25148600979238102317693637)
                  ·
                    refine ⟨4715362683607144184567557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25148600979238102317693637 4715362683607144184567557)
                    ·
                      refine ⟨884130503176339534606417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4715362683607144184567557 884130503176339534606417)
                      ·
                        rfl

theorem cell23_1721838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_1721838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721838 prefixEnd_1721838 := by exact prefixLift 1721838
  have htrace : WordTrace (prefixWord ++ tailWord_1721838) baseStart_1721838 baseEnd_1721838 := by
    simpa [prefixWord, tailWord_1721838, baseEnd_1721838] using wordTrace_append hprefix tailTrace_1721838
  have hstable : (prefixWord ++ tailWord_1721838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721838).length < 2 ^ (prefixWord ++ tailWord_1721838).sum := by decide
  have hdescent : baseEnd_1721838 < baseStart_1721838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721851 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 6]
def baseStart_1721851 : Nat := 118140960795 + 1721851 * 2 ^ 59
def prefixEnd_1721851 : Nat := 4983230072969 + 3 ^ 40 * 1721851 * 2
def baseEnd_1721851 : Nat := 884137178424847983743857

theorem tailTrace_1721851 : CollatzResearch.WordTrace tailWord_1721851 prefixEnd_1721851 884137178424847983743857 := by
  unfold tailWord_1721851
  simp only [CollatzResearch.WordTrace]
  refine ⟨62801065285035370583901407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41867376856690247055934271 62801065285035370583901407)
  ·
    refine ⟨94201597927553055875852111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62801065285035370583901407 94201597927553055875852111)
    ·
      refine ⟨141302396891329583813778167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94201597927553055875852111 141302396891329583813778167)
      ·
        refine ⟨211953595336994375720667251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141302396891329583813778167 211953595336994375720667251)
        ·
          refine ⟨317930393005491563581000877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211953595336994375720667251 317930393005491563581000877)
          ·
            refine ⟨119223897377059336342875329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317930393005491563581000877 119223897377059336342875329)
            ·
              refine ⟨89417923032794502257156497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119223897377059336342875329 89417923032794502257156497)
              ·
                refine ⟨67063442274595876692867373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89417923032794502257156497 67063442274595876692867373)
                ·
                  refine ⟨25148790852973453759825265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67063442274595876692867373 25148790852973453759825265)
                  ·
                    refine ⟨18861593139730090319868949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25148790852973453759825265 18861593139730090319868949)
                    ·
                      refine ⟨884137178424847983743857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18861593139730090319868949 884137178424847983743857)
                      ·
                        rfl

theorem cell23_1721851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 6].length) (baseStart_1721851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721851 prefixEnd_1721851 := by exact prefixLift 1721851
  have htrace : WordTrace (prefixWord ++ tailWord_1721851) baseStart_1721851 baseEnd_1721851 := by
    simpa [prefixWord, tailWord_1721851, baseEnd_1721851] using wordTrace_append hprefix tailTrace_1721851
  have hstable : (prefixWord ++ tailWord_1721851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721851).length < 2 ^ (prefixWord ++ tailWord_1721851).sum := by decide
  have hdescent : baseEnd_1721851 < baseStart_1721851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721852 : List Nat := [2, 2, 2, 1, 2, 1, 5, 3, 1, 4]
def baseStart_1721852 : Nat := 118140960795 + 1721852 * 2 ^ 59
def prefixEnd_1721852 : Nat := 4983230072969 + 3 ^ 40 * 1721852 * 2
def baseEnd_1721852 : Nat := 294712563968500826610451

theorem tailTrace_1721852 : CollatzResearch.WordTrace tailWord_1721852 prefixEnd_1721852 294712563968500826610451 := by
  unfold tailWord_1721852
  simp only [CollatzResearch.WordTrace]
  refine ⟨31400550879015873877343905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41867401172021165169791873 31400550879015873877343905)
  ·
    refine ⟨23550413159261905408007929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31400550879015873877343905 23550413159261905408007929)
    ·
      refine ⟨17662809869446429056005947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23550413159261905408007929 17662809869446429056005947)
      ·
        refine ⟨26494214804169643584008921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17662809869446429056005947 26494214804169643584008921)
        ·
          refine ⟨19870661103127232688006691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26494214804169643584008921 19870661103127232688006691)
          ·
            refine ⟨29805991654690849032010037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19870661103127232688006691 29805991654690849032010037)
            ·
              refine ⟨2794311717627267096750941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29805991654690849032010037 2794311717627267096750941)
              ·
                refine ⟨1047866894110225161281603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2794311717627267096750941 1047866894110225161281603)
                ·
                  refine ⟨1571800341165337741922405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1047866894110225161281603 1571800341165337741922405)
                  ·
                    refine ⟨294712563968500826610451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1571800341165337741922405 294712563968500826610451)
                    ·
                      rfl

theorem cell23_1721852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_1721852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721852 prefixEnd_1721852 := by exact prefixLift 1721852
  have htrace : WordTrace (prefixWord ++ tailWord_1721852) baseStart_1721852 baseEnd_1721852 := by
    simpa [prefixWord, tailWord_1721852, baseEnd_1721852] using wordTrace_append hprefix tailTrace_1721852
  have hstable : (prefixWord ++ tailWord_1721852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721852).length < 2 ^ (prefixWord ++ tailWord_1721852).sum := by decide
  have hdescent : baseEnd_1721852 < baseStart_1721852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721912 : List Nat := [2, 1, 2, 1, 4, 3, 3, 1, 1, 5]
def baseStart_1721912 : Nat := 118140960795 + 1721912 * 2 ^ 59
def prefixEnd_1721912 : Nat := 4983230072969 + 3 ^ 40 * 1721912 * 2
def baseEnd_1721912 : Nat := 294722833581590748360359

theorem tailTrace_1721912 : CollatzResearch.WordTrace tailWord_1721912 prefixEnd_1721912 294722833581590748360359 := by
  unfold tailWord_1721912
  simp only [CollatzResearch.WordTrace]
  refine ⟨31401645068907189000935995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41868860091876252001247993 31401645068907189000935995)
  ·
    refine ⟨47102467603360783501403993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31401645068907189000935995 47102467603360783501403993)
    ·
      refine ⟨35326850702520587626052995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47102467603360783501403993 35326850702520587626052995)
      ·
        refine ⟨52990276053780881439079493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35326850702520587626052995 52990276053780881439079493)
        ·
          refine ⟨9935676760083915269827405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52990276053780881439079493 9935676760083915269827405)
          ·
            refine ⟨3725878785031468226185277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9935676760083915269827405 3725878785031468226185277)
            ·
              refine ⟨1397204544386800584819479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3725878785031468226185277 1397204544386800584819479)
              ·
                refine ⟨2095806816580200877229219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1397204544386800584819479 2095806816580200877229219)
                ·
                  refine ⟨3143710224870301315843829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2095806816580200877229219 3143710224870301315843829)
                  ·
                    refine ⟨294722833581590748360359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3143710224870301315843829 294722833581590748360359)
                    ·
                      rfl

theorem cell23_1721912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 1, 5].length) (baseStart_1721912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721912 prefixEnd_1721912 := by exact prefixLift 1721912
  have htrace : WordTrace (prefixWord ++ tailWord_1721912) baseStart_1721912 baseEnd_1721912 := by
    simpa [prefixWord, tailWord_1721912, baseEnd_1721912] using wordTrace_append hprefix tailTrace_1721912
  have hstable : (prefixWord ++ tailWord_1721912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721912).length < 2 ^ (prefixWord ++ tailWord_1721912).sum := by decide
  have hdescent : baseEnd_1721912 < baseStart_1721912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721955 : List Nat := [1, 1, 1, 5, 1, 4, 3, 7]
def baseStart_1721955 : Nat := 118140960795 + 1721955 * 2 ^ 59
def prefixEnd_1721955 : Nat := 4983230072969 + 3 ^ 40 * 1721955 * 2
def baseEnd_1721955 : Nat := 32747799274552428771977

theorem tailTrace_1721955 : CollatzResearch.WordTrace tailWord_1721955 prefixEnd_1721955 32747799274552428771977 := by
  unfold tailWord_1721955
  simp only [CollatzResearch.WordTrace]
  refine ⟨62804858476658596345687319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41869905651105730897124879 62804858476658596345687319)
  ·
    refine ⟨94207287714987894518530979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62804858476658596345687319 94207287714987894518530979)
    ·
      refine ⟨141310931572481841777796469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94207287714987894518530979 141310931572481841777796469)
      ·
        refine ⟨13247899834920172666668419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141310931572481841777796469 13247899834920172666668419)
        ·
          refine ⟨19871849752380259000002629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13247899834920172666668419 19871849752380259000002629)
          ·
            refine ⟨3725971828571298562500493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19871849752380259000002629 3725971828571298562500493)
            ·
              refine ⟨1397239435714236960937685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3725971828571298562500493 1397239435714236960937685)
              ·
                refine ⟨32747799274552428771977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1397239435714236960937685 32747799274552428771977)
                ·
                  rfl

theorem cell23_1721955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 7].length) (baseStart_1721955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721955 prefixEnd_1721955 := by exact prefixLift 1721955
  have htrace : WordTrace (prefixWord ++ tailWord_1721955) baseStart_1721955 baseEnd_1721955 := by
    simpa [prefixWord, tailWord_1721955, baseEnd_1721955] using wordTrace_append hprefix tailTrace_1721955
  have hstable : (prefixWord ++ tailWord_1721955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721955).length < 2 ^ (prefixWord ++ tailWord_1721955).sum := by decide
  have hdescent : baseEnd_1721955 < baseStart_1721955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721966 : List Nat := [4, 1, 2, 2, 3, 2, 2, 1, 1, 1, 4]
def baseStart_1721966 : Nat := 118140960795 + 1721966 * 2 ^ 59
def prefixEnd_1721966 : Nat := 4983230072969 + 3 ^ 40 * 1721966 * 2
def baseEnd_1721966 : Nat := 884196228700115033805829

theorem tailTrace_1721966 : CollatzResearch.WordTrace tailWord_1721966 prefixEnd_1721966 884196228700115033805829 := by
  unfold tailWord_1721966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7850657459952343153042219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41870173119745830149558501 7850657459952343153042219)
  ·
    refine ⟨11775986189928514729563329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7850657459952343153042219 11775986189928514729563329)
    ·
      refine ⟨8831989642446386047172497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11775986189928514729563329 8831989642446386047172497)
      ·
        refine ⟨6623992231834789535379373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8831989642446386047172497 6623992231834789535379373)
        ·
          refine ⟨2483997086938046075767265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6623992231834789535379373 2483997086938046075767265)
          ·
            refine ⟨1862997815203534556825449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2483997086938046075767265 1862997815203534556825449)
            ·
              refine ⟨1397248361402650917619087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1862997815203534556825449 1397248361402650917619087)
              ·
                refine ⟨2095872542103976376428631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1397248361402650917619087 2095872542103976376428631)
                ·
                  refine ⟨3143808813155964564642947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2095872542103976376428631 3143808813155964564642947)
                  ·
                    refine ⟨4715713219733946846964421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3143808813155964564642947 4715713219733946846964421)
                    ·
                      refine ⟨884196228700115033805829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4715713219733946846964421 884196228700115033805829)
                      ·
                        rfl

theorem cell23_1721966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_1721966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721966 prefixEnd_1721966 := by exact prefixLift 1721966
  have htrace : WordTrace (prefixWord ++ tailWord_1721966) baseStart_1721966 baseEnd_1721966 := by
    simpa [prefixWord, tailWord_1721966, baseEnd_1721966] using wordTrace_append hprefix tailTrace_1721966
  have hstable : (prefixWord ++ tailWord_1721966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721966).length < 2 ^ (prefixWord ++ tailWord_1721966).sum := by decide
  have hdescent : baseEnd_1721966 < baseStart_1721966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1721978 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5]
def baseStart_1721978 : Nat := 118140960795 + 1721978 * 2 ^ 59
def prefixEnd_1721978 : Nat := 4983230072969 + 3 ^ 40 * 1721978 * 2
def baseEnd_1721978 : Nat := 884202390467968986855773

theorem tailTrace_1721978 : CollatzResearch.WordTrace tailWord_1721978 prefixEnd_1721978 884202390467968986855773 := by
  unfold tailWord_1721978
  simp only [CollatzResearch.WordTrace]
  refine ⟨15701424338893817818443647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41870464903716847515849725 15701424338893817818443647)
  ·
    refine ⟨23552136508340726727665471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15701424338893817818443647 23552136508340726727665471)
    ·
      refine ⟨35328204762511090091498207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23552136508340726727665471 35328204762511090091498207)
      ·
        refine ⟨52992307143766635137247311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35328204762511090091498207 52992307143766635137247311)
        ·
          refine ⟨79488460715649952705870967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52992307143766635137247311 79488460715649952705870967)
          ·
            refine ⟨119232691073474929058806451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79488460715649952705870967 119232691073474929058806451)
            ·
              refine ⟨178849036610212393588209677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119232691073474929058806451 178849036610212393588209677)
              ·
                refine ⟨67068388728829647595578629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178849036610212393588209677 67068388728829647595578629)
                ·
                  refine ⟨12575322886655558924170993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67068388728829647595578629 12575322886655558924170993)
                  ·
                    refine ⟨9431492164991669193128245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12575322886655558924170993 9431492164991669193128245)
                    ·
                      refine ⟨884202390467968986855773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9431492164991669193128245 884202390467968986855773)
                      ·
                        rfl

theorem cell23_1721978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_1721978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1721978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1721978 prefixEnd_1721978 := by exact prefixLift 1721978
  have htrace : WordTrace (prefixWord ++ tailWord_1721978) baseStart_1721978 baseEnd_1721978 := by
    simpa [prefixWord, tailWord_1721978, baseEnd_1721978] using wordTrace_append hprefix tailTrace_1721978
  have hstable : (prefixWord ++ tailWord_1721978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1721978).length < 2 ^ (prefixWord ++ tailWord_1721978).sum := by decide
  have hdescent : baseEnd_1721978 < baseStart_1721978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1721978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722039 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 4, 2, 2]
def baseStart_1722039 : Nat := 118140960795 + 1722039 * 2 ^ 59
def prefixEnd_1722039 : Nat := 4983230072969 + 3 ^ 40 * 1722039 * 2
def baseEnd_1722039 : Nat := 884233712787893248192993

theorem tailTrace_1722039 : CollatzResearch.WordTrace tailWord_1722039 prefixEnd_1722039 884233712787893248192993 := by
  unfold tailWord_1722039
  simp only [CollatzResearch.WordTrace]
  refine ⟨62807922208354278691745171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41871948138902852461163447 62807922208354278691745171)
  ·
    refine ⟨94211883312531418037617757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62807922208354278691745171 94211883312531418037617757)
    ·
      refine ⟨35329456242199281764106659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94211883312531418037617757 35329456242199281764106659)
      ·
        refine ⟨52994184363298922646159989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35329456242199281764106659 52994184363298922646159989)
        ·
          refine ⟨4968204784059273998077499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52994184363298922646159989 4968204784059273998077499)
          ·
            refine ⟨7452307176088910997116249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4968204784059273998077499 7452307176088910997116249)
            ·
              refine ⟨5589230382066683247837187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7452307176088910997116249 5589230382066683247837187)
              ·
                refine ⟨8383845573100024871755781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5589230382066683247837187 8383845573100024871755781)
                ·
                  refine ⟨1571971044956254663454209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8383845573100024871755781 1571971044956254663454209)
                  ·
                    refine ⟨1178978283717190997590657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1571971044956254663454209 1178978283717190997590657)
                    ·
                      refine ⟨884233712787893248192993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1178978283717190997590657 884233712787893248192993)
                      ·
                        rfl

theorem cell23_1722039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 2, 2].length) (baseStart_1722039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722039 prefixEnd_1722039 := by exact prefixLift 1722039
  have htrace : WordTrace (prefixWord ++ tailWord_1722039) baseStart_1722039 baseEnd_1722039 := by
    simpa [prefixWord, tailWord_1722039, baseEnd_1722039] using wordTrace_append hprefix tailTrace_1722039
  have hstable : (prefixWord ++ tailWord_1722039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722039).length < 2 ^ (prefixWord ++ tailWord_1722039).sum := by decide
  have hdescent : baseEnd_1722039 < baseStart_1722039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722050 : List Nat := [3, 5, 1, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_1722050 : Nat := 118140960795 + 1722050 * 2 ^ 59
def prefixEnd_1722050 : Nat := 4983230072969 + 3 ^ 40 * 1722050 * 2
def baseEnd_1722050 : Nat := 884239361075092705155443

theorem tailTrace_1722050 : CollatzResearch.WordTrace tailWord_1722050 prefixEnd_1722050 884239361075092705155443 := by
  unfold tailWord_1722050
  simp only [CollatzResearch.WordTrace]
  refine ⟨15702080852828606892598901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41872215607542951713597069 15702080852828606892598901)
  ·
    refine ⟨1472070079952681896181147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15702080852828606892598901 1472070079952681896181147)
    ·
      refine ⟨2208105119929022844271721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1472070079952681896181147 2208105119929022844271721)
      ·
        refine ⟨1656078839946767133203791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2208105119929022844271721 1656078839946767133203791)
        ·
          refine ⟨2484118259920150699805687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1656078839946767133203791 2484118259920150699805687)
          ·
            refine ⟨3726177389880226049708531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484118259920150699805687 3726177389880226049708531)
            ·
              refine ⟨5589266084820339074562797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3726177389880226049708531 5589266084820339074562797)
              ·
                refine ⟨2095974781807627152961049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5589266084820339074562797 2095974781807627152961049)
                ·
                  refine ⟨1571981086355720364720787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2095974781807627152961049 1571981086355720364720787)
                  ·
                    refine ⟨2357971629533580547081181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1571981086355720364720787 2357971629533580547081181)
                    ·
                      refine ⟨884239361075092705155443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2357971629533580547081181 884239361075092705155443)
                      ·
                        rfl

theorem cell23_1722050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_1722050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722050 prefixEnd_1722050 := by exact prefixLift 1722050
  have htrace : WordTrace (prefixWord ++ tailWord_1722050) baseStart_1722050 baseEnd_1722050 := by
    simpa [prefixWord, tailWord_1722050, baseEnd_1722050] using wordTrace_append hprefix tailTrace_1722050
  have hstable : (prefixWord ++ tailWord_1722050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722050).length < 2 ^ (prefixWord ++ tailWord_1722050).sum := by decide
  have hdescent : baseEnd_1722050 < baseStart_1722050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722055 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 3]
def baseStart_1722055 : Nat := 118140960795 + 1722055 * 2 ^ 59
def prefixEnd_1722055 : Nat := 4983230072969 + 3 ^ 40 * 1722055 * 2
def baseEnd_1722055 : Nat := 884241928478365185592919

theorem tailTrace_1722055 : CollatzResearch.WordTrace tailWord_1722055 prefixEnd_1722055 884241928478365185592919 := by
  unfold tailWord_1722055
  simp only [CollatzResearch.WordTrace]
  refine ⟨62808505776296313424327619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41872337184197542282885079 62808505776296313424327619)
  ·
    refine ⟨94212758664444470136491429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62808505776296313424327619 94212758664444470136491429)
    ·
      refine ⟨17664892249583338150592143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94212758664444470136491429 17664892249583338150592143)
      ·
        refine ⟨26497338374375007225888215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17664892249583338150592143 26497338374375007225888215)
        ·
          refine ⟨39746007561562510838832323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26497338374375007225888215 39746007561562510838832323)
          ·
            refine ⟨59619011342343766258248485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39746007561562510838832323 59619011342343766258248485)
            ·
              refine ⟨11178564626689456173421591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59619011342343766258248485 11178564626689456173421591)
              ·
                refine ⟨16767846940034184260132387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11178564626689456173421591 16767846940034184260132387)
                ·
                  refine ⟨25151770410051276390198581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16767846940034184260132387 25151770410051276390198581)
                  ·
                    refine ⟨2357978475942307161581117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25151770410051276390198581 2357978475942307161581117)
                    ·
                      refine ⟨884241928478365185592919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2357978475942307161581117 884241928478365185592919)
                      ·
                        rfl

theorem cell23_1722055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_1722055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722055 prefixEnd_1722055 := by exact prefixLift 1722055
  have htrace : WordTrace (prefixWord ++ tailWord_1722055) baseStart_1722055 baseEnd_1722055 := by
    simpa [prefixWord, tailWord_1722055, baseEnd_1722055] using wordTrace_append hprefix tailTrace_1722055
  have hstable : (prefixWord ++ tailWord_1722055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722055).length < 2 ^ (prefixWord ++ tailWord_1722055).sum := by decide
  have hdescent : baseEnd_1722055 < baseStart_1722055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722085 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 3, 2, 5]
def baseStart_1722085 : Nat := 118140960795 + 1722085 * 2 ^ 59
def prefixEnd_1722085 : Nat := 4983230072969 + 3 ^ 40 * 1722085 * 2
def baseEnd_1722085 : Nat := 884257332898000068217781

theorem tailTrace_1722085 : CollatzResearch.WordTrace tailWord_1722085 prefixEnd_1722085 884257332898000068217781 := by
  unfold tailWord_1722085
  simp only [CollatzResearch.WordTrace]
  refine ⟨62809599966187628547919709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41873066644125085698613139 62809599966187628547919709)
  ·
    refine ⟨23553599987320360705469891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62809599966187628547919709 23553599987320360705469891)
    ·
      refine ⟨35330399980980541058204837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23553599987320360705469891 35330399980980541058204837)
      ·
        refine ⟨6624449996433851448413407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35330399980980541058204837 6624449996433851448413407)
        ·
          refine ⟨9936674994650777172620111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6624449996433851448413407 9936674994650777172620111)
          ·
            refine ⟨14905012491976165758930167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9936674994650777172620111 14905012491976165758930167)
            ·
              refine ⟨22357518737964248638395251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14905012491976165758930167 22357518737964248638395251)
              ·
                refine ⟨33536278106946372957592877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22357518737964248638395251 33536278106946372957592877)
                ·
                  refine ⟨12576104290104889859097329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33536278106946372957592877 12576104290104889859097329)
                  ·
                    refine ⟨9432078217578667394322997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12576104290104889859097329 9432078217578667394322997)
                    ·
                      refine ⟨884257332898000068217781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9432078217578667394322997 884257332898000068217781)
                      ·
                        rfl

theorem cell23_1722085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_1722085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722085 prefixEnd_1722085 := by exact prefixLift 1722085
  have htrace : WordTrace (prefixWord ++ tailWord_1722085) baseStart_1722085 baseEnd_1722085 := by
    simpa [prefixWord, tailWord_1722085, baseEnd_1722085] using wordTrace_append hprefix tailTrace_1722085
  have hstable : (prefixWord ++ tailWord_1722085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722085).length < 2 ^ (prefixWord ++ tailWord_1722085).sum := by decide
  have hdescent : baseEnd_1722085 < baseStart_1722085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722102 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_1722102 : Nat := 118140960795 + 1722102 * 2 ^ 59
def prefixEnd_1722102 : Nat := 4983230072969 + 3 ^ 40 * 1722102 * 2
def baseEnd_1722102 : Nat := 884266062069126501705203

theorem tailTrace_1722102 : CollatzResearch.WordTrace tailWord_1722102 prefixEnd_1722102 884266062069126501705203 := by
  unfold tailWord_1722102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3925638750445377528205535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41873480004750693634192373 3925638750445377528205535)
  ·
    refine ⟨5888458125668066292308303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3925638750445377528205535 5888458125668066292308303)
    ·
      refine ⟨8832687188502099438462455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5888458125668066292308303 8832687188502099438462455)
      ·
        refine ⟨13249030782753149157693683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8832687188502099438462455 13249030782753149157693683)
        ·
          refine ⟨19873546174129723736540525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13249030782753149157693683 19873546174129723736540525)
          ·
            refine ⟨7452579815298646401202697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19873546174129723736540525 7452579815298646401202697)
            ·
              refine ⟨5589434861473984800902023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7452579815298646401202697 5589434861473984800902023)
              ·
                refine ⟨8384152292210977201353035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5589434861473984800902023 8384152292210977201353035)
                ·
                  refine ⟨12576228438316465802029553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8384152292210977201353035 12576228438316465802029553)
                  ·
                    refine ⟨9432171328737349351522165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12576228438316465802029553 9432171328737349351522165)
                    ·
                      refine ⟨884266062069126501705203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9432171328737349351522165 884266062069126501705203)
                      ·
                        rfl

theorem cell23_1722102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_1722102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722102 prefixEnd_1722102 := by exact prefixLift 1722102
  have htrace : WordTrace (prefixWord ++ tailWord_1722102) baseStart_1722102 baseEnd_1722102 := by
    simpa [prefixWord, tailWord_1722102, baseEnd_1722102] using wordTrace_append hprefix tailTrace_1722102
  have hstable : (prefixWord ++ tailWord_1722102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722102).length < 2 ^ (prefixWord ++ tailWord_1722102).sum := by decide
  have hdescent : baseEnd_1722102 < baseStart_1722102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722112 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 2, 4, 2]
def baseStart_1722112 : Nat := 118140960795 + 1722112 * 2 ^ 59
def prefixEnd_1722112 : Nat := 4983230072969 + 3 ^ 40 * 1722112 * 2
def baseEnd_1722112 : Nat := 884271196875671462580157

theorem tailTrace_1722112 : CollatzResearch.WordTrace tailWord_1722112 prefixEnd_1722112 884271196875671462580157 := by
  unfold tailWord_1722112
  simp only [CollatzResearch.WordTrace]
  refine ⟨31405292368544906079576295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41873723158059874772768393 31405292368544906079576295)
  ·
    refine ⟨47107938552817359119364443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31405292368544906079576295 47107938552817359119364443)
    ·
      refine ⟨70661907829226038679046665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47107938552817359119364443 70661907829226038679046665)
      ·
        refine ⟨52996430871919529009284999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70661907829226038679046665 52996430871919529009284999)
        ·
          refine ⟨79494646307879293513927499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52996430871919529009284999 79494646307879293513927499)
          ·
            refine ⟨119241969461818940270891249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79494646307879293513927499 119241969461818940270891249)
            ·
              refine ⟨89431477096364205203168437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119241969461818940270891249 89431477096364205203168437)
              ·
                refine ⟨8384200977784144237797041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89431477096364205203168437 8384200977784144237797041)
                ·
                  refine ⟨6288150733338108178347781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8384200977784144237797041 6288150733338108178347781)
                  ·
                    refine ⟨1179028262500895283440209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6288150733338108178347781 1179028262500895283440209)
                    ·
                      refine ⟨884271196875671462580157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1179028262500895283440209 884271196875671462580157)
                      ·
                        rfl

theorem cell23_1722112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 2, 4, 2].length) (baseStart_1722112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722112 prefixEnd_1722112 := by exact prefixLift 1722112
  have htrace : WordTrace (prefixWord ++ tailWord_1722112) baseStart_1722112 baseEnd_1722112 := by
    simpa [prefixWord, tailWord_1722112, baseEnd_1722112] using wordTrace_append hprefix tailTrace_1722112
  have hstable : (prefixWord ++ tailWord_1722112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722112).length < 2 ^ (prefixWord ++ tailWord_1722112).sum := by decide
  have hdescent : baseEnd_1722112 < baseStart_1722112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722122 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 5, 4]
def baseStart_1722122 : Nat := 118140960795 + 1722122 * 2 ^ 59
def prefixEnd_1722122 : Nat := 4983230072969 + 3 ^ 40 * 1722122 * 2
def baseEnd_1722122 : Nat := 294758777227405474485037

theorem tailTrace_1722122 : CollatzResearch.WordTrace tailWord_1722122 prefixEnd_1722122 294758777227405474485037 := by
  unfold tailWord_1722122
  simp only [CollatzResearch.WordTrace]
  refine ⟨15702737366763395966754155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41873966311369055911344413 15702737366763395966754155)
  ·
    refine ⟨23554106050145093950131233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15702737366763395966754155 23554106050145093950131233)
    ·
      refine ⟨17665579537608820462598425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23554106050145093950131233 17665579537608820462598425)
      ·
        refine ⟨13249184653206615346948819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17665579537608820462598425 13249184653206615346948819)
        ·
          refine ⟨19873776979809923020423229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13249184653206615346948819 19873776979809923020423229)
          ·
            refine ⟨7452666367428721132658711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19873776979809923020423229 7452666367428721132658711)
            ·
              refine ⟨11178999551143081698988067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7452666367428721132658711 11178999551143081698988067)
              ·
                refine ⟨16768499326714622548482101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11178999551143081698988067 16768499326714622548482101)
                ·
                  refine ⟨1572046811879495863920197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16768499326714622548482101 1572046811879495863920197)
                  ·
                    refine ⟨294758777227405474485037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1572046811879495863920197 294758777227405474485037)
                    ·
                      rfl

theorem cell23_1722122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_1722122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722122 prefixEnd_1722122 := by exact prefixLift 1722122
  have htrace : WordTrace (prefixWord ++ tailWord_1722122) baseStart_1722122 baseEnd_1722122 := by
    simpa [prefixWord, tailWord_1722122, baseEnd_1722122] using wordTrace_append hprefix tailTrace_1722122
  have hstable : (prefixWord ++ tailWord_1722122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722122).length < 2 ^ (prefixWord ++ tailWord_1722122).sum := by decide
  have hdescent : baseEnd_1722122 < baseStart_1722122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722152 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 8]
def baseStart_1722152 : Nat := 118140960795 + 1722152 * 2 ^ 59
def prefixEnd_1722152 : Nat := 4983230072969 + 3 ^ 40 * 1722152 * 2
def baseEnd_1722152 : Nat := 98254637344650145119997

theorem tailTrace_1722152 : CollatzResearch.WordTrace tailWord_1722152 prefixEnd_1722152 98254637344650145119997 := by
  unfold tailWord_1722152
  simp only [CollatzResearch.WordTrace]
  refine ⟨31406021828472449495304355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41874695771296599327072473 31406021828472449495304355)
  ·
    refine ⟨47109032742708674242956533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31406021828472449495304355 47109032742708674242956533)
    ·
      refine ⟨4416471819628938210277175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47109032742708674242956533 4416471819628938210277175)
      ·
        refine ⟨6624707729443407315415763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4416471819628938210277175 6624707729443407315415763)
        ·
          refine ⟨9937061594165110973123645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6624707729443407315415763 9937061594165110973123645)
          ·
            refine ⟨3726398097811916614921367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9937061594165110973123645 3726398097811916614921367)
            ·
              refine ⟨5589597146717874922382051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3726398097811916614921367 5589597146717874922382051)
              ·
                refine ⟨8384395720076812383573077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5589597146717874922382051 8384395720076812383573077)
                ·
                  refine ⟨98254637344650145119997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8384395720076812383573077 98254637344650145119997)
                  ·
                    rfl

theorem cell23_1722152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 8].length) (baseStart_1722152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722152 prefixEnd_1722152 := by exact prefixLift 1722152
  have htrace : WordTrace (prefixWord ++ tailWord_1722152) baseStart_1722152 baseEnd_1722152 := by
    simpa [prefixWord, tailWord_1722152, baseEnd_1722152] using wordTrace_append hprefix tailTrace_1722152
  have hstable : (prefixWord ++ tailWord_1722152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722152).length < 2 ^ (prefixWord ++ tailWord_1722152).sum := by decide
  have hdescent : baseEnd_1722152 < baseStart_1722152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722179 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 3, 1, 3]
def baseStart_1722179 : Nat := 118140960795 + 1722179 * 2 ^ 59
def prefixEnd_1722179 : Nat := 4983230072969 + 3 ^ 40 * 1722179 * 2
def baseEnd_1722179 : Nat := 884305600079522700442349

theorem tailTrace_1722179 : CollatzResearch.WordTrace tailWord_1722179 prefixEnd_1722179 884305600079522700442349 := by
  unfold tailWord_1722179
  simp only [CollatzResearch.WordTrace]
  refine ⟨62813028427847082601841591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41875352285231388401227727 62813028427847082601841591)
  ·
    refine ⟨94219542641770623902762387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62813028427847082601841591 94219542641770623902762387)
    ·
      refine ⟨141329313962655935854143581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94219542641770623902762387 141329313962655935854143581)
      ·
        refine ⟨52998492735995975945303843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141329313962655935854143581 52998492735995975945303843)
        ·
          refine ⟨79497739103993963917955765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52998492735995975945303843 79497739103993963917955765)
          ·
            refine ⟨7452913040999434117308353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79497739103993963917955765 7452913040999434117308353)
            ·
              refine ⟨5589684780749575587981265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7452913040999434117308353 5589684780749575587981265)
              ·
                refine ⟨4192263585562181690985949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5589684780749575587981265 4192263585562181690985949)
                ·
                  refine ⟨1572098844585818134119731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4192263585562181690985949 1572098844585818134119731)
                  ·
                    refine ⟨2358148266878727201179597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1572098844585818134119731 2358148266878727201179597)
                    ·
                      refine ⟨884305600079522700442349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2358148266878727201179597 884305600079522700442349)
                      ·
                        rfl

theorem cell23_1722179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 1, 3].length) (baseStart_1722179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722179 prefixEnd_1722179 := by exact prefixLift 1722179
  have htrace : WordTrace (prefixWord ++ tailWord_1722179) baseStart_1722179 baseEnd_1722179 := by
    simpa [prefixWord, tailWord_1722179, baseEnd_1722179] using wordTrace_append hprefix tailTrace_1722179
  have hstable : (prefixWord ++ tailWord_1722179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722179).length < 2 ^ (prefixWord ++ tailWord_1722179).sum := by decide
  have hdescent : baseEnd_1722179 < baseStart_1722179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722264 : List Nat := [2, 1, 2, 6, 2, 1, 2, 2, 1, 1, 3]
def baseStart_1722264 : Nat := 118140960795 + 1722264 * 2 ^ 59
def prefixEnd_1722264 : Nat := 4983230072969 + 3 ^ 40 * 1722264 * 2
def baseEnd_1722264 : Nat := 884349245935154867879459

theorem tailTrace_1722264 : CollatzResearch.WordTrace tailWord_1722264 prefixEnd_1722264 884349245935154867879459 := by
  unfold tailWord_1722264
  simp only [CollatzResearch.WordTrace]
  refine ⟨31408064316269571059342923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41877419088359428079123897 31408064316269571059342923)
  ·
    refine ⟨47112096474404356589014385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31408064316269571059342923 47112096474404356589014385)
    ·
      refine ⟨35334072355803267441760789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47112096474404356589014385 35334072355803267441760789)
      ·
        refine ⟨1656284641678278161332537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35334072355803267441760789 1656284641678278161332537)
        ·
          refine ⟨1242213481258708620999403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1656284641678278161332537 1242213481258708620999403)
          ·
            refine ⟨1863320221888062931499105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1242213481258708620999403 1863320221888062931499105)
            ·
              refine ⟨1397490166416047198624329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1863320221888062931499105 1397490166416047198624329)
              ·
                refine ⟨1048117624812035398968247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1397490166416047198624329 1048117624812035398968247)
                ·
                  refine ⟨1572176437218053098452371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1048117624812035398968247 1572176437218053098452371)
                  ·
                    refine ⟨2358264655827079647678557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1572176437218053098452371 2358264655827079647678557)
                    ·
                      refine ⟨884349245935154867879459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2358264655827079647678557 884349245935154867879459)
                      ·
                        rfl

theorem cell23_1722264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_1722264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722264 prefixEnd_1722264 := by exact prefixLift 1722264
  have htrace : WordTrace (prefixWord ++ tailWord_1722264) baseStart_1722264 baseEnd_1722264 := by
    simpa [prefixWord, tailWord_1722264, baseEnd_1722264] using wordTrace_append hprefix tailTrace_1722264
  have hstable : (prefixWord ++ tailWord_1722264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722264).length < 2 ^ (prefixWord ++ tailWord_1722264).sum := by decide
  have hdescent : baseEnd_1722264 < baseStart_1722264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722296 : List Nat := [2, 1, 2, 1, 2, 3, 2, 4, 1, 3, 2]
def baseStart_1722296 : Nat := 118140960795 + 1722296 * 2 ^ 59
def prefixEnd_1722296 : Nat := 4983230072969 + 3 ^ 40 * 1722296 * 2
def baseEnd_1722296 : Nat := 884365677316098742679311

theorem tailTrace_1722296 : CollatzResearch.WordTrace tailWord_1722296 prefixEnd_1722296 884365677316098742679311 := by
  unfold tailWord_1722296
  simp only [CollatzResearch.WordTrace]
  refine ⟨31408647884211605791925371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41878197178948807722567161 31408647884211605791925371)
  ·
    refine ⟨47112971826317408687888057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31408647884211605791925371 47112971826317408687888057)
    ·
      refine ⟨35334728869738056515916043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47112971826317408687888057 35334728869738056515916043)
      ·
        refine ⟨53002093304607084773874065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35334728869738056515916043 53002093304607084773874065)
        ·
          refine ⟨39751569978455313580405549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53002093304607084773874065 39751569978455313580405549)
          ·
            refine ⟨14906838741920742592652081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39751569978455313580405549 14906838741920742592652081)
            ·
              refine ⟨11180129056440556944489061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14906838741920742592652081 11180129056440556944489061)
              ·
                refine ⟨2096274198082604427091699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11180129056440556944489061 2096274198082604427091699)
                ·
                  refine ⟨3144411297123906640637549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2096274198082604427091699 3144411297123906640637549)
                  ·
                    refine ⟨1179154236421464990239081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3144411297123906640637549 1179154236421464990239081)
                    ·
                      refine ⟨884365677316098742679311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1179154236421464990239081 884365677316098742679311)
                      ·
                        rfl

theorem cell23_1722296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 1, 3, 2].length) (baseStart_1722296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722296 prefixEnd_1722296 := by exact prefixLift 1722296
  have htrace : WordTrace (prefixWord ++ tailWord_1722296) baseStart_1722296 baseEnd_1722296 := by
    simpa [prefixWord, tailWord_1722296, baseEnd_1722296] using wordTrace_append hprefix tailTrace_1722296
  have hstable : (prefixWord ++ tailWord_1722296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722296).length < 2 ^ (prefixWord ++ tailWord_1722296).sum := by decide
  have hdescent : baseEnd_1722296 < baseStart_1722296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722309 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 3, 4, 2]
def baseStart_1722309 : Nat := 118140960795 + 1722309 * 2 ^ 59
def prefixEnd_1722309 : Nat := 4983230072969 + 3 ^ 40 * 1722309 * 2
def baseEnd_1722309 : Nat := 884372352564607191816751

theorem tailTrace_1722309 : CollatzResearch.WordTrace tailWord_1722309 prefixEnd_1722309 884372352564607191816751 := by
  unfold tailWord_1722309
  simp only [CollatzResearch.WordTrace]
  refine ⟨62817769917376114804073981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41878513278250743202715987 62817769917376114804073981)
  ·
    refine ⟨23556663719016043051527743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62817769917376114804073981 23556663719016043051527743)
    ·
      refine ⟨35334995578524064577291615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23556663719016043051527743 35334995578524064577291615)
      ·
        refine ⟨53002493367786096865937423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35334995578524064577291615 53002493367786096865937423)
        ·
          refine ⟨79503740051679145298906135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53002493367786096865937423 79503740051679145298906135)
          ·
            refine ⟨119255610077518717948359203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79503740051679145298906135 119255610077518717948359203)
            ·
              refine ⟨178883415116278076922538805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119255610077518717948359203 178883415116278076922538805)
              ·
                refine ⟨16770320167151069711488013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178883415116278076922538805 16770320167151069711488013)
                ·
                  refine ⟨6288870062681651141808005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16770320167151069711488013 6288870062681651141808005)
                  ·
                    refine ⟨1179163136752809589089001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6288870062681651141808005 1179163136752809589089001)
                    ·
                      refine ⟨884372352564607191816751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1179163136752809589089001 884372352564607191816751)
                      ·
                        rfl

theorem cell23_1722309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 4, 2].length) (baseStart_1722309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722309 prefixEnd_1722309 := by exact prefixLift 1722309
  have htrace : WordTrace (prefixWord ++ tailWord_1722309) baseStart_1722309 baseEnd_1722309 := by
    simpa [prefixWord, tailWord_1722309, baseEnd_1722309] using wordTrace_append hprefix tailTrace_1722309
  have hstable : (prefixWord ++ tailWord_1722309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722309).length < 2 ^ (prefixWord ++ tailWord_1722309).sum := by decide
  have hdescent : baseEnd_1722309 < baseStart_1722309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722339 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1722339 : Nat := 118140960795 + 1722339 * 2 ^ 59
def prefixEnd_1722339 : Nat := 4983230072969 + 3 ^ 40 * 1722339 * 2
def baseEnd_1722339 : Nat := 884387756984242074441613

theorem tailTrace_1722339 : CollatzResearch.WordTrace tailWord_1722339 prefixEnd_1722339 884387756984242074441613 := by
  unfold tailWord_1722339
  simp only [CollatzResearch.WordTrace]
  refine ⟨62818864107267429927666071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41879242738178286618444047 62818864107267429927666071)
  ·
    refine ⟨94228296160901144891499107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62818864107267429927666071 94228296160901144891499107)
    ·
      refine ⟨141342444241351717337248661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94228296160901144891499107 141342444241351717337248661)
      ·
        refine ⟨6625427073813361750183531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 141342444241351717337248661 6625427073813361750183531)
        ·
          refine ⟨9938140610720042625275297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6625427073813361750183531 9938140610720042625275297)
          ·
            refine ⟨7453605458040031968956473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9938140610720042625275297 7453605458040031968956473)
            ·
              refine ⟨5590204093530023976717355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7453605458040031968956473 5590204093530023976717355)
              ·
                refine ⟨8385306140295035965076033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5590204093530023976717355 8385306140295035965076033)
                ·
                  refine ⟨6288979605221276973807025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8385306140295035965076033 6288979605221276973807025)
                  ·
                    refine ⟨4716734703915957730355269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6288979605221276973807025 4716734703915957730355269)
                    ·
                      refine ⟨884387756984242074441613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4716734703915957730355269 884387756984242074441613)
                      ·
                        rfl

theorem cell23_1722339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1722339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722339 prefixEnd_1722339 := by exact prefixLift 1722339
  have htrace : WordTrace (prefixWord ++ tailWord_1722339) baseStart_1722339 baseEnd_1722339 := by
    simpa [prefixWord, tailWord_1722339, baseEnd_1722339] using wordTrace_append hprefix tailTrace_1722339
  have hstable : (prefixWord ++ tailWord_1722339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722339).length < 2 ^ (prefixWord ++ tailWord_1722339).sum := by decide
  have hdescent : baseEnd_1722339 < baseStart_1722339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722379 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 2, 5]
def baseStart_1722379 : Nat := 118140960795 + 1722379 * 2 ^ 59
def prefixEnd_1722379 : Nat := 4983230072969 + 3 ^ 40 * 1722379 * 2
def baseEnd_1722379 : Nat := 294802765403473972647143

theorem tailTrace_1722379 : CollatzResearch.WordTrace tailWord_1722379 prefixEnd_1722379 294802765403473972647143 := by
  unfold tailWord_1722379
  simp only [CollatzResearch.WordTrace]
  refine ⟨62820323027122516759122191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41880215351415011172748127 62820323027122516759122191)
  ·
    refine ⟨94230484540683775138683287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62820323027122516759122191 94230484540683775138683287)
    ·
      refine ⟨141345726811025662708024931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94230484540683775138683287 141345726811025662708024931)
      ·
        refine ⟨212018590216538494062037397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141345726811025662708024931 212018590216538494062037397)
        ·
          refine ⟨9938371416400241909158003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 212018590216538494062037397 9938371416400241909158003)
          ·
            refine ⟨14907557124600362863737005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9938371416400241909158003 14907557124600362863737005)
            ·
              refine ⟨5590333921725136073901377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14907557124600362863737005 5590333921725136073901377)
              ·
                refine ⟨4192750441293852055426033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5590333921725136073901377 4192750441293852055426033)
                ·
                  refine ⟨3144562830970389041569525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4192750441293852055426033 3144562830970389041569525)
                  ·
                    refine ⟨294802765403473972647143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3144562830970389041569525 294802765403473972647143)
                    ·
                      rfl

theorem cell23_1722379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 5].length) (baseStart_1722379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722379 prefixEnd_1722379 := by exact prefixLift 1722379
  have htrace : WordTrace (prefixWord ++ tailWord_1722379) baseStart_1722379 baseEnd_1722379 := by
    simpa [prefixWord, tailWord_1722379, baseEnd_1722379] using wordTrace_append hprefix tailTrace_1722379
  have hstable : (prefixWord ++ tailWord_1722379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722379).length < 2 ^ (prefixWord ++ tailWord_1722379).sum := by decide
  have hdescent : baseEnd_1722379 < baseStart_1722379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722399 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 4]
def baseStart_1722399 : Nat := 118140960795 + 1722399 * 2 ^ 59
def prefixEnd_1722399 : Nat := 4983230072969 + 3 ^ 40 * 1722399 * 2
def baseEnd_1722399 : Nat := 884418565823511839691337

theorem tailTrace_1722399 : CollatzResearch.WordTrace tailWord_1722399 prefixEnd_1722399 884418565823511839691337 := by
  unfold tailWord_1722399
  simp only [CollatzResearch.WordTrace]
  refine ⟨62821052487050060174850251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41880701658033373449900167 62821052487050060174850251)
  ·
    refine ⟨94231578730575090262275377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62821052487050060174850251 94231578730575090262275377)
    ·
      refine ⟨70673684047931317696706533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94231578730575090262275377 70673684047931317696706533)
      ·
        refine ⟨13251315758987122068132475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70673684047931317696706533 13251315758987122068132475)
        ·
          refine ⟨19876973638480683102198713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13251315758987122068132475 19876973638480683102198713)
          ·
            refine ⟨14907730228860512326649035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19876973638480683102198713 14907730228860512326649035)
            ·
              refine ⟨22361595343290768489973553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14907730228860512326649035 22361595343290768489973553)
              ·
                refine ⟨16771196507468076367480165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22361595343290768489973553 16771196507468076367480165)
                ·
                  refine ⟨3144599345150264318902531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16771196507468076367480165 3144599345150264318902531)
                  ·
                    refine ⟨4716899017725396478353797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3144599345150264318902531 4716899017725396478353797)
                    ·
                      refine ⟨884418565823511839691337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4716899017725396478353797 884418565823511839691337)
                      ·
                        rfl

theorem cell23_1722399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_1722399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722399 prefixEnd_1722399 := by exact prefixLift 1722399
  have htrace : WordTrace (prefixWord ++ tailWord_1722399) baseStart_1722399 baseEnd_1722399 := by
    simpa [prefixWord, tailWord_1722399, baseEnd_1722399] using wordTrace_append hprefix tailTrace_1722399
  have hstable : (prefixWord ++ tailWord_1722399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722399).length < 2 ^ (prefixWord ++ tailWord_1722399).sum := by decide
  have hdescent : baseEnd_1722399 < baseStart_1722399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722416 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 4]
def baseStart_1722416 : Nat := 118140960795 + 1722416 * 2 ^ 59
def prefixEnd_1722416 : Nat := 4983230072969 + 3 ^ 40 * 1722416 * 2
def baseEnd_1722416 : Nat := 884427294994638273178759

theorem tailTrace_1722416 : CollatzResearch.WordTrace tailWord_1722416 prefixEnd_1722416 884427294994638273178759 := by
  unfold tailWord_1722416
  simp only [CollatzResearch.WordTrace]
  refine ⟨31410836263994236039109551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41881115018658981385479401 31410836263994236039109551)
  ·
    refine ⟨47116254395991354058664327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31410836263994236039109551 47116254395991354058664327)
    ·
      refine ⟨70674381593987031087996491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47116254395991354058664327 70674381593987031087996491)
      ·
        refine ⟨106011572390980546631994737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70674381593987031087996491 106011572390980546631994737)
        ·
          refine ⟨79508679293235409973996053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106011572390980546631994737 79508679293235409973996053)
          ·
            refine ⟨3726969341870409842531065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79508679293235409973996053 3726969341870409842531065)
            ·
              refine ⟨2795227006402807381898299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3726969341870409842531065 2795227006402807381898299)
              ·
                refine ⟨4192840509604211072847449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2795227006402807381898299 4192840509604211072847449)
                ·
                  refine ⟨3144630382203158304635587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4192840509604211072847449 3144630382203158304635587)
                  ·
                    refine ⟨4716945573304737456953381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3144630382203158304635587 4716945573304737456953381)
                    ·
                      refine ⟨884427294994638273178759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4716945573304737456953381 884427294994638273178759)
                      ·
                        rfl

theorem cell23_1722416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 4].length) (baseStart_1722416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722416 prefixEnd_1722416 := by exact prefixLift 1722416
  have htrace : WordTrace (prefixWord ++ tailWord_1722416) baseStart_1722416 baseEnd_1722416 := by
    simpa [prefixWord, tailWord_1722416, baseEnd_1722416] using wordTrace_append hprefix tailTrace_1722416
  have hstable : (prefixWord ++ tailWord_1722416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722416).length < 2 ^ (prefixWord ++ tailWord_1722416).sum := by decide
  have hdescent : baseEnd_1722416 < baseStart_1722416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722419 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 3]
def baseStart_1722419 : Nat := 118140960795 + 1722419 * 2 ^ 59
def prefixEnd_1722419 : Nat := 4983230072969 + 3 ^ 40 * 1722419 * 2
def baseEnd_1722419 : Nat := 884428835436601761441245

theorem tailTrace_1722419 : CollatzResearch.WordTrace tailWord_1722419 prefixEnd_1722419 884428835436601761441245 := by
  unfold tailWord_1722419
  simp only [CollatzResearch.WordTrace]
  refine ⟨62821781946977603590578311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41881187964651735727052207 62821781946977603590578311)
  ·
    refine ⟨94232672920466405385867467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62821781946977603590578311 94232672920466405385867467)
    ·
      refine ⟨141349009380699608078801201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94232672920466405385867467 141349009380699608078801201)
      ·
        refine ⟨106011757035524706059100901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141349009380699608078801201 106011757035524706059100901)
        ·
          refine ⟨19877204444160882386081419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106011757035524706059100901 19877204444160882386081419)
          ·
            refine ⟨29815806666241323579122129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19877204444160882386081419 29815806666241323579122129)
            ·
              refine ⟨22361854999680992684341597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29815806666241323579122129 22361854999680992684341597)
              ·
                refine ⟨8385695624880372256628099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22361854999680992684341597 8385695624880372256628099)
                ·
                  refine ⟨12578543437320558384942149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8385695624880372256628099 12578543437320558384942149)
                  ·
                    refine ⟨2358476894497604697176653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12578543437320558384942149 2358476894497604697176653)
                    ·
                      refine ⟨884428835436601761441245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2358476894497604697176653 884428835436601761441245)
                      ·
                        rfl

theorem cell23_1722419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 3].length) (baseStart_1722419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722419 prefixEnd_1722419 := by exact prefixLift 1722419
  have htrace : WordTrace (prefixWord ++ tailWord_1722419) baseStart_1722419 baseEnd_1722419 := by
    simpa [prefixWord, tailWord_1722419, baseEnd_1722419] using wordTrace_append hprefix tailTrace_1722419
  have hstable : (prefixWord ++ tailWord_1722419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722419).length < 2 ^ (prefixWord ++ tailWord_1722419).sum := by decide
  have hdescent : baseEnd_1722419 < baseStart_1722419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722429 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1722429 : Nat := 118140960795 + 1722429 * 2 ^ 59
def prefixEnd_1722429 : Nat := 4983230072969 + 3 ^ 40 * 1722429 * 2
def baseEnd_1722429 : Nat := 884433970243146722316199

theorem tailTrace_1722429 : CollatzResearch.WordTrace tailWord_1722429 prefixEnd_1722429 884433970243146722316199 := by
  unfold tailWord_1722429
  simp only [CollatzResearch.WordTrace]
  refine ⟨62822146676941375298442341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41881431117960916865628227 62822146676941375298442341)
  ·
    refine ⟨11779152501926507868457939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62822146676941375298442341 11779152501926507868457939)
    ·
      refine ⟨17668728752889761802686909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11779152501926507868457939 17668728752889761802686909)
      ·
        refine ⟨6625773282333660676007591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17668728752889761802686909 6625773282333660676007591)
        ·
          refine ⟨9938659923500491014011387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6625773282333660676007591 9938659923500491014011387)
          ·
            refine ⟨14907989885250736521017081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9938659923500491014011387 14907989885250736521017081)
            ·
              refine ⟨11180992413938052390762811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14907989885250736521017081 11180992413938052390762811)
              ·
                refine ⟨16771488620907078586144217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11180992413938052390762811 16771488620907078586144217)
                ·
                  refine ⟨12578616465680308939608163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16771488620907078586144217 12578616465680308939608163)
                  ·
                    refine ⟨18867924698520463409412245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12578616465680308939608163 18867924698520463409412245)
                    ·
                      refine ⟨884433970243146722316199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18867924698520463409412245 884433970243146722316199)
                      ·
                        rfl

theorem cell23_1722429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1722429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722429 prefixEnd_1722429 := by exact prefixLift 1722429
  have htrace : WordTrace (prefixWord ++ tailWord_1722429) baseStart_1722429 baseEnd_1722429 := by
    simpa [prefixWord, tailWord_1722429, baseEnd_1722429] using wordTrace_append hprefix tailTrace_1722429
  have hstable : (prefixWord ++ tailWord_1722429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722429).length < 2 ^ (prefixWord ++ tailWord_1722429).sum := by decide
  have hdescent : baseEnd_1722429 < baseStart_1722429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722449 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 2, 5, 3]
def baseStart_1722449 : Nat := 118140960795 + 1722449 * 2 ^ 59
def prefixEnd_1722449 : Nat := 4983230072969 + 3 ^ 40 * 1722449 * 2
def baseEnd_1722449 : Nat := 884444239856236644066107

theorem tailTrace_1722449 : CollatzResearch.WordTrace tailWord_1722449 prefixEnd_1722449 884444239856236644066107 := by
  unfold tailWord_1722449
  simp only [CollatzResearch.WordTrace]
  refine ⟨62822876136868918714170401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41881917424579279142780267 62822876136868918714170401)
  ·
    refine ⟨47117157102651689035627801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62822876136868918714170401 47117157102651689035627801)
    ·
      refine ⟨35337867826988766776720851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47117157102651689035627801 35337867826988766776720851)
      ·
        refine ⟨53006801740483150165081277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35337867826988766776720851 53006801740483150165081277)
        ·
          refine ⟨19877550652681181311905479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53006801740483150165081277 19877550652681181311905479)
          ·
            refine ⟨29816325979021771967858219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19877550652681181311905479 29816325979021771967858219)
            ·
              refine ⟨44724488968532657951787329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29816325979021771967858219 44724488968532657951787329)
              ·
                refine ⟨33543366726399493463840497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44724488968532657951787329 33543366726399493463840497)
                ·
                  refine ⟨25157525044799620097880373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33543366726399493463840497 25157525044799620097880373)
                  ·
                    refine ⟨2358517972949964384176285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25157525044799620097880373 2358517972949964384176285)
                    ·
                      refine ⟨884444239856236644066107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2358517972949964384176285 884444239856236644066107)
                      ·
                        rfl

theorem cell23_1722449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_1722449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722449 prefixEnd_1722449 := by exact prefixLift 1722449
  have htrace : WordTrace (prefixWord ++ tailWord_1722449) baseStart_1722449 baseEnd_1722449 := by
    simpa [prefixWord, tailWord_1722449, baseEnd_1722449] using wordTrace_append hprefix tailTrace_1722449
  have hstable : (prefixWord ++ tailWord_1722449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722449).length < 2 ^ (prefixWord ++ tailWord_1722449).sum := by decide
  have hdescent : baseEnd_1722449 < baseStart_1722449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722500 : List Nat := [2, 3, 2, 1, 2, 1, 1, 6, 1, 1, 3]
def baseStart_1722500 : Nat := 118140960795 + 1722500 * 2 ^ 59
def prefixEnd_1722500 : Nat := 4983230072969 + 3 ^ 40 * 1722500 * 2
def baseEnd_1722500 : Nat := 884470427369615944528373

theorem tailTrace_1722500 : CollatzResearch.WordTrace tailWord_1722500 prefixEnd_1722500 884470427369615944528373 := by
  unfold tailWord_1722500
  simp only [CollatzResearch.WordTrace]
  refine ⟨31412368129842077212138477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41883157506456102949517969 31412368129842077212138477)
  ·
    refine ⟨11779638048690778954551929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31412368129842077212138477 11779638048690778954551929)
    ·
      refine ⟨8834728536518084215913947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11779638048690778954551929 8834728536518084215913947)
      ·
        refine ⟨13252092804777126323870921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8834728536518084215913947 13252092804777126323870921)
        ·
          refine ⟨9939069603582844742903191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13252092804777126323870921 9939069603582844742903191)
          ·
            refine ⟨14908604405374267114354787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9939069603582844742903191 14908604405374267114354787)
            ·
              refine ⟨22362906608061400671532181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14908604405374267114354787 22362906608061400671532181)
              ·
                refine ⟨1048261247252878156478071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22362906608061400671532181 1048261247252878156478071)
                ·
                  refine ⟨1572391870879317234717107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1048261247252878156478071 1572391870879317234717107)
                  ·
                    refine ⟨2358587806318975852075661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1572391870879317234717107 2358587806318975852075661)
                    ·
                      refine ⟨884470427369615944528373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2358587806318975852075661 884470427369615944528373)
                      ·
                        rfl

theorem cell23_1722500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_1722500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722500 prefixEnd_1722500 := by exact prefixLift 1722500
  have htrace : WordTrace (prefixWord ++ tailWord_1722500) baseStart_1722500 baseEnd_1722500 := by
    simpa [prefixWord, tailWord_1722500, baseEnd_1722500] using wordTrace_append hprefix tailTrace_1722500
  have hstable : (prefixWord ++ tailWord_1722500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722500).length < 2 ^ (prefixWord ++ tailWord_1722500).sum := by decide
  have hdescent : baseEnd_1722500 < baseStart_1722500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722523 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 3, 2, 2]
def baseStart_1722523 : Nat := 118140960795 + 1722523 * 2 ^ 59
def prefixEnd_1722523 : Nat := 4983230072969 + 3 ^ 40 * 1722523 * 2
def baseEnd_1722523 : Nat := 884482237424669354540767

theorem tailTrace_1722523 : CollatzResearch.WordTrace tailWord_1722523 prefixEnd_1722523 884482237424669354540767 := by
  unfold tailWord_1722523
  simp only [CollatzResearch.WordTrace]
  refine ⟨62825575138600829352364223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41883716759067219568242815 62825575138600829352364223)
  ·
    refine ⟨94238362707901244028546335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62825575138600829352364223 94238362707901244028546335)
    ·
      refine ⟨141357544061851866042819503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94238362707901244028546335 141357544061851866042819503)
      ·
        refine ⟨212036316092777799064229255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141357544061851866042819503 212036316092777799064229255)
        ·
          refine ⟨318054474139166698596343883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212036316092777799064229255 318054474139166698596343883)
          ·
            refine ⟨477081711208750047894515825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318054474139166698596343883 477081711208750047894515825)
            ·
              refine ⟨357811283406562535920886869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477081711208750047894515825 357811283406562535920886869)
              ·
                refine ⟨4193100977420654717822893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 357811283406562535920886869 4193100977420654717822893)
                ·
                  refine ⟨1572412866532745519183585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4193100977420654717822893 1572412866532745519183585)
                  ·
                    refine ⟨1179309649899559139387689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1572412866532745519183585 1179309649899559139387689)
                    ·
                      refine ⟨884482237424669354540767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1179309649899559139387689 884482237424669354540767)
                      ·
                        rfl

theorem cell23_1722523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 2, 2].length) (baseStart_1722523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722523 prefixEnd_1722523 := by exact prefixLift 1722523
  have htrace : WordTrace (prefixWord ++ tailWord_1722523) baseStart_1722523 baseEnd_1722523 := by
    simpa [prefixWord, tailWord_1722523, baseEnd_1722523] using wordTrace_append hprefix tailTrace_1722523
  have hstable : (prefixWord ++ tailWord_1722523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722523).length < 2 ^ (prefixWord ++ tailWord_1722523).sum := by decide
  have hdescent : baseEnd_1722523 < baseStart_1722523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722559 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 2, 7]
def baseStart_1722559 : Nat := 118140960795 + 1722559 * 2 ^ 59
def prefixEnd_1722559 : Nat := 4983230072969 + 3 ^ 40 * 1722559 * 2
def baseEnd_1722559 : Nat := 294833574242743737896867

theorem tailTrace_1722559 : CollatzResearch.WordTrace tailWord_1722559 prefixEnd_1722559 294833574242743737896867 := by
  unfold tailWord_1722559
  simp only [CollatzResearch.WordTrace]
  refine ⟨62826888166470407500674731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41884592110980271667116487 62826888166470407500674731)
  ·
    refine ⟨94240332249705611251012097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62826888166470407500674731 94240332249705611251012097)
    ·
      refine ⟨70680249187279208438259073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94240332249705611251012097 70680249187279208438259073)
      ·
        refine ⟨53010186890459406328694305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70680249187279208438259073 53010186890459406328694305)
        ·
          refine ⟨39757640167844554746520729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53010186890459406328694305 39757640167844554746520729)
          ·
            refine ⟨29818230125883416059890547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39757640167844554746520729 29818230125883416059890547)
            ·
              refine ⟨44727345188825124089835821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29818230125883416059890547 44727345188825124089835821)
              ·
                refine ⟨16772754445809421533688433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44727345188825124089835821 16772754445809421533688433)
                ·
                  refine ⟨12579565834357066150266325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16772754445809421533688433 12579565834357066150266325)
                  ·
                    refine ⟨294833574242743737896867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12579565834357066150266325 294833574242743737896867)
                    ·
                      rfl

theorem cell23_1722559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 7].length) (baseStart_1722559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722559 prefixEnd_1722559 := by exact prefixLift 1722559
  have htrace : WordTrace (prefixWord ++ tailWord_1722559) baseStart_1722559 baseEnd_1722559 := by
    simpa [prefixWord, tailWord_1722559, baseEnd_1722559] using wordTrace_append hprefix tailTrace_1722559
  have hstable : (prefixWord ++ tailWord_1722559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722559).length < 2 ^ (prefixWord ++ tailWord_1722559).sum := by decide
  have hdescent : baseEnd_1722559 < baseStart_1722559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722569 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 1, 4, 5]
def baseStart_1722569 : Nat := 118140960795 + 1722569 * 2 ^ 59
def prefixEnd_1722569 : Nat := 4983230072969 + 3 ^ 40 * 1722569 * 2
def baseEnd_1722569 : Nat := 884505857534776174565555

theorem tailTrace_1722569 : CollatzResearch.WordTrace tailWord_1722569 prefixEnd_1722569 884505857534776174565555 := by
  unfold tailWord_1722569
  simp only [CollatzResearch.WordTrace]
  refine ⟨62827252896434179208538761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41884835264289452805692507 62827252896434179208538761)
  ·
    refine ⟨47120439672325634406404071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62827252896434179208538761 47120439672325634406404071)
    ·
      refine ⟨70680659508488451609606107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47120439672325634406404071 70680659508488451609606107)
      ·
        refine ⟨106020989262732677414409161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70680659508488451609606107 106020989262732677414409161)
        ·
          refine ⟨79515741947049508060806871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106020989262732677414409161 79515741947049508060806871)
          ·
            refine ⟨119273612920574262091210307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79515741947049508060806871 119273612920574262091210307)
            ·
              refine ⟨178910419380861393136815461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119273612920574262091210307 178910419380861393136815461)
              ·
                refine ⟨33545703633911511213152899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178910419380861393136815461 33545703633911511213152899)
                ·
                  refine ⟨50318555450867266819729349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33545703633911511213152899 50318555450867266819729349)
                  ·
                    refine ⟨9434729147037612528699253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50318555450867266819729349 9434729147037612528699253)
                    ·
                      refine ⟨884505857534776174565555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9434729147037612528699253 884505857534776174565555)
                      ·
                        rfl

theorem cell23_1722569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_1722569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722569 prefixEnd_1722569 := by exact prefixLift 1722569
  have htrace : WordTrace (prefixWord ++ tailWord_1722569) baseStart_1722569 baseEnd_1722569 := by
    simpa [prefixWord, tailWord_1722569, baseEnd_1722569] using wordTrace_append hprefix tailTrace_1722569
  have hstable : (prefixWord ++ tailWord_1722569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722569).length < 2 ^ (prefixWord ++ tailWord_1722569).sum := by decide
  have hdescent : baseEnd_1722569 < baseStart_1722569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722594 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1722594 : Nat := 118140960795 + 1722594 * 2 ^ 59
def prefixEnd_1722594 : Nat := 4983230072969 + 3 ^ 40 * 1722594 * 2
def baseEnd_1722594 : Nat := 884518694551138576752941

theorem tailTrace_1722594 : CollatzResearch.WordTrace tailWord_1722594 prefixEnd_1722594 884518694551138576752941 := by
  unfold tailWord_1722594
  simp only [CollatzResearch.WordTrace]
  refine ⟨15707041180335902119549709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41885443147562405652132557 15707041180335902119549709)
  ·
    refine ⟨5890140442625963294831141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15707041180335902119549709 5890140442625963294831141)
    ·
      refine ⟨1104401332992368117780839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5890140442625963294831141 1104401332992368117780839)
      ·
        refine ⟨1656601999488552176671259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104401332992368117780839 1656601999488552176671259)
        ·
          refine ⟨2484902999232828265006889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1656601999488552176671259 2484902999232828265006889)
          ·
            refine ⟨1863677249424621198755167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2484902999232828265006889 1863677249424621198755167)
            ·
              refine ⟨2795515874136931798132751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1863677249424621198755167 2795515874136931798132751)
              ·
                refine ⟨4193273811205397697199127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2795515874136931798132751 4193273811205397697199127)
                ·
                  refine ⟨6289910716808096545798691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4193273811205397697199127 6289910716808096545798691)
                  ·
                    refine ⟨9434866075212144818698037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6289910716808096545798691 9434866075212144818698037)
                    ·
                      refine ⟨884518694551138576752941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9434866075212144818698037 884518694551138576752941)
                      ·
                        rfl

theorem cell23_1722594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1722594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722594 prefixEnd_1722594 := by exact prefixLift 1722594
  have htrace : WordTrace (prefixWord ++ tailWord_1722594) baseStart_1722594 baseEnd_1722594 := by
    simpa [prefixWord, tailWord_1722594, baseEnd_1722594] using wordTrace_append hprefix tailTrace_1722594
  have hstable : (prefixWord ++ tailWord_1722594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722594).length < 2 ^ (prefixWord ++ tailWord_1722594).sum := by decide
  have hdescent : baseEnd_1722594 < baseStart_1722594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722606 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 2, 6]
def baseStart_1722606 : Nat := 118140960795 + 1722606 * 2 ^ 59
def prefixEnd_1722606 : Nat := 4983230072969 + 3 ^ 40 * 1722606 * 2
def baseEnd_1722606 : Nat := 294841618772997509934295

theorem tailTrace_1722606 : CollatzResearch.WordTrace tailWord_1722606 prefixEnd_1722606 294841618772997509934295 := by
  unfold tailWord_1722606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7853575299662516815954459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41885734931533423018423781 7853575299662516815954459)
  ·
    refine ⟨11780362949493775223931689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7853575299662516815954459 11780362949493775223931689)
    ·
      refine ⟨8835272212120331417948767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11780362949493775223931689 8835272212120331417948767)
      ·
        refine ⟨13252908318180497126923151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8835272212120331417948767 13252908318180497126923151)
        ·
          refine ⟨19879362477270745690384727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13252908318180497126923151 19879362477270745690384727)
          ·
            refine ⟨29819043715906118535577091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19879362477270745690384727 29819043715906118535577091)
            ·
              refine ⟨44728565573859177803365637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29819043715906118535577091 44728565573859177803365637)
              ·
                refine ⟨8386606045098595838131057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44728565573859177803365637 8386606045098595838131057)
                ·
                  refine ⟨6289954533823946878598293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8386606045098595838131057 6289954533823946878598293)
                  ·
                    refine ⟨294841618772997509934295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6289954533823946878598293 294841618772997509934295)
                    ·
                      rfl

theorem cell23_1722606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_1722606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722606 prefixEnd_1722606 := by exact prefixLift 1722606
  have htrace : WordTrace (prefixWord ++ tailWord_1722606) baseStart_1722606 baseEnd_1722606 := by
    simpa [prefixWord, tailWord_1722606, baseEnd_1722606] using wordTrace_append hprefix tailTrace_1722606
  have hstable : (prefixWord ++ tailWord_1722606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722606).length < 2 ^ (prefixWord ++ tailWord_1722606).sum := by decide
  have hdescent : baseEnd_1722606 < baseStart_1722606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722619 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 13]
def baseStart_1722619 : Nat := 118140960795 + 1722619 * 2 ^ 59
def prefixEnd_1722619 : Nat := 4983230072969 + 3 ^ 40 * 1722619 * 2
def baseEnd_1722619 : Nat := 98281281285277886548925

theorem tailTrace_1722619 : CollatzResearch.WordTrace tailWord_1722619 prefixEnd_1722619 98281281285277886548925 := by
  unfold tailWord_1722619
  simp only [CollatzResearch.WordTrace]
  refine ⟨62829076546253037747858911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41886051030835358498572607 62829076546253037747858911)
  ·
    refine ⟨94243614819379556621788367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62829076546253037747858911 94243614819379556621788367)
    ·
      refine ⟨141365422229069334932682551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94243614819379556621788367 141365422229069334932682551)
      ·
        refine ⟨212048133343604002399023827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141365422229069334932682551 212048133343604002399023827)
        ·
          refine ⟨318072200015406003598535741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212048133343604002399023827 318072200015406003598535741)
          ·
            refine ⟨119277075005777251349450903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 318072200015406003598535741 119277075005777251349450903)
            ·
              refine ⟨178915612508665877024176355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119277075005777251349450903 178915612508665877024176355)
              ·
                refine ⟨268373418762998815536264533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178915612508665877024176355 268373418762998815536264533)
                ·
                  refine ⟨98281281285277886548925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 268373418762998815536264533 98281281285277886548925)
                  ·
                    rfl

theorem cell23_1722619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 13].length) (baseStart_1722619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722619 prefixEnd_1722619 := by exact prefixLift 1722619
  have htrace : WordTrace (prefixWord ++ tailWord_1722619) baseStart_1722619 baseEnd_1722619 := by
    simpa [prefixWord, tailWord_1722619, baseEnd_1722619] using wordTrace_append hprefix tailTrace_1722619
  have hstable : (prefixWord ++ tailWord_1722619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722619).length < 2 ^ (prefixWord ++ tailWord_1722619).sum := by decide
  have hdescent : baseEnd_1722619 < baseStart_1722619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722636 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 7]
def baseStart_1722636 : Nat := 118140960795 + 1722636 * 2 ^ 59
def prefixEnd_1722636 : Nat := 4983230072969 + 3 ^ 40 * 1722636 * 2
def baseEnd_1722636 : Nat := 98282251193180823603083

theorem tailTrace_1722636 : CollatzResearch.WordTrace tailWord_1722636 prefixEnd_1722636 98282251193180823603083 := by
  unfold tailWord_1722636
  simp only [CollatzResearch.WordTrace]
  refine ⟨31414848293595724825613881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41886464391460966434151841 31414848293595724825613881)
  ·
    refine ⟨23561136220196793619210411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31414848293595724825613881 23561136220196793619210411)
    ·
      refine ⟨35341704330295190428815617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23561136220196793619210411 35341704330295190428815617)
      ·
        refine ⟨26506278247721392821611713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35341704330295190428815617 26506278247721392821611713)
        ·
          refine ⟨19879708685791044616208785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26506278247721392821611713 19879708685791044616208785)
          ·
            refine ⟨14909781514343283462156589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19879708685791044616208785 14909781514343283462156589)
            ·
              refine ⟨5591168067878731298308721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14909781514343283462156589 5591168067878731298308721)
              ·
                refine ⟨4193376050909048473731541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5591168067878731298308721 4193376050909048473731541)
                ·
                  refine ⟨98282251193180823603083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4193376050909048473731541 98282251193180823603083)
                  ·
                    rfl

theorem cell23_1722636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 7].length) (baseStart_1722636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722636 prefixEnd_1722636 := by exact prefixLift 1722636
  have htrace : WordTrace (prefixWord ++ tailWord_1722636) baseStart_1722636 baseEnd_1722636 := by
    simpa [prefixWord, tailWord_1722636, baseEnd_1722636] using wordTrace_append hprefix tailTrace_1722636
  have hstable : (prefixWord ++ tailWord_1722636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722636).length < 2 ^ (prefixWord ++ tailWord_1722636).sum := by decide
  have hdescent : baseEnd_1722636 < baseStart_1722636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722703 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 4, 4, 2]
def baseStart_1722703 : Nat := 118140960795 + 1722703 * 2 ^ 59
def prefixEnd_1722703 : Nat := 4983230072969 + 3 ^ 40 * 1722703 * 2
def baseEnd_1722703 : Nat := 884574663942478650289939

theorem tailTrace_1722703 : CollatzResearch.WordTrace tailWord_1722703 prefixEnd_1722703 884574663942478650289939 := by
  unfold tailWord_1722703
  simp only [CollatzResearch.WordTrace]
  refine ⟨62832140277948720093916763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41888093518632480062611175 62832140277948720093916763)
  ·
    refine ⟨94248210416923080140875145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62832140277948720093916763 94248210416923080140875145)
    ·
      refine ⟨70686157812692310105656359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94248210416923080140875145 70686157812692310105656359)
      ·
        refine ⟨106029236719038465158484539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70686157812692310105656359 106029236719038465158484539)
        ·
          refine ⟨159043855078557697737726809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106029236719038465158484539 159043855078557697737726809)
          ·
            refine ⟨119282891308918273303295107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159043855078557697737726809 119282891308918273303295107)
            ·
              refine ⟨178924336963377409954942661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119282891308918273303295107 178924336963377409954942661)
              ·
                refine ⟨33548313180633264366551749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178924336963377409954942661 33548313180633264366551749)
                ·
                  refine ⟨6290308721368737068728453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33548313180633264366551749 6290308721368737068728453)
                  ·
                    refine ⟨1179432885256638200386585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6290308721368737068728453 1179432885256638200386585)
                    ·
                      refine ⟨884574663942478650289939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1179432885256638200386585 884574663942478650289939)
                      ·
                        rfl

theorem cell23_1722703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 4, 2].length) (baseStart_1722703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722703 prefixEnd_1722703 := by exact prefixLift 1722703
  have htrace : WordTrace (prefixWord ++ tailWord_1722703) baseStart_1722703 baseEnd_1722703 := by
    simpa [prefixWord, tailWord_1722703, baseEnd_1722703] using wordTrace_append hprefix tailTrace_1722703
  have hstable : (prefixWord ++ tailWord_1722703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722703).length < 2 ^ (prefixWord ++ tailWord_1722703).sum := by decide
  have hdescent : baseEnd_1722703 < baseStart_1722703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722720 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 4]
def baseStart_1722720 : Nat := 118140960795 + 1722720 * 2 ^ 59
def prefixEnd_1722720 : Nat := 4983230072969 + 3 ^ 40 * 1722720 * 2
def baseEnd_1722720 : Nat := 884583393113605083777361

theorem tailTrace_1722720 : CollatzResearch.WordTrace tailWord_1722720 prefixEnd_1722720 884583393113605083777361 := by
  unfold tailWord_1722720
  simp only [CollatzResearch.WordTrace]
  refine ⟨31416380159443565998642807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41888506879258087998190409 31416380159443565998642807)
  ·
    refine ⟨47124570239165348997964211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31416380159443565998642807 47124570239165348997964211)
    ·
      refine ⟨70686855358748023496946317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47124570239165348997964211 70686855358748023496946317)
      ·
        refine ⟨26507570759530508811354869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70686855358748023496946317 26507570759530508811354869)
        ·
          refine ⟨2485084758705985201064519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26507570759530508811354869 2485084758705985201064519)
          ·
            refine ⟨3727627138058977801596779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485084758705985201064519 3727627138058977801596779)
            ·
              refine ⟨5591440707088466702395169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3727627138058977801596779 5591440707088466702395169)
              ·
                refine ⟨4193580530316350026796377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5591440707088466702395169 4193580530316350026796377)
                ·
                  refine ⟨3145185397737262520097283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4193580530316350026796377 3145185397737262520097283)
                  ·
                    refine ⟨4717778096605893780145925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3145185397737262520097283 4717778096605893780145925)
                    ·
                      refine ⟨884583393113605083777361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4717778096605893780145925 884583393113605083777361)
                      ·
                        rfl

theorem cell23_1722720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_1722720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722720 prefixEnd_1722720 := by exact prefixLift 1722720
  have htrace : WordTrace (prefixWord ++ tailWord_1722720) baseStart_1722720 baseEnd_1722720 := by
    simpa [prefixWord, tailWord_1722720, baseEnd_1722720] using wordTrace_append hprefix tailTrace_1722720
  have hstable : (prefixWord ++ tailWord_1722720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722720).length < 2 ^ (prefixWord ++ tailWord_1722720).sum := by decide
  have hdescent : baseEnd_1722720 < baseStart_1722720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722754 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1722754 : Nat := 118140960795 + 1722754 * 2 ^ 59
def prefixEnd_1722754 : Nat := 4983230072969 + 3 ^ 40 * 1722754 * 2
def baseEnd_1722754 : Nat := 884600851455857950752205

theorem tailTrace_1722754 : CollatzResearch.WordTrace tailWord_1722754 prefixEnd_1722754 884600851455857950752205 := by
  unfold tailWord_1722754
  simp only [CollatzResearch.WordTrace]
  refine ⟨15708500100190988951005829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41889333600509303869348877 15708500100190988951005829)
  ·
    refine ⟨2945343768785810428313593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15708500100190988951005829 2945343768785810428313593)
    ·
      refine ⟨2209007826589357821235195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2945343768785810428313593 2209007826589357821235195)
      ·
        refine ⟨3313511739884036731852793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209007826589357821235195 3313511739884036731852793)
        ·
          refine ⟨2485133804913027548889595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3313511739884036731852793 2485133804913027548889595)
          ·
            refine ⟨3727700707369541323334393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485133804913027548889595 3727700707369541323334393)
            ·
              refine ⟨2795775530527155992500795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3727700707369541323334393 2795775530527155992500795)
              ·
                refine ⟨4193663295790733988751193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2795775530527155992500795 4193663295790733988751193)
                ·
                  refine ⟨3145247471843050491563395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4193663295790733988751193 3145247471843050491563395)
                  ·
                    refine ⟨4717871207764575737345093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3145247471843050491563395 4717871207764575737345093)
                    ·
                      refine ⟨884600851455857950752205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4717871207764575737345093 884600851455857950752205)
                      ·
                        rfl

theorem cell23_1722754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1722754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722754 prefixEnd_1722754 := by exact prefixLift 1722754
  have htrace : WordTrace (prefixWord ++ tailWord_1722754) baseStart_1722754 baseEnd_1722754 := by
    simpa [prefixWord, tailWord_1722754, baseEnd_1722754] using wordTrace_append hprefix tailTrace_1722754
  have hstable : (prefixWord ++ tailWord_1722754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722754).length < 2 ^ (prefixWord ++ tailWord_1722754).sum := by decide
  have hdescent : baseEnd_1722754 < baseStart_1722754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722781 : List Nat := [1, 4, 2, 1, 4, 2, 2, 2, 1, 4]
def baseStart_1722781 : Nat := 118140960795 + 1722781 * 2 ^ 59
def prefixEnd_1722781 : Nat := 4983230072969 + 3 ^ 40 * 1722781 * 2
def baseEnd_1722781 : Nat := 294871571811176448371527

theorem tailTrace_1722781 : CollatzResearch.WordTrace tailWord_1722781 prefixEnd_1722781 294871571811176448371527 := by
  unfold tailWord_1722781
  simp only [CollatzResearch.WordTrace]
  refine ⟨62834985171666139415256197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41889990114444092943504131 62834985171666139415256197)
  ·
    refine ⟨11781559719687401140360537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62834985171666139415256197 11781559719687401140360537)
    ·
      refine ⟨8836169789765550855270403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11781559719687401140360537 8836169789765550855270403)
      ·
        refine ⟨13254254684648326282905605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8836169789765550855270403 13254254684648326282905605)
        ·
          refine ⟨2485172753371561178044801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13254254684648326282905605 2485172753371561178044801)
          ·
            refine ⟨1863879565028670883533601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2485172753371561178044801 1863879565028670883533601)
            ·
              refine ⟨1397909673771503162650201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1863879565028670883533601 1397909673771503162650201)
              ·
                refine ⟨1048432255328627371987651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1397909673771503162650201 1048432255328627371987651)
                ·
                  refine ⟨1572648382992941057981477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1048432255328627371987651 1572648382992941057981477)
                  ·
                    refine ⟨294871571811176448371527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1572648382992941057981477 294871571811176448371527)
                    ·
                      rfl

theorem cell23_1722781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_1722781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722781 prefixEnd_1722781 := by exact prefixLift 1722781
  have htrace : WordTrace (prefixWord ++ tailWord_1722781) baseStart_1722781 baseEnd_1722781 := by
    simpa [prefixWord, tailWord_1722781, baseEnd_1722781] using wordTrace_append hprefix tailTrace_1722781
  have hstable : (prefixWord ++ tailWord_1722781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722781).length < 2 ^ (prefixWord ++ tailWord_1722781).sum := by decide
  have hdescent : baseEnd_1722781 < baseStart_1722781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722803 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 8, 4]
def baseStart_1722803 : Nat := 118140960795 + 1722803 * 2 ^ 59
def prefixEnd_1722803 : Nat := 4983230072969 + 3 ^ 40 * 1722803 * 2
def baseEnd_1722803 : Nat := 294875337335976086346493

theorem tailTrace_1722803 : CollatzResearch.WordTrace tailWord_1722803 prefixEnd_1722803 294875337335976086346493 := by
  unfold tailWord_1722803
  simp only [CollatzResearch.WordTrace]
  refine ⟨62835787577586437172557063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41890525051724291448371375 62835787577586437172557063)
  ·
    refine ⟨94253681366379655758835595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62835787577586437172557063 94253681366379655758835595)
    ·
      refine ⟨141380522049569483638253393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94253681366379655758835595 141380522049569483638253393)
      ·
        refine ⟨106035391537177112728690045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141380522049569483638253393 106035391537177112728690045)
        ·
          refine ⟨39763271826441417273258767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106035391537177112728690045 39763271826441417273258767)
          ·
            refine ⟨59644907739662125909888151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39763271826441417273258767 59644907739662125909888151)
            ·
              refine ⟨89467361609493188864832227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59644907739662125909888151 89467361609493188864832227)
              ·
                refine ⟨134201042414239783297248341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89467361609493188864832227 134201042414239783297248341)
                ·
                  refine ⟨1572668465791872460514629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 134201042414239783297248341 1572668465791872460514629)
                  ·
                    refine ⟨294875337335976086346493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1572668465791872460514629 294875337335976086346493)
                    ·
                      rfl

theorem cell23_1722803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 4].length) (baseStart_1722803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722803 prefixEnd_1722803 := by exact prefixLift 1722803
  have htrace : WordTrace (prefixWord ++ tailWord_1722803) baseStart_1722803 baseEnd_1722803 := by
    simpa [prefixWord, tailWord_1722803, baseEnd_1722803] using wordTrace_append hprefix tailTrace_1722803
  have hstable : (prefixWord ++ tailWord_1722803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722803).length < 2 ^ (prefixWord ++ tailWord_1722803).sum := by decide
  have hdescent : baseEnd_1722803 < baseStart_1722803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722837 : List Nat := [1, 3, 2, 3, 1, 2, 3, 2, 2, 4]
def baseStart_1722837 : Nat := 118140960795 + 1722837 * 2 ^ 59
def prefixEnd_1722837 : Nat := 4983230072969 + 3 ^ 40 * 1722837 * 2
def baseEnd_1722837 : Nat := 294881156783393708671441

theorem tailTrace_1722837 : CollatzResearch.WordTrace tailWord_1722837 prefixEnd_1722837 294881156783393708671441 := by
  unfold tailWord_1722837
  simp only [CollatzResearch.WordTrace]
  refine ⟨62837027659463260979294765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41891351772975507319529843 62837027659463260979294765)
  ·
    refine ⟨23563885372298722867235537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62837027659463260979294765 23563885372298722867235537)
    ·
      refine ⟨17672914029224042150426653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23563885372298722867235537 17672914029224042150426653)
      ·
        refine ⟨6627342760959015806409995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17672914029224042150426653 6627342760959015806409995)
        ·
          refine ⟨9941014141438523709614993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6627342760959015806409995 9941014141438523709614993)
          ·
            refine ⟨7455760606078892782211245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9941014141438523709614993 7455760606078892782211245)
            ·
              refine ⟨2795910227279584793329217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7455760606078892782211245 2795910227279584793329217)
              ·
                refine ⟨2096932670459688594996913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2795910227279584793329217 2096932670459688594996913)
                ·
                  refine ⟨1572699502844766446247685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2096932670459688594996913 1572699502844766446247685)
                  ·
                    refine ⟨294881156783393708671441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1572699502844766446247685 294881156783393708671441)
                    ·
                      rfl

theorem cell23_1722837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_1722837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722837 prefixEnd_1722837 := by exact prefixLift 1722837
  have htrace : WordTrace (prefixWord ++ tailWord_1722837) baseStart_1722837 baseEnd_1722837 := by
    simpa [prefixWord, tailWord_1722837, baseEnd_1722837] using wordTrace_append hprefix tailTrace_1722837
  have hstable : (prefixWord ++ tailWord_1722837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722837).length < 2 ^ (prefixWord ++ tailWord_1722837).sum := by decide
  have hdescent : baseEnd_1722837 < baseStart_1722837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722873 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 2, 2, 5]
def baseStart_1722873 : Nat := 118140960795 + 1722873 * 2 ^ 59
def prefixEnd_1722873 : Nat := 4983230072969 + 3 ^ 40 * 1722873 * 2
def baseEnd_1722873 : Nat := 884661955653742985164157

theorem tailTrace_1722873 : CollatzResearch.WordTrace tailWord_1722873 prefixEnd_1722873 884661955653742985164157 := by
  unfold tailWord_1722873
  simp only [CollatzResearch.WordTrace]
  refine ⟨62838340687332839127605273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41892227124888559418403515 62838340687332839127605273)
  ·
    refine ⟨47128755515499629345703955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62838340687332839127605273 47128755515499629345703955)
    ·
      refine ⟨70693133273249444018555933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47128755515499629345703955 70693133273249444018555933)
      ·
        refine ⟨26509924977468541506958475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70693133273249444018555933 26509924977468541506958475)
        ·
          refine ⟨39764887466202812260437713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26509924977468541506958475 39764887466202812260437713)
          ·
            refine ⟨29823665599652109195328285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39764887466202812260437713 29823665599652109195328285)
            ·
              refine ⟨11183874599869540948248107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29823665599652109195328285 11183874599869540948248107)
              ·
                refine ⟨16775811899804311422372161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11183874599869540948248107 16775811899804311422372161)
                ·
                  refine ⟨12581858924853233566779121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16775811899804311422372161 12581858924853233566779121)
                  ·
                    refine ⟨9436394193639925175084341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12581858924853233566779121 9436394193639925175084341)
                    ·
                      refine ⟨884661955653742985164157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9436394193639925175084341 884661955653742985164157)
                      ·
                        rfl

theorem cell23_1722873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_1722873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722873 prefixEnd_1722873 := by exact prefixLift 1722873
  have htrace : WordTrace (prefixWord ++ tailWord_1722873) baseStart_1722873 baseEnd_1722873 := by
    simpa [prefixWord, tailWord_1722873, baseEnd_1722873] using wordTrace_append hprefix tailTrace_1722873
  have hstable : (prefixWord ++ tailWord_1722873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722873).length < 2 ^ (prefixWord ++ tailWord_1722873).sum := by decide
  have hdescent : baseEnd_1722873 < baseStart_1722873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722923 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 7]
def baseStart_1722923 : Nat := 118140960795 + 1722923 * 2 ^ 59
def prefixEnd_1722923 : Nat := 4983230072969 + 3 ^ 40 * 1722923 * 2
def baseEnd_1722923 : Nat := 98298625520718643282103

theorem tailTrace_1722923 : CollatzResearch.WordTrace tailWord_1722923 prefixEnd_1722923 98298625520718643282103 := by
  unfold tailWord_1722923
  simp only [CollatzResearch.WordTrace]
  refine ⟨62840164337151697666925423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41893442891434465111283615 62840164337151697666925423)
  ·
    refine ⟨94260246505727546500388135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62840164337151697666925423 94260246505727546500388135)
    ·
      refine ⟨141390369758591319750582203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94260246505727546500388135 141390369758591319750582203)
      ·
        refine ⟨212085554637886979625873305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141390369758591319750582203 212085554637886979625873305)
        ·
          refine ⟨159064165978415234719404979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212085554637886979625873305 159064165978415234719404979)
          ·
            refine ⟨238596248967622852079107469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159064165978415234719404979 238596248967622852079107469)
            ·
              refine ⟨89473593362858569529665301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238596248967622852079107469 89473593362858569529665301)
              ·
                refine ⟨4194074688883995446703061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89473593362858569529665301 4194074688883995446703061)
                ·
                  refine ⟨98298625520718643282103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4194074688883995446703061 98298625520718643282103)
                  ·
                    rfl

theorem cell23_1722923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 7].length) (baseStart_1722923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722923 prefixEnd_1722923 := by exact prefixLift 1722923
  have htrace : WordTrace (prefixWord ++ tailWord_1722923) baseStart_1722923 baseEnd_1722923 := by
    simpa [prefixWord, tailWord_1722923, baseEnd_1722923] using wordTrace_append hprefix tailTrace_1722923
  have hstable : (prefixWord ++ tailWord_1722923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722923).length < 2 ^ (prefixWord ++ tailWord_1722923).sum := by decide
  have hdescent : baseEnd_1722923 < baseStart_1722923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722934 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_1722934 : Nat := 118140960795 + 1722934 * 2 ^ 59
def prefixEnd_1722934 : Nat := 4983230072969 + 3 ^ 40 * 1722934 * 2
def baseEnd_1722934 : Nat := 884693277973667246501377

theorem tailTrace_1722934 : CollatzResearch.WordTrace tailWord_1722934 prefixEnd_1722934 884693277973667246501377 := by
  unfold tailWord_1722934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3927535346256990409098491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41893710360074564363717237 3927535346256990409098491)
  ·
    refine ⟨5891303019385485613647737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3927535346256990409098491 5891303019385485613647737)
    ·
      refine ⟨4418477264539114210235803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5891303019385485613647737 4418477264539114210235803)
      ·
        refine ⟨6627715896808671315353705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4418477264539114210235803 6627715896808671315353705)
        ·
          refine ⟨4970786922606503486515279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6627715896808671315353705 4970786922606503486515279)
          ·
            refine ⟨7456180383909755229772919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4970786922606503486515279 7456180383909755229772919)
            ·
              refine ⟨11184270575864632844659379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7456180383909755229772919 11184270575864632844659379)
              ·
                refine ⟨16776405863796949266989069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11184270575864632844659379 16776405863796949266989069)
                ·
                  refine ⟨6291152198923855975120901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16776405863796949266989069 6291152198923855975120901)
                  ·
                    refine ⟨1179591037298222995335169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6291152198923855975120901 1179591037298222995335169)
                    ·
                      refine ⟨884693277973667246501377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1179591037298222995335169 884693277973667246501377)
                      ·
                        rfl

theorem cell23_1722934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_1722934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722934 prefixEnd_1722934 := by exact prefixLift 1722934
  have htrace : WordTrace (prefixWord ++ tailWord_1722934) baseStart_1722934 baseEnd_1722934 := by
    simpa [prefixWord, tailWord_1722934, baseEnd_1722934] using wordTrace_append hprefix tailTrace_1722934
  have hstable : (prefixWord ++ tailWord_1722934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722934).length < 2 ^ (prefixWord ++ tailWord_1722934).sum := by decide
  have hdescent : baseEnd_1722934 < baseStart_1722934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722951 : List Nat := [1, 1, 4, 1, 4, 2, 2, 2, 2, 2, 2]
def baseStart_1722951 : Nat := 118140960795 + 1722951 * 2 ^ 59
def prefixEnd_1722951 : Nat := 4983230072969 + 3 ^ 40 * 1722951 * 2
def baseEnd_1722951 : Nat := 884702007144793679988799

theorem tailTrace_1722951 : CollatzResearch.WordTrace tailWord_1722951 prefixEnd_1722951 884702007144793679988799 := by
  unfold tailWord_1722951
  simp only [CollatzResearch.WordTrace]
  refine ⟨62841185581050258448944707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41894123720700172299296471 62841185581050258448944707)
  ·
    refine ⟨94261778371575387673417061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62841185581050258448944707 94261778371575387673417061)
    ·
      refine ⟨17674083444670385188765699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94261778371575387673417061 17674083444670385188765699)
      ·
        refine ⟨26511125167005577783148549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17674083444670385188765699 26511125167005577783148549)
        ·
          refine ⟨4970835968813545834340353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26511125167005577783148549 4970835968813545834340353)
          ·
            refine ⟨3728126976610159375755265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4970835968813545834340353 3728126976610159375755265)
            ·
              refine ⟨2796095232457619531816449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3728126976610159375755265 2796095232457619531816449)
              ·
                refine ⟨2097071424343214648862337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2796095232457619531816449 2097071424343214648862337)
                ·
                  refine ⟨1572803568257410986646753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2097071424343214648862337 1572803568257410986646753)
                  ·
                    refine ⟨1179602676193058239985065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1572803568257410986646753 1179602676193058239985065)
                    ·
                      refine ⟨884702007144793679988799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1179602676193058239985065 884702007144793679988799)
                      ·
                        rfl

theorem cell23_1722951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_1722951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722951 prefixEnd_1722951 := by exact prefixLift 1722951
  have htrace : WordTrace (prefixWord ++ tailWord_1722951) baseStart_1722951 baseEnd_1722951 := by
    simpa [prefixWord, tailWord_1722951, baseEnd_1722951] using wordTrace_append hprefix tailTrace_1722951
  have hstable : (prefixWord ++ tailWord_1722951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722951).length < 2 ^ (prefixWord ++ tailWord_1722951).sum := by decide
  have hdescent : baseEnd_1722951 < baseStart_1722951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1722953 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 5, 7]
def baseStart_1722953 : Nat := 118140960795 + 1722953 * 2 ^ 59
def prefixEnd_1722953 : Nat := 4983230072969 + 3 ^ 40 * 1722953 * 2
def baseEnd_1722953 : Nat := 294901011368700890721263

theorem tailTrace_1722953 : CollatzResearch.WordTrace tailWord_1722953 prefixEnd_1722953 294901011368700890721263 := by
  unfold tailWord_1722953
  simp only [CollatzResearch.WordTrace]
  refine ⟨62841258527043012790517513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41894172351362008527011675 62841258527043012790517513)
  ·
    refine ⟨47130943895282259592888135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62841258527043012790517513 47130943895282259592888135)
    ·
      refine ⟨70696415842923389389332203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47130943895282259592888135 70696415842923389389332203)
      ·
        refine ⟨106044623764385084083998305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70696415842923389389332203 106044623764385084083998305)
        ·
          refine ⟨79533467823288813062998729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106044623764385084083998305 79533467823288813062998729)
          ·
            refine ⟨59650100867466609797249047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79533467823288813062998729 59650100867466609797249047)
            ·
              refine ⟨89475151301199914695873571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59650100867466609797249047 89475151301199914695873571)
              ·
                refine ⟨134212726951799872043810357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89475151301199914695873571 134212726951799872043810357)
                ·
                  refine ⟨12582443151731238004107221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134212726951799872043810357 12582443151731238004107221)
                  ·
                    refine ⟨294901011368700890721263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12582443151731238004107221 294901011368700890721263)
                    ·
                      rfl

theorem cell23_1722953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 7].length) (baseStart_1722953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1722953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1722953 prefixEnd_1722953 := by exact prefixLift 1722953
  have htrace : WordTrace (prefixWord ++ tailWord_1722953) baseStart_1722953 baseEnd_1722953 := by
    simpa [prefixWord, tailWord_1722953, baseEnd_1722953] using wordTrace_append hprefix tailTrace_1722953
  have hstable : (prefixWord ++ tailWord_1722953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1722953).length < 2 ^ (prefixWord ++ tailWord_1722953).sum := by decide
  have hdescent : baseEnd_1722953 < baseStart_1722953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1722953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723097 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 3, 1, 4]
def baseStart_1723097 : Nat := 118140960795 + 1723097 * 2 ^ 59
def prefixEnd_1723097 : Nat := 4983230072969 + 3 ^ 40 * 1723097 * 2
def baseEnd_1723097 : Nat := 884776975320350108763127

theorem tailTrace_1723097 : CollatzResearch.WordTrace tailWord_1723097 prefixEnd_1723097 884776975320350108763127 := by
  unfold tailWord_1723097
  simp only [CollatzResearch.WordTrace]
  refine ⟨62846510638521325383759545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41897673759014216922506363 62846510638521325383759545)
  ·
    refine ⟨47134882978890994037819659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62846510638521325383759545 47134882978890994037819659)
    ·
      refine ⟨70702324468336491056729489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47134882978890994037819659 70702324468336491056729489)
      ·
        refine ⟨53026743351252368292547117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70702324468336491056729489 53026743351252368292547117)
        ·
          refine ⟨19885028756719638109705169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53026743351252368292547117 19885028756719638109705169)
          ·
            refine ⟨14913771567539728582278877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19885028756719638109705169 14913771567539728582278877)
            ·
              refine ⟨5592664337827398218354579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14913771567539728582278877 5592664337827398218354579)
              ·
                refine ⟨8388996506741097327531869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5592664337827398218354579 8388996506741097327531869)
                ·
                  refine ⟨3145873690027911497824451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8388996506741097327531869 3145873690027911497824451)
                  ·
                    refine ⟨4718810535041867246736677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3145873690027911497824451 4718810535041867246736677)
                    ·
                      refine ⟨884776975320350108763127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4718810535041867246736677 884776975320350108763127)
                      ·
                        rfl

theorem cell23_1723097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_1723097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723097 prefixEnd_1723097 := by exact prefixLift 1723097
  have htrace : WordTrace (prefixWord ++ tailWord_1723097) baseStart_1723097 baseEnd_1723097 := by
    simpa [prefixWord, tailWord_1723097, baseEnd_1723097] using wordTrace_append hprefix tailTrace_1723097
  have hstable : (prefixWord ++ tailWord_1723097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723097).length < 2 ^ (prefixWord ++ tailWord_1723097).sum := by decide
  have hdescent : baseEnd_1723097 < baseStart_1723097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723107 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 3, 6]
def baseStart_1723107 : Nat := 118140960795 + 1723107 * 2 ^ 59
def prefixEnd_1723107 : Nat := 4983230072969 + 3 ^ 40 * 1723107 * 2
def baseEnd_1723107 : Nat := 294927370042298356546027

theorem tailTrace_1723107 : CollatzResearch.WordTrace tailWord_1723107 prefixEnd_1723107 294927370042298356546027 := by
  unfold tailWord_1723107
  simp only [CollatzResearch.WordTrace]
  refine ⟨62846875368485097091623575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41897916912323398061082383 62846875368485097091623575)
  ·
    refine ⟨94270313052727645637435363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62846875368485097091623575 94270313052727645637435363)
    ·
      refine ⟨141405469579091468456153045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94270313052727645637435363 141405469579091468456153045)
      ·
        refine ⟨3314190693259956291941087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 141405469579091468456153045 3314190693259956291941087)
        ·
          refine ⟨4971286039889934437911631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3314190693259956291941087 4971286039889934437911631)
          ·
            refine ⟨7456929059834901656867447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4971286039889934437911631 7456929059834901656867447)
            ·
              refine ⟨11185393589752352485301171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7456929059834901656867447 11185393589752352485301171)
              ·
                refine ⟨16778090384628528727951757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11185393589752352485301171 16778090384628528727951757)
                ·
                  refine ⟨6291783894235698272981909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16778090384628528727951757 6291783894235698272981909)
                  ·
                    refine ⟨294927370042298356546027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6291783894235698272981909 294927370042298356546027)
                    ·
                      rfl

theorem cell23_1723107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 6].length) (baseStart_1723107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723107 prefixEnd_1723107 := by exact prefixLift 1723107
  have htrace : WordTrace (prefixWord ++ tailWord_1723107) baseStart_1723107 baseEnd_1723107 := by
    simpa [prefixWord, tailWord_1723107, baseEnd_1723107] using wordTrace_append hprefix tailTrace_1723107
  have hstable : (prefixWord ++ tailWord_1723107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723107).length < 2 ^ (prefixWord ++ tailWord_1723107).sum := by decide
  have hdescent : baseEnd_1723107 < baseStart_1723107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723144 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 1, 2, 4]
def baseStart_1723144 : Nat := 118140960795 + 1723144 * 2 ^ 59
def prefixEnd_1723144 : Nat := 4983230072969 + 3 ^ 40 * 1723144 * 2
def baseEnd_1723144 : Nat := 884801108911111424875411

theorem tailTrace_1723144 : CollatzResearch.WordTrace tailWord_1723144 prefixEnd_1723144 884801108911111424875411 := by
  unfold tailWord_1723144
  simp only [CollatzResearch.WordTrace]
  refine ⟨31424112434675526205360243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41898816579567368273813657 31424112434675526205360243)
  ·
    refine ⟨47136168652013289308040365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31424112434675526205360243 47136168652013289308040365)
    ·
      refine ⟨17676063244504983490515137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47136168652013289308040365 17676063244504983490515137)
      ·
        refine ⟨13257047433378737617886353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17676063244504983490515137 13257047433378737617886353)
        ·
          refine ⟨9942785575034053213414765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13257047433378737617886353 9942785575034053213414765)
          ·
            refine ⟨3728544590637769955030537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9942785575034053213414765 3728544590637769955030537)
            ·
              refine ⟨2796408442978327466272903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3728544590637769955030537 2796408442978327466272903)
              ·
                refine ⟨4194612664467491199409355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2796408442978327466272903 4194612664467491199409355)
                ·
                  refine ⟨6291918996701236799114033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194612664467491199409355 6291918996701236799114033)
                  ·
                    refine ⟨4718939247525927599335525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6291918996701236799114033 4718939247525927599335525)
                    ·
                      refine ⟨884801108911111424875411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4718939247525927599335525 884801108911111424875411)
                      ·
                        rfl

theorem cell23_1723144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_1723144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723144 prefixEnd_1723144 := by exact prefixLift 1723144
  have htrace : WordTrace (prefixWord ++ tailWord_1723144) baseStart_1723144 baseEnd_1723144 := by
    simpa [prefixWord, tailWord_1723144, baseEnd_1723144] using wordTrace_append hprefix tailTrace_1723144
  have hstable : (prefixWord ++ tailWord_1723144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723144).length < 2 ^ (prefixWord ++ tailWord_1723144).sum := by decide
  have hdescent : baseEnd_1723144 < baseStart_1723144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723164 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_1723164 : Nat := 118140960795 + 1723164 * 2 ^ 59
def prefixEnd_1723164 : Nat := 4983230072969 + 3 ^ 40 * 1723164 * 2
def baseEnd_1723164 : Nat := 884811378524201346625319

theorem tailTrace_1723164 : CollatzResearch.WordTrace tailWord_1723164 prefixEnd_1723164 884811378524201346625319 := by
  unfold tailWord_1723164
  simp only [CollatzResearch.WordTrace]
  refine ⟨31424477164639297913224273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41899302886185730550965697 31424477164639297913224273)
  ·
    refine ⟨23568357873479473434918205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31424477164639297913224273 23568357873479473434918205)
    ·
      refine ⟨8838134202554802538094327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23568357873479473434918205 8838134202554802538094327)
      ·
        refine ⟨13257201303832203807141491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8838134202554802538094327 13257201303832203807141491)
        ·
          refine ⟨19885801955748305710712237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13257201303832203807141491 19885801955748305710712237)
          ·
            refine ⟨7457175733405614641517089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19885801955748305710712237 7457175733405614641517089)
            ·
              refine ⟨5592881800054210981137817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7457175733405614641517089 5592881800054210981137817)
              ·
                refine ⟨4194661350040658235853363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5592881800054210981137817 4194661350040658235853363)
                ·
                  refine ⟨6291992025060987353780045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194661350040658235853363 6291992025060987353780045)
                  ·
                    refine ⟨2359497009397870257667517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6291992025060987353780045 2359497009397870257667517)
                    ·
                      refine ⟨884811378524201346625319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2359497009397870257667517 884811378524201346625319)
                      ·
                        rfl

theorem cell23_1723164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_1723164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723164 prefixEnd_1723164 := by exact prefixLift 1723164
  have htrace : WordTrace (prefixWord ++ tailWord_1723164) baseStart_1723164 baseEnd_1723164 := by
    simpa [prefixWord, tailWord_1723164, baseEnd_1723164] using wordTrace_append hprefix tailTrace_1723164
  have hstable : (prefixWord ++ tailWord_1723164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723164).length < 2 ^ (prefixWord ++ tailWord_1723164).sum := by decide
  have hdescent : baseEnd_1723164 < baseStart_1723164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723165 : List Nat := [1, 4, 2, 4, 1, 2, 2, 1, 1, 1, 4]
def baseStart_1723165 : Nat := 118140960795 + 1723165 * 2 ^ 59
def prefixEnd_1723165 : Nat := 4983230072969 + 3 ^ 40 * 1723165 * 2
def baseEnd_1723165 : Nat := 884811892004855842712815

theorem tailTrace_1723165 : CollatzResearch.WordTrace tailWord_1723165 prefixEnd_1723165 884811892004855842712815 := by
  unfold tailWord_1723165
  simp only [CollatzResearch.WordTrace]
  refine ⟨62848990802274972997234949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41899327201516648664823299 62848990802274972997234949)
  ·
    refine ⟨11784185775426557436981553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62848990802274972997234949 11784185775426557436981553)
    ·
      refine ⟨8838139331569918077736165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11784185775426557436981553 8838139331569918077736165)
      ·
        refine ⟨1657151124669359639575531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8838139331569918077736165 1657151124669359639575531)
        ·
          refine ⟨2485726687004039459363297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1657151124669359639575531 2485726687004039459363297)
          ·
            refine ⟨1864295015253029594522473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2485726687004039459363297 1864295015253029594522473)
            ·
              refine ⟨1398221261439772195891855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1864295015253029594522473 1398221261439772195891855)
              ·
                refine ⟨2097331892159658293837783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398221261439772195891855 2097331892159658293837783)
                ·
                  refine ⟨3145997838239487440756675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2097331892159658293837783 3145997838239487440756675)
                  ·
                    refine ⟨4718996757359231161135013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3145997838239487440756675 4718996757359231161135013)
                    ·
                      refine ⟨884811892004855842712815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4718996757359231161135013 884811892004855842712815)
                      ·
                        rfl

theorem cell23_1723165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_1723165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723165 prefixEnd_1723165 := by exact prefixLift 1723165
  have htrace : WordTrace (prefixWord ++ tailWord_1723165) baseStart_1723165 baseEnd_1723165 := by
    simpa [prefixWord, tailWord_1723165, baseEnd_1723165] using wordTrace_append hprefix tailTrace_1723165
  have hstable : (prefixWord ++ tailWord_1723165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723165).length < 2 ^ (prefixWord ++ tailWord_1723165).sum := by decide
  have hdescent : baseEnd_1723165 < baseStart_1723165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723168 : List Nat := [2, 1, 1, 5, 1, 4, 2, 1, 1, 2, 3]
def baseStart_1723168 : Nat := 118140960795 + 1723168 * 2 ^ 59
def prefixEnd_1723168 : Nat := 4983230072969 + 3 ^ 40 * 1723168 * 2
def baseEnd_1723168 : Nat := 884813432446819330975301

theorem tailTrace_1723168 : CollatzResearch.WordTrace tailWord_1723168 prefixEnd_1723168 884813432446819330975301 := by
  unfold tailWord_1723168
  simp only [CollatzResearch.WordTrace]
  refine ⟨31424550110632052254797079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41899400147509403006396105 31424550110632052254797079)
  ·
    refine ⟨47136825165948078382195619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31424550110632052254797079 47136825165948078382195619)
    ·
      refine ⟨70705237748922117573293429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47136825165948078382195619 70705237748922117573293429)
      ·
        refine ⟨6628616038961448522496259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70705237748922117573293429 6628616038961448522496259)
        ·
          refine ⟨9942924058442172783744389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6628616038961448522496259 9942924058442172783744389)
          ·
            refine ⟨1864298260957907396952073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9942924058442172783744389 1864298260957907396952073)
            ·
              refine ⟨1398223695718430547714055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1864298260957907396952073 1398223695718430547714055)
              ·
                refine ⟨2097335543577645821571083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1398223695718430547714055 2097335543577645821571083)
                ·
                  refine ⟨3146003315366468732356625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2097335543577645821571083 3146003315366468732356625)
                  ·
                    refine ⟨2359502486524851549267469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3146003315366468732356625 2359502486524851549267469)
                    ·
                      refine ⟨884813432446819330975301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2359502486524851549267469 884813432446819330975301)
                      ·
                        rfl

theorem cell23_1723168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_1723168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723168 prefixEnd_1723168 := by exact prefixLift 1723168
  have htrace : WordTrace (prefixWord ++ tailWord_1723168) baseStart_1723168 baseEnd_1723168 := by
    simpa [prefixWord, tailWord_1723168, baseEnd_1723168] using wordTrace_append hprefix tailTrace_1723168
  have hstable : (prefixWord ++ tailWord_1723168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723168).length < 2 ^ (prefixWord ++ tailWord_1723168).sum := by decide
  have hdescent : baseEnd_1723168 < baseStart_1723168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723198 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_1723198 : Nat := 118140960795 + 1723198 * 2 ^ 59
def prefixEnd_1723198 : Nat := 4983230072969 + 3 ^ 40 * 1723198 * 2
def baseEnd_1723198 : Nat := 884828836866454213600163

theorem tailTrace_1723198 : CollatzResearch.WordTrace tailWord_1723198 prefixEnd_1723198 884828836866454213600163 := by
  unfold tailWord_1723198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7856274301394427454148281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41900129607436946422124165 7856274301394427454148281)
  ·
    refine ⟨5892205726045820590611211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7856274301394427454148281 5892205726045820590611211)
    ·
      refine ⟨8838308589068730885916817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5892205726045820590611211 8838308589068730885916817)
      ·
        refine ⟨6628731441801548164437613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8838308589068730885916817 6628731441801548164437613)
        ·
          refine ⟨2485774290675580561664105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6628731441801548164437613 2485774290675580561664105)
          ·
            refine ⟨1864330718006685421248079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2485774290675580561664105 1864330718006685421248079)
            ·
              refine ⟨2796496077010028131872119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864330718006685421248079 2796496077010028131872119)
              ·
                refine ⟨4194744115515042197808179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2796496077010028131872119 4194744115515042197808179)
                ·
                  refine ⟨6292116173272563296712269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4194744115515042197808179 6292116173272563296712269)
                  ·
                    refine ⟨2359543564977211236267101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6292116173272563296712269 2359543564977211236267101)
                    ·
                      refine ⟨884828836866454213600163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2359543564977211236267101 884828836866454213600163)
                      ·
                        rfl

theorem cell23_1723198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_1723198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723198 prefixEnd_1723198 := by exact prefixLift 1723198
  have htrace : WordTrace (prefixWord ++ tailWord_1723198) baseStart_1723198 baseEnd_1723198 := by
    simpa [prefixWord, tailWord_1723198, baseEnd_1723198] using wordTrace_append hprefix tailTrace_1723198
  have hstable : (prefixWord ++ tailWord_1723198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723198).length < 2 ^ (prefixWord ++ tailWord_1723198).sum := by decide
  have hdescent : baseEnd_1723198 < baseStart_1723198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723207 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_1723207 : Nat := 118140960795 + 1723207 * 2 ^ 59
def prefixEnd_1723207 : Nat := 4983230072969 + 3 ^ 40 * 1723207 * 2
def baseEnd_1723207 : Nat := 884833458192344678387621

theorem tailTrace_1723207 : CollatzResearch.WordTrace tailWord_1723207 prefixEnd_1723207 884833458192344678387621 := by
  unfold tailWord_1723207
  simp only [CollatzResearch.WordTrace]
  refine ⟨62850522668122814170263875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41900348445415209446842583 62850522668122814170263875)
  ·
    refine ⟨94275784002184221255395813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62850522668122814170263875 94275784002184221255395813)
    ·
      refine ⟨17676709500409541485386715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94275784002184221255395813 17676709500409541485386715)
      ·
        refine ⟨26515064250614312228080073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17676709500409541485386715 26515064250614312228080073)
        ·
          refine ⟨19886298187960734171060055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26515064250614312228080073 19886298187960734171060055)
          ·
            refine ⟨29829447281941101256590083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19886298187960734171060055 29829447281941101256590083)
            ·
              refine ⟨44744170922911651884885125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29829447281941101256590083 44744170922911651884885125)
              ·
                refine ⟨8389532048045934728415961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44744170922911651884885125 8389532048045934728415961)
                ·
                  refine ⟨6292149036034451046311971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8389532048045934728415961 6292149036034451046311971)
                  ·
                    refine ⟨9438223554051676569467957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6292149036034451046311971 9438223554051676569467957)
                    ·
                      refine ⟨884833458192344678387621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9438223554051676569467957 884833458192344678387621)
                      ·
                        rfl

theorem cell23_1723207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_1723207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723207 prefixEnd_1723207 := by exact prefixLift 1723207
  have htrace : WordTrace (prefixWord ++ tailWord_1723207) baseStart_1723207 baseEnd_1723207 := by
    simpa [prefixWord, tailWord_1723207, baseEnd_1723207] using wordTrace_append hprefix tailTrace_1723207
  have hstable : (prefixWord ++ tailWord_1723207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723207).length < 2 ^ (prefixWord ++ tailWord_1723207).sum := by decide
  have hdescent : baseEnd_1723207 < baseStart_1723207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723221 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 6, 2, 2]
def baseStart_1723221 : Nat := 118140960795 + 1723221 * 2 ^ 59
def prefixEnd_1723221 : Nat := 4983230072969 + 3 ^ 40 * 1723221 * 2
def baseEnd_1723221 : Nat := 884840646921507623612557

theorem tailTrace_1723221 : CollatzResearch.WordTrace tailWord_1723221 prefixEnd_1723221 884840646921507623612557 := by
  unfold tailWord_1723221
  simp only [CollatzResearch.WordTrace]
  refine ⟨62851033290072094561273517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41900688860048063040849011 62851033290072094561273517)
  ·
    refine ⟨23569137483777035460477569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62851033290072094561273517 23569137483777035460477569)
    ·
      refine ⟨17676853112832776595358177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23569137483777035460477569 17676853112832776595358177)
      ·
        refine ⟨13257639834624582446518633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17676853112832776595358177 13257639834624582446518633)
        ·
          refine ⟨9943229875968436834888975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13257639834624582446518633 9943229875968436834888975)
          ·
            refine ⟨14914844813952655252333463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9943229875968436834888975 14914844813952655252333463)
            ·
              refine ⟨22372267220928982878500195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14914844813952655252333463 22372267220928982878500195)
              ·
                refine ⟨33558400831393474317750293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22372267220928982878500195 33558400831393474317750293)
                ·
                  refine ⟨1573050038971569108644545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33558400831393474317750293 1573050038971569108644545)
                  ·
                    refine ⟨1179787529228676831483409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1573050038971569108644545 1179787529228676831483409)
                    ·
                      refine ⟨884840646921507623612557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1179787529228676831483409 884840646921507623612557)
                      ·
                        rfl

theorem cell23_1723221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_1723221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723221 prefixEnd_1723221 := by exact prefixLift 1723221
  have htrace : WordTrace (prefixWord ++ tailWord_1723221) baseStart_1723221 baseEnd_1723221 := by
    simpa [prefixWord, tailWord_1723221, baseEnd_1723221] using wordTrace_append hprefix tailTrace_1723221
  have hstable : (prefixWord ++ tailWord_1723221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723221).length < 2 ^ (prefixWord ++ tailWord_1723221).sum := by decide
  have hdescent : baseEnd_1723221 < baseStart_1723221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723264 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 4, 5, 2]
def baseStart_1723264 : Nat := 118140960795 + 1723264 * 2 ^ 59
def prefixEnd_1723264 : Nat := 4983230072969 + 3 ^ 40 * 1723264 * 2
def baseEnd_1723264 : Nat := 884862726589650955374859

theorem tailTrace_1723264 : CollatzResearch.WordTrace tailWord_1723264 prefixEnd_1723264 884862726589650955374859 := by
  unfold tailWord_1723264
  simp only [CollatzResearch.WordTrace]
  refine ⟨31426300814458156452544423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41901734419277541936725897 31426300814458156452544423)
  ·
    refine ⟨47139451221687234678816635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31426300814458156452544423 47139451221687234678816635)
    ·
      refine ⟨70709176832530852018224953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47139451221687234678816635 70709176832530852018224953)
      ·
        refine ⟨53031882624398139013668715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70709176832530852018224953 53031882624398139013668715)
        ·
          refine ⟨79547823936597208520503073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53031882624398139013668715 79547823936597208520503073)
          ·
            refine ⟨59660867952447906390377305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79547823936597208520503073 59660867952447906390377305)
            ·
              refine ⟨44745650964335929792782979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59660867952447906390377305 44745650964335929792782979)
              ·
                refine ⟨67118476446503894689174469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44745650964335929792782979 67118476446503894689174469)
                ·
                  refine ⟨12584714333719480254220213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67118476446503894689174469 12584714333719480254220213)
                  ·
                    refine ⟨1179816968786201273833145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12584714333719480254220213 1179816968786201273833145)
                    ·
                      refine ⟨884862726589650955374859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1179816968786201273833145 884862726589650955374859)
                      ·
                        rfl

theorem cell23_1723264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4, 5, 2].length) (baseStart_1723264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723264 prefixEnd_1723264 := by exact prefixLift 1723264
  have htrace : WordTrace (prefixWord ++ tailWord_1723264) baseStart_1723264 baseEnd_1723264 := by
    simpa [prefixWord, tailWord_1723264, baseEnd_1723264] using wordTrace_append hprefix tailTrace_1723264
  have hstable : (prefixWord ++ tailWord_1723264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723264).length < 2 ^ (prefixWord ++ tailWord_1723264).sum := by decide
  have hdescent : baseEnd_1723264 < baseStart_1723264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723267 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 7]
def baseStart_1723267 : Nat := 118140960795 + 1723267 * 2 ^ 59
def prefixEnd_1723267 : Nat := 4983230072969 + 3 ^ 40 * 1723267 * 2
def baseEnd_1723267 : Nat := 884864267031614443637345

theorem tailTrace_1723267 : CollatzResearch.WordTrace tailWord_1723267 prefixEnd_1723267 884864267031614443637345 := by
  unfold tailWord_1723267
  simp only [CollatzResearch.WordTrace]
  refine ⟨62852711047905444417448055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41901807365270296278298703 62852711047905444417448055)
  ·
    refine ⟨94279066571858166626172083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62852711047905444417448055 94279066571858166626172083)
    ·
      refine ⟨141418599857787249939258125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94279066571858166626172083 141418599857787249939258125)
      ·
        refine ⟨53031974946670218727221797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141418599857787249939258125 53031974946670218727221797)
        ·
          refine ⟨9943495302500666011354087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53031974946670218727221797 9943495302500666011354087)
          ·
            refine ⟨14915242953750999017031131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9943495302500666011354087 14915242953750999017031131)
            ·
              refine ⟨22372864430626498525546697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14915242953750999017031131 22372864430626498525546697)
              ·
                refine ⟨16779648322969873894160023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22372864430626498525546697 16779648322969873894160023)
                ·
                  refine ⟨25169472484454810841240035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16779648322969873894160023 25169472484454810841240035)
                  ·
                    refine ⟨37754208726682216261860053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25169472484454810841240035 37754208726682216261860053)
                    ·
                      refine ⟨884864267031614443637345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37754208726682216261860053 884864267031614443637345)
                      ·
                        rfl

theorem cell23_1723267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_1723267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723267 prefixEnd_1723267 := by exact prefixLift 1723267
  have htrace : WordTrace (prefixWord ++ tailWord_1723267) baseStart_1723267 baseEnd_1723267 := by
    simpa [prefixWord, tailWord_1723267, baseEnd_1723267] using wordTrace_append hprefix tailTrace_1723267
  have hstable : (prefixWord ++ tailWord_1723267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723267).length < 2 ^ (prefixWord ++ tailWord_1723267).sum := by decide
  have hdescent : baseEnd_1723267 < baseStart_1723267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723284 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_1723284 : Nat := 118140960795 + 1723284 * 2 ^ 59
def prefixEnd_1723284 : Nat := 4983230072969 + 3 ^ 40 * 1723284 * 2
def baseEnd_1723284 : Nat := 884872996202740877124767

theorem tailTrace_1723284 : CollatzResearch.WordTrace tailWord_1723284 prefixEnd_1723284 884872996202740877124767 := by
  unfold tailWord_1723284
  simp only [CollatzResearch.WordTrace]
  refine ⟨31426665544421928160408453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41902220725895904213877937 31426665544421928160408453)
  ·
    refine ⟨5892499789579111530076585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31426665544421928160408453 5892499789579111530076585)
    ·
      refine ⟨4419374842184333647557439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5892499789579111530076585 4419374842184333647557439)
      ·
        refine ⟨6629062263276500471336159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4419374842184333647557439 6629062263276500471336159)
        ·
          refine ⟨9943593394914750707004239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6629062263276500471336159 9943593394914750707004239)
          ·
            refine ⟨14915390092372126060506359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9943593394914750707004239 14915390092372126060506359)
            ·
              refine ⟨22373085138558189090759539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14915390092372126060506359 22373085138558189090759539)
              ·
                refine ⟨33559627707837283636139309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22373085138558189090759539 33559627707837283636139309)
                ·
                  refine ⟨12584860390438981363552241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33559627707837283636139309 12584860390438981363552241)
                  ·
                    refine ⟨9438645292829236022664181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12584860390438981363552241 9438645292829236022664181)
                    ·
                      refine ⟨884872996202740877124767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9438645292829236022664181 884872996202740877124767)
                      ·
                        rfl

theorem cell23_1723284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_1723284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723284 prefixEnd_1723284 := by exact prefixLift 1723284
  have htrace : WordTrace (prefixWord ++ tailWord_1723284) baseStart_1723284 baseEnd_1723284 := by
    simpa [prefixWord, tailWord_1723284, baseEnd_1723284] using wordTrace_append hprefix tailTrace_1723284
  have hstable : (prefixWord ++ tailWord_1723284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723284).length < 2 ^ (prefixWord ++ tailWord_1723284).sum := by decide
  have hdescent : baseEnd_1723284 < baseStart_1723284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723307 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 6]
def baseStart_1723307 : Nat := 118140960795 + 1723307 * 2 ^ 59
def prefixEnd_1723307 : Nat := 4983230072969 + 3 ^ 40 * 1723307 * 2
def baseEnd_1723307 : Nat := 884884806257794287137161

theorem tailTrace_1723307 : CollatzResearch.WordTrace tailWord_1723307 prefixEnd_1723307 884884806257794287137161 := by
  unfold tailWord_1723307
  simp only [CollatzResearch.WordTrace]
  refine ⟨62854169967760531248904175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41902779978507020832602783 62854169967760531248904175)
  ·
    refine ⟨94281254951640796873356263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62854169967760531248904175 94281254951640796873356263)
    ·
      refine ⟨141421882427461195310034395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94281254951640796873356263 141421882427461195310034395)
      ·
        refine ⟨212132823641191792965051593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141421882427461195310034395 212132823641191792965051593)
        ·
          refine ⟨159099617730893844723788695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212132823641191792965051593 159099617730893844723788695)
          ·
            refine ⟨238649426596340767085683043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159099617730893844723788695 238649426596340767085683043)
            ·
              refine ⟨357974139894511150628524565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238649426596340767085683043 357974139894511150628524565)
              ·
                refine ⟨16780037807555210185712089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 357974139894511150628524565 16780037807555210185712089)
                ·
                  refine ⟨12585028355666407639284067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16780037807555210185712089 12585028355666407639284067)
                  ·
                    refine ⟨18877542533499611458926101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12585028355666407639284067 18877542533499611458926101)
                    ·
                      refine ⟨884884806257794287137161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18877542533499611458926101 884884806257794287137161)
                      ·
                        rfl

theorem cell23_1723307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 6].length) (baseStart_1723307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723307 prefixEnd_1723307 := by exact prefixLift 1723307
  have htrace : WordTrace (prefixWord ++ tailWord_1723307) baseStart_1723307 baseEnd_1723307 := by
    simpa [prefixWord, tailWord_1723307, baseEnd_1723307] using wordTrace_append hprefix tailTrace_1723307
  have hstable : (prefixWord ++ tailWord_1723307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723307).length < 2 ^ (prefixWord ++ tailWord_1723307).sum := by decide
  have hdescent : baseEnd_1723307 < baseStart_1723307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723321 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 3, 4]
def baseStart_1723321 : Nat := 118140960795 + 1723321 * 2 ^ 59
def prefixEnd_1723321 : Nat := 4983230072969 + 3 ^ 40 * 1723321 * 2
def baseEnd_1723321 : Nat := 294963998328985744120699

theorem tailTrace_1723321 : CollatzResearch.WordTrace tailWord_1723321 prefixEnd_1723321 294963998328985744120699 := by
  unfold tailWord_1723321
  simp only [CollatzResearch.WordTrace]
  refine ⟨62854680589709811639913817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41903120393139874426609211 62854680589709811639913817)
  ·
    refine ⟨47141010442282358729935363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62854680589709811639913817 47141010442282358729935363)
    ·
      refine ⟨70711515663423538094903045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47141010442282358729935363 70711515663423538094903045)
      ·
        refine ⟨13258409186891913392794321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70711515663423538094903045 13258409186891913392794321)
        ·
          refine ⟨9943806890168935044595741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13258409186891913392794321 9943806890168935044595741)
          ·
            refine ⟨3728927583813350641723403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9943806890168935044595741 3728927583813350641723403)
            ·
              refine ⟨5593391375720025962585105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3728927583813350641723403 5593391375720025962585105)
              ·
                refine ⟨4195043531790019471938829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5593391375720025962585105 4195043531790019471938829)
                ·
                  refine ⟨1573141324421257301977061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4195043531790019471938829 1573141324421257301977061)
                  ·
                    refine ⟨294963998328985744120699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1573141324421257301977061 294963998328985744120699)
                    ·
                      rfl

theorem cell23_1723321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 4].length) (baseStart_1723321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723321 prefixEnd_1723321 := by exact prefixLift 1723321
  have htrace : WordTrace (prefixWord ++ tailWord_1723321) baseStart_1723321 baseEnd_1723321 := by
    simpa [prefixWord, tailWord_1723321, baseEnd_1723321] using wordTrace_append hprefix tailTrace_1723321
  have hstable : (prefixWord ++ tailWord_1723321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723321).length < 2 ^ (prefixWord ++ tailWord_1723321).sum := by decide
  have hdescent : baseEnd_1723321 < baseStart_1723321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723337 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 8]
def baseStart_1723337 : Nat := 118140960795 + 1723337 * 2 ^ 59
def prefixEnd_1723337 : Nat := 4983230072969 + 3 ^ 40 * 1723337 * 2
def baseEnd_1723337 : Nat := 884900210677429169762023

theorem tailTrace_1723337 : CollatzResearch.WordTrace tailWord_1723337 prefixEnd_1723337 884900210677429169762023 := by
  unfold tailWord_1723337
  simp only [CollatzResearch.WordTrace]
  refine ⟨62855264157651846372496265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41903509438434564248330843 62855264157651846372496265)
  ·
    refine ⟨47141448118238884779372199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62855264157651846372496265 47141448118238884779372199)
    ·
      refine ⟨70712172177358327169058299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47141448118238884779372199 70712172177358327169058299)
      ·
        refine ⟨106068258266037490753587449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70712172177358327169058299 106068258266037490753587449)
        ·
          refine ⟨79551193699528118065190587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106068258266037490753587449 79551193699528118065190587)
          ·
            refine ⟨119326790549292177097785881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79551193699528118065190587 119326790549292177097785881)
            ·
              refine ⟨89495092911969132823339411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119326790549292177097785881 89495092911969132823339411)
              ·
                refine ⟨134242639367953699235009117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89495092911969132823339411 134242639367953699235009117)
                ·
                  refine ⟨50340989762982637213128419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134242639367953699235009117 50340989762982637213128419)
                  ·
                    refine ⟨75511484644473955819692629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50340989762982637213128419 75511484644473955819692629)
                    ·
                      refine ⟨884900210677429169762023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 75511484644473955819692629 884900210677429169762023)
                      ·
                        rfl

theorem cell23_1723337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_1723337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723337 prefixEnd_1723337 := by exact prefixLift 1723337
  have htrace : WordTrace (prefixWord ++ tailWord_1723337) baseStart_1723337 baseEnd_1723337 := by
    simpa [prefixWord, tailWord_1723337, baseEnd_1723337] using wordTrace_append hprefix tailTrace_1723337
  have hstable : (prefixWord ++ tailWord_1723337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723337).length < 2 ^ (prefixWord ++ tailWord_1723337).sum := by decide
  have hdescent : baseEnd_1723337 < baseStart_1723337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723354 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6]
def baseStart_1723354 : Nat := 118140960795 + 1723354 * 2 ^ 59
def prefixEnd_1723354 : Nat := 4983230072969 + 3 ^ 40 * 1723354 * 2
def baseEnd_1723354 : Nat := 884908939848555603249445

theorem tailTrace_1723354 : CollatzResearch.WordTrace tailWord_1723354 prefixEnd_1723354 884908939848555603249445 := by
  unfold tailWord_1723354
  simp only [CollatzResearch.WordTrace]
  refine ⟨15713971049647564568966279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41903922799060172183910077 15713971049647564568966279)
  ·
    refine ⟨23570956574471346853449419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15713971049647564568966279 23570956574471346853449419)
    ·
      refine ⟨35356434861707020280174129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23570956574471346853449419 35356434861707020280174129)
      ·
        refine ⟨26517326146280265210130597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35356434861707020280174129 26517326146280265210130597)
        ·
          refine ⟨4971998652427549726899487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26517326146280265210130597 4971998652427549726899487)
          ·
            refine ⟨7457997978641324590349231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4971998652427549726899487 7457997978641324590349231)
            ·
              refine ⟨11186996967961986885523847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7457997978641324590349231 11186996967961986885523847)
              ·
                refine ⟨16780495451942980328285771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11186996967961986885523847 16780495451942980328285771)
                ·
                  refine ⟨25170743177914470492428657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16780495451942980328285771 25170743177914470492428657)
                  ·
                    refine ⟨18878057383435852869321493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25170743177914470492428657 18878057383435852869321493)
                    ·
                      refine ⟨884908939848555603249445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18878057383435852869321493 884908939848555603249445)
                      ·
                        rfl

theorem cell23_1723354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_1723354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723354 prefixEnd_1723354 := by exact prefixLift 1723354
  have htrace : WordTrace (prefixWord ++ tailWord_1723354) baseStart_1723354 baseEnd_1723354 := by
    simpa [prefixWord, tailWord_1723354, baseEnd_1723354] using wordTrace_append hprefix tailTrace_1723354
  have hstable : (prefixWord ++ tailWord_1723354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723354).length < 2 ^ (prefixWord ++ tailWord_1723354).sum := by decide
  have hdescent : baseEnd_1723354 < baseStart_1723354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723364 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 3, 5]
def baseStart_1723364 : Nat := 118140960795 + 1723364 * 2 ^ 59
def prefixEnd_1723364 : Nat := 4983230072969 + 3 ^ 40 * 1723364 * 2
def baseEnd_1723364 : Nat := 294971358218366854708133

theorem tailTrace_1723364 : CollatzResearch.WordTrace tailWord_1723364 prefixEnd_1723364 294971358218366854708133 := by
  unfold tailWord_1723364
  simp only [CollatzResearch.WordTrace]
  refine ⟨31428124464277014991864573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41904165952369353322486097 31428124464277014991864573)
  ·
    refine ⟨11785546674103880621949215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31428124464277014991864573 11785546674103880621949215)
    ·
      refine ⟨17678320011155820932923823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11785546674103880621949215 17678320011155820932923823)
      ·
        refine ⟨26517480016733731399385735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17678320011155820932923823 26517480016733731399385735)
        ·
          refine ⟨39776220025100597099078603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26517480016733731399385735 39776220025100597099078603)
          ·
            refine ⟨59664330037650895648617905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39776220025100597099078603 59664330037650895648617905)
            ·
              refine ⟨44748247528238171736463429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59664330037650895648617905 44748247528238171736463429)
              ·
                refine ⟨8390296411544657200586893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44748247528238171736463429 8390296411544657200586893)
                ·
                  refine ⟨3146361154329246450220085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8390296411544657200586893 3146361154329246450220085)
                  ·
                    refine ⟨294971358218366854708133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3146361154329246450220085 294971358218366854708133)
                    ·
                      rfl

theorem cell23_1723364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_1723364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723364 prefixEnd_1723364 := by exact prefixLift 1723364
  have htrace : WordTrace (prefixWord ++ tailWord_1723364) baseStart_1723364 baseEnd_1723364 := by
    simpa [prefixWord, tailWord_1723364, baseEnd_1723364] using wordTrace_append hprefix tailTrace_1723364
  have hstable : (prefixWord ++ tailWord_1723364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723364).length < 2 ^ (prefixWord ++ tailWord_1723364).sum := by decide
  have hdescent : baseEnd_1723364 < baseStart_1723364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723411 : List Nat := [1, 1, 1, 2, 1, 4, 1, 6, 2, 4]
def baseStart_1723411 : Nat := 118140960795 + 1723411 * 2 ^ 59
def prefixEnd_1723411 : Nat := 4983230072969 + 3 ^ 40 * 1723411 * 2
def baseEnd_1723411 : Nat := 294979402748620626745561

theorem tailTrace_1723411 : CollatzResearch.WordTrace tailWord_1723411 prefixEnd_1723411 294979402748620626745561 := by
  unfold tailWord_1723411
  simp only [CollatzResearch.WordTrace]
  refine ⟨62857963159383757010690087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41905308772922504673793391 62857963159383757010690087)
  ·
    refine ⟨94286944739075635516035131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62857963159383757010690087 94286944739075635516035131)
    ·
      refine ⟨141430417108613453274052697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94286944739075635516035131 141430417108613453274052697)
      ·
        refine ⟨106072812831460089955539523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141430417108613453274052697 106072812831460089955539523)
        ·
          refine ⟨159109219247190134933309285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106072812831460089955539523 159109219247190134933309285)
          ·
            refine ⟨29832978608848150299995491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159109219247190134933309285 29832978608848150299995491)
            ·
              refine ⟨44749467913272225449993237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29832978608848150299995491 44749467913272225449993237)
              ·
                refine ⟨2097631308434635567968433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44749467913272225449993237 2097631308434635567968433)
                ·
                  refine ⟨1573223481325976675976325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2097631308434635567968433 1573223481325976675976325)
                  ·
                    refine ⟨294979402748620626745561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1573223481325976675976325 294979402748620626745561)
                    ·
                      rfl

theorem cell23_1723411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 4].length) (baseStart_1723411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723411 prefixEnd_1723411 := by exact prefixLift 1723411
  have htrace : WordTrace (prefixWord ++ tailWord_1723411) baseStart_1723411 baseEnd_1723411 := by
    simpa [prefixWord, tailWord_1723411, baseEnd_1723411] using wordTrace_append hprefix tailTrace_1723411
  have hstable : (prefixWord ++ tailWord_1723411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723411).length < 2 ^ (prefixWord ++ tailWord_1723411).sum := by decide
  have hdescent : baseEnd_1723411 < baseStart_1723411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723438 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_1723438 : Nat := 118140960795 + 1723438 * 2 ^ 59
def prefixEnd_1723438 : Nat := 4983230072969 + 3 ^ 40 * 1723438 * 2
def baseEnd_1723438 : Nat := 884952072223533274599059

theorem tailTrace_1723438 : CollatzResearch.WordTrace tailWord_1723438 prefixEnd_1723438 884952072223533274599059 := by
  unfold tailWord_1723438
  simp only [CollatzResearch.WordTrace]
  refine ⟨7857368491285742577740371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41905965286857293747948645 7857368491285742577740371)
  ·
    refine ⟨11786052736928613866610557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7857368491285742577740371 11786052736928613866610557)
    ·
      refine ⟨4419769776348230199978959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11786052736928613866610557 4419769776348230199978959)
      ·
        refine ⟨6629654664522345299968439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4419769776348230199978959 6629654664522345299968439)
        ·
          refine ⟨9944481996783517949952659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6629654664522345299968439 9944481996783517949952659)
          ·
            refine ⟨14916722995175276924928989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9944481996783517949952659 14916722995175276924928989)
            ·
              refine ⟨5593771123190728846848371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14916722995175276924928989 5593771123190728846848371)
              ·
                refine ⟨8390656684786093270272557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5593771123190728846848371 8390656684786093270272557)
                ·
                  refine ⟨3146496256794784976352209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8390656684786093270272557 3146496256794784976352209)
                  ·
                    refine ⟨2359872192596088732264157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3146496256794784976352209 2359872192596088732264157)
                    ·
                      refine ⟨884952072223533274599059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2359872192596088732264157 884952072223533274599059)
                      ·
                        rfl

theorem cell23_1723438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_1723438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723438 prefixEnd_1723438 := by exact prefixLift 1723438
  have htrace : WordTrace (prefixWord ++ tailWord_1723438) baseStart_1723438 baseEnd_1723438 := by
    simpa [prefixWord, tailWord_1723438, baseEnd_1723438] using wordTrace_append hprefix tailTrace_1723438
  have hstable : (prefixWord ++ tailWord_1723438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723438).length < 2 ^ (prefixWord ++ tailWord_1723438).sum := by decide
  have hdescent : baseEnd_1723438 < baseStart_1723438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723462 : List Nat := [6, 1, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_1723462 : Nat := 118140960795 + 1723462 * 2 ^ 59
def prefixEnd_1723462 : Nat := 4983230072969 + 3 ^ 40 * 1723462 * 2
def baseEnd_1723462 : Nat := 294988131919747060232983

theorem tailTrace_1723462 : CollatzResearch.WordTrace tailWord_1723462 prefixEnd_1723462 294988131919747060232983 := by
  unfold tailWord_1723462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1964369477568718522524895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41906548854799328480531093 1964369477568718522524895)
  ·
    refine ⟨2946554216353077783787343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1964369477568718522524895 2946554216353077783787343)
    ·
      refine ⟨4419831324529616675681015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2946554216353077783787343 4419831324529616675681015)
      ·
        refine ⟨6629746986794425013521523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4419831324529616675681015 6629746986794425013521523)
        ·
          refine ⟨9944620480191637520282285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6629746986794425013521523 9944620480191637520282285)
          ·
            refine ⟨3729232680071864070105857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9944620480191637520282285 3729232680071864070105857)
            ·
              refine ⟨2796924510053898052579393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3729232680071864070105857 2796924510053898052579393)
              ·
                refine ⟨2097693382540423539434545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2796924510053898052579393 2097693382540423539434545)
                ·
                  refine ⟨1573270036905317654575909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2097693382540423539434545 1573270036905317654575909)
                  ·
                    refine ⟨294988131919747060232983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1573270036905317654575909 294988131919747060232983)
                    ·
                      rfl

theorem cell23_1723462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_1723462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723462 prefixEnd_1723462 := by exact prefixLift 1723462
  have htrace : WordTrace (prefixWord ++ tailWord_1723462) baseStart_1723462 baseEnd_1723462 := by
    simpa [prefixWord, tailWord_1723462, baseEnd_1723462] using wordTrace_append hprefix tailTrace_1723462
  have hstable : (prefixWord ++ tailWord_1723462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723462).length < 2 ^ (prefixWord ++ tailWord_1723462).sum := by decide
  have hdescent : baseEnd_1723462 < baseStart_1723462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723469 : List Nat := [1, 6, 1, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_1723469 : Nat := 118140960795 + 1723469 * 2 ^ 59
def prefixEnd_1723469 : Nat := 4983230072969 + 3 ^ 40 * 1723469 * 2
def baseEnd_1723469 : Nat := 884967990123822653311417

theorem tailTrace_1723469 : CollatzResearch.WordTrace tailWord_1723469 prefixEnd_1723469 884967990123822653311417 := by
  unfold tailWord_1723469
  simp only [CollatzResearch.WordTrace]
  refine ⟨62860078593173632916301461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41906719062115755277534307 62860078593173632916301461)
  ·
    refine ⟨2946566184055014042951631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62860078593173632916301461 2946566184055014042951631)
    ·
      refine ⟨4419849276082521064427447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2946566184055014042951631 4419849276082521064427447)
      ·
        refine ⟨6629773914123781596641171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4419849276082521064427447 6629773914123781596641171)
        ·
          refine ⟨9944660871185672394961757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6629773914123781596641171 9944660871185672394961757)
          ·
            refine ⟨3729247826694627148110659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9944660871185672394961757 3729247826694627148110659)
            ·
              refine ⟨5593871740041940722165989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3729247826694627148110659 5593871740041940722165989)
              ·
                refine ⟨1048850951257863885406123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5593871740041940722165989 1048850951257863885406123)
                ·
                  refine ⟨1573276426886795828109185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1048850951257863885406123 1573276426886795828109185)
                  ·
                    refine ⟨1179957320165096871081889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1573276426886795828109185 1179957320165096871081889)
                    ·
                      refine ⟨884967990123822653311417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1179957320165096871081889 884967990123822653311417)
                      ·
                        rfl

theorem cell23_1723469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_1723469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723469 prefixEnd_1723469 := by exact prefixLift 1723469
  have htrace : WordTrace (prefixWord ++ tailWord_1723469) baseStart_1723469 baseEnd_1723469 := by
    simpa [prefixWord, tailWord_1723469, baseEnd_1723469] using wordTrace_append hprefix tailTrace_1723469
  have hstable : (prefixWord ++ tailWord_1723469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723469).length < 2 ^ (prefixWord ++ tailWord_1723469).sum := by decide
  have hdescent : baseEnd_1723469 < baseStart_1723469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723538 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1723538 : Nat := 118140960795 + 1723538 * 2 ^ 59
def prefixEnd_1723538 : Nat := 4983230072969 + 3 ^ 40 * 1723538 * 2
def baseEnd_1723538 : Nat := 885003420288982883348599

theorem tailTrace_1723538 : CollatzResearch.WordTrace tailWord_1723538 prefixEnd_1723538 885003420288982883348599 := by
  unfold tailWord_1723538
  simp only [CollatzResearch.WordTrace]
  refine ⟨15715648807480914425140817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41908396819949105133708845 15715648807480914425140817)
  ·
    refine ⟨11786736605610685818855613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15715648807480914425140817 11786736605610685818855613)
    ·
      refine ⟨4420026227104007182070855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11786736605610685818855613 4420026227104007182070855)
      ·
        refine ⟨6630039340656010773106283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4420026227104007182070855 6630039340656010773106283)
        ·
          refine ⟨9945059010984016159659425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6630039340656010773106283 9945059010984016159659425)
          ·
            refine ⟨7458794258238012119744569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9945059010984016159659425 7458794258238012119744569)
            ·
              refine ⟨5594095693678509089808427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7458794258238012119744569 5594095693678509089808427)
              ·
                refine ⟨8391143540517763634712641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5594095693678509089808427 8391143540517763634712641)
                ·
                  refine ⟨6293357655388322726034481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8391143540517763634712641 6293357655388322726034481)
                  ·
                    refine ⟨4720018241541242044525861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6293357655388322726034481 4720018241541242044525861)
                    ·
                      refine ⟨885003420288982883348599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4720018241541242044525861 885003420288982883348599)
                      ·
                        rfl

theorem cell23_1723538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1723538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723538 prefixEnd_1723538 := by exact prefixLift 1723538
  have htrace : WordTrace (prefixWord ++ tailWord_1723538) baseStart_1723538 baseEnd_1723538 := by
    simpa [prefixWord, tailWord_1723538, baseEnd_1723538] using wordTrace_append hprefix tailTrace_1723538
  have hstable : (prefixWord ++ tailWord_1723538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723538).length < 2 ^ (prefixWord ++ tailWord_1723538).sum := by decide
  have hdescent : baseEnd_1723538 < baseStart_1723538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723541 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 1, 5, 3]
def baseStart_1723541 : Nat := 118140960795 + 1723541 * 2 ^ 59
def prefixEnd_1723541 : Nat := 4983230072969 + 3 ^ 40 * 1723541 * 2
def baseEnd_1723541 : Nat := 885004960730946371611085

theorem tailTrace_1723541 : CollatzResearch.WordTrace tailWord_1723541 prefixEnd_1723541 885004960730946371611085 := by
  unfold tailWord_1723541
  simp only [CollatzResearch.WordTrace]
  refine ⟨62862704648912789212922477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41908469765941859475281651 62862704648912789212922477)
  ·
    refine ⟨23573514243342295954845929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62862704648912789212922477 23573514243342295954845929)
    ·
      refine ⟨17680135682506721966134447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23573514243342295954845929 17680135682506721966134447)
      ·
        refine ⟨26520203523760082949201671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17680135682506721966134447 26520203523760082949201671)
        ·
          refine ⟨39780305285640124423802507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26520203523760082949201671 39780305285640124423802507)
          ·
            refine ⟨59670457928460186635703761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39780305285640124423802507 59670457928460186635703761)
            ·
              refine ⟨44752843446345139976777821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59670457928460186635703761 44752843446345139976777821)
              ·
                refine ⟨16782316292379427491291683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44752843446345139976777821 16782316292379427491291683)
                ·
                  refine ⟨25173474438569141236937525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16782316292379427491291683 25173474438569141236937525)
                  ·
                    refine ⟨2360013228615856990962893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25173474438569141236937525 2360013228615856990962893)
                    ·
                      refine ⟨885004960730946371611085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2360013228615856990962893 885004960730946371611085)
                      ·
                        rfl

theorem cell23_1723541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_1723541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723541 prefixEnd_1723541 := by exact prefixLift 1723541
  have htrace : WordTrace (prefixWord ++ tailWord_1723541) baseStart_1723541 baseEnd_1723541 := by
    simpa [prefixWord, tailWord_1723541, baseEnd_1723541] using wordTrace_append hprefix tailTrace_1723541
  have hstable : (prefixWord ++ tailWord_1723541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723541).length < 2 ^ (prefixWord ++ tailWord_1723541).sum := by decide
  have hdescent : baseEnd_1723541 < baseStart_1723541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723582 : List Nat := [4, 2, 1, 1, 3, 2, 3, 2, 5]
def baseStart_1723582 : Nat := 118140960795 + 1723582 * 2 ^ 59
def prefixEnd_1723582 : Nat := 4983230072969 + 3 ^ 40 * 1723582 * 2
def baseEnd_1723582 : Nat := 98336223715308967910933

theorem tailTrace_1723582 : CollatzResearch.WordTrace tailWord_1723582 prefixEnd_1723582 98336223715308967910933 := by
  unfold tailWord_1723582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7858025005220531651895625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41909466694509502143443333 7858025005220531651895625)
  ·
    refine ⟨5893518753915398738921719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7858025005220531651895625 5893518753915398738921719)
    ·
      refine ⟨8840278130873098108382579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5893518753915398738921719 8840278130873098108382579)
      ·
        refine ⟨13260417196309647162573869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8840278130873098108382579 13260417196309647162573869)
        ·
          refine ⟨4972656448616117685965201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13260417196309647162573869 4972656448616117685965201)
          ·
            refine ⟨3729492336462088264473901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4972656448616117685965201 3729492336462088264473901)
            ·
              refine ⟨1398559626173283099177713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3729492336462088264473901 1398559626173283099177713)
              ·
                refine ⟨1048919719629962324383285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1398559626173283099177713 1048919719629962324383285)
                ·
                  refine ⟨98336223715308967910933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1048919719629962324383285 98336223715308967910933)
                  ·
                    rfl

theorem cell23_1723582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_1723582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723582 prefixEnd_1723582 := by exact prefixLift 1723582
  have htrace : WordTrace (prefixWord ++ tailWord_1723582) baseStart_1723582 baseEnd_1723582 := by
    simpa [prefixWord, tailWord_1723582, baseEnd_1723582] using wordTrace_append hprefix tailTrace_1723582
  have hstable : (prefixWord ++ tailWord_1723582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723582).length < 2 ^ (prefixWord ++ tailWord_1723582).sum := by decide
  have hdescent : baseEnd_1723582 < baseStart_1723582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723641 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 1, 2, 6]
def baseStart_1723641 : Nat := 118140960795 + 1723641 * 2 ^ 59
def prefixEnd_1723641 : Nat := 4983230072969 + 3 ^ 40 * 1723641 * 2
def baseEnd_1723641 : Nat := 885056308796395980360625

theorem tailTrace_1723641 : CollatzResearch.WordTrace tailWord_1723641 prefixEnd_1723641 885056308796395980360625 := by
  unfold tailWord_1723641
  simp only [CollatzResearch.WordTrace]
  refine ⟨62866351948550506291562777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41910901299033670861041851 62866351948550506291562777)
  ·
    refine ⟨47149763961412879718672083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62866351948550506291562777 47149763961412879718672083)
    ·
      refine ⟨70724645942119319578008125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47149763961412879718672083 70724645942119319578008125)
      ·
        refine ⟨26521742228294744841753047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70724645942119319578008125 26521742228294744841753047)
        ·
          refine ⟨39782613342442117262629571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26521742228294744841753047 39782613342442117262629571)
          ·
            refine ⟨59673920013663175893944357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39782613342442117262629571 59673920013663175893944357)
            ·
              refine ⟨11188860002561845480114567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59673920013663175893944357 11188860002561845480114567)
              ·
                refine ⟨16783290003842768220171851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11188860002561845480114567 16783290003842768220171851)
                ·
                  refine ⟨25174935005764152330257777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16783290003842768220171851 25174935005764152330257777)
                  ·
                    refine ⟨18881201254323114247693333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25174935005764152330257777 18881201254323114247693333)
                    ·
                      refine ⟨885056308796395980360625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18881201254323114247693333 885056308796395980360625)
                      ·
                        rfl

theorem cell23_1723641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_1723641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723641 prefixEnd_1723641 := by exact prefixLift 1723641
  have htrace : WordTrace (prefixWord ++ tailWord_1723641) baseStart_1723641 baseEnd_1723641 := by
    simpa [prefixWord, tailWord_1723641, baseEnd_1723641] using wordTrace_append hprefix tailTrace_1723641
  have hstable : (prefixWord ++ tailWord_1723641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723641).length < 2 ^ (prefixWord ++ tailWord_1723641).sum := by decide
  have hdescent : baseEnd_1723641 < baseStart_1723641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723665 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 3, 1, 3]
def baseStart_1723665 : Nat := 118140960795 + 1723665 * 2 ^ 59
def prefixEnd_1723665 : Nat := 4983230072969 + 3 ^ 40 * 1723665 * 2
def baseEnd_1723665 : Nat := 885068632332103886460515

theorem tailTrace_1723665 : CollatzResearch.WordTrace tailWord_1723665 prefixEnd_1723665 885068632332103886460515 := by
  unfold tailWord_1723665
  simp only [CollatzResearch.WordTrace]
  refine ⟨62867227300463558390436449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41911484866975705593624299 62867227300463558390436449)
  ·
    refine ⟨47150420475347668792827337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62867227300463558390436449 47150420475347668792827337)
    ·
      refine ⟨35362815356510751594620503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47150420475347668792827337 35362815356510751594620503)
      ·
        refine ⟨53044223034766127391930755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35362815356510751594620503 53044223034766127391930755)
        ·
          refine ⟨79566334552149191087896133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53044223034766127391930755 79566334552149191087896133)
          ·
            refine ⟨14918687728527973328980525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79566334552149191087896133 14918687728527973328980525)
            ·
              refine ⟨5594507898197989998367697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14918687728527973328980525 5594507898197989998367697)
              ·
                refine ⟨4195880923648492498775773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5594507898197989998367697 4195880923648492498775773)
                ·
                  refine ⟨1573455346368184687040915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4195880923648492498775773 1573455346368184687040915)
                  ·
                    refine ⟨2360183019552277030561373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1573455346368184687040915 2360183019552277030561373)
                    ·
                      refine ⟨885068632332103886460515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2360183019552277030561373 885068632332103886460515)
                      ·
                        rfl

theorem cell23_1723665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 1, 3].length) (baseStart_1723665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723665 prefixEnd_1723665 := by exact prefixLift 1723665
  have htrace : WordTrace (prefixWord ++ tailWord_1723665) baseStart_1723665 baseEnd_1723665 := by
    simpa [prefixWord, tailWord_1723665, baseEnd_1723665] using wordTrace_append hprefix tailTrace_1723665
  have hstable : (prefixWord ++ tailWord_1723665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723665).length < 2 ^ (prefixWord ++ tailWord_1723665).sum := by decide
  have hdescent : baseEnd_1723665 < baseStart_1723665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723666 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_1723666 : Nat := 118140960795 + 1723666 * 2 ^ 59
def prefixEnd_1723666 : Nat := 4983230072969 + 3 ^ 40 * 1723666 * 2
def baseEnd_1723666 : Nat := 885069145812758382548011

theorem tailTrace_1723666 : CollatzResearch.WordTrace tailWord_1723666 prefixEnd_1723666 885069145812758382548011 := by
  unfold tailWord_1723666
  simp only [CollatzResearch.WordTrace]
  refine ⟨15716815943364983890305713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41911509182306623707481901 15716815943364983890305713)
  ·
    refine ⟨11787611957523737917729285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15716815943364983890305713 11787611957523737917729285)
    ·
      refine ⟨2210177242035700859574241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11787611957523737917729285 2210177242035700859574241)
      ·
        refine ⟨1657632931526775644680681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2210177242035700859574241 1657632931526775644680681)
        ·
          refine ⟨1243224698645081733510511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1657632931526775644680681 1243224698645081733510511)
          ·
            refine ⟨1864837047967622600265767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243224698645081733510511 1864837047967622600265767)
            ·
              refine ⟨2797255571951433900398651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864837047967622600265767 2797255571951433900398651)
              ·
                refine ⟨4195883357927150850597977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2797255571951433900398651 4195883357927150850597977)
                ·
                  refine ⟨3146912518445363137948483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4195883357927150850597977 3146912518445363137948483)
                  ·
                    refine ⟨4720368777668044706922725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3146912518445363137948483 4720368777668044706922725)
                    ·
                      refine ⟨885069145812758382548011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4720368777668044706922725 885069145812758382548011)
                      ·
                        rfl

theorem cell23_1723666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_1723666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723666 prefixEnd_1723666 := by exact prefixLift 1723666
  have htrace : WordTrace (prefixWord ++ tailWord_1723666) baseStart_1723666 baseEnd_1723666 := by
    simpa [prefixWord, tailWord_1723666, baseEnd_1723666] using wordTrace_append hprefix tailTrace_1723666
  have hstable : (prefixWord ++ tailWord_1723666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723666).length < 2 ^ (prefixWord ++ tailWord_1723666).sum := by decide
  have hdescent : baseEnd_1723666 < baseStart_1723666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723685 : List Nat := [1, 3, 1, 2, 4, 2, 1, 3, 1, 5]
def baseStart_1723685 : Nat := 118140960795 + 1723685 * 2 ^ 59
def prefixEnd_1723685 : Nat := 4983230072969 + 3 ^ 40 * 1723685 * 2
def baseEnd_1723685 : Nat := 295026300648397936070141

theorem tailTrace_1723685 : CollatzResearch.WordTrace tailWord_1723685 prefixEnd_1723685 295026300648397936070141 := by
  unfold tailWord_1723685
  simp only [CollatzResearch.WordTrace]
  refine ⟨62867956760391101806164509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41911971173594067870776339 62867956760391101806164509)
  ·
    refine ⟨23575483785146663177311691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62867956760391101806164509 23575483785146663177311691)
    ·
      refine ⟨35363225677719994765967537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23575483785146663177311691 35363225677719994765967537)
      ·
        refine ⟨26522419258289996074475653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35363225677719994765967537 26522419258289996074475653)
        ·
          refine ⟨4972953610929374263964185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26522419258289996074475653 4972953610929374263964185)
          ·
            refine ⟨3729715208197030697973139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4972953610929374263964185 3729715208197030697973139)
            ·
              refine ⟨5594572812295546046959709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3729715208197030697973139 5594572812295546046959709)
              ·
                refine ⟨2097964804610829767609891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5594572812295546046959709 2097964804610829767609891)
                ·
                  refine ⟨3146947206916244651414837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2097964804610829767609891 3146947206916244651414837)
                  ·
                    refine ⟨295026300648397936070141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3146947206916244651414837 295026300648397936070141)
                    ·
                      rfl

theorem cell23_1723685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_1723685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723685 prefixEnd_1723685 := by exact prefixLift 1723685
  have htrace : WordTrace (prefixWord ++ tailWord_1723685) baseStart_1723685 baseEnd_1723685 := by
    simpa [prefixWord, tailWord_1723685, baseEnd_1723685] using wordTrace_append hprefix tailTrace_1723685
  have hstable : (prefixWord ++ tailWord_1723685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723685).length < 2 ^ (prefixWord ++ tailWord_1723685).sum := by decide
  have hdescent : baseEnd_1723685 < baseStart_1723685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723708 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_1723708 : Nat := 118140960795 + 1723708 * 2 ^ 59
def prefixEnd_1723708 : Nat := 4983230072969 + 3 ^ 40 * 1723708 * 2
def baseEnd_1723708 : Nat := 885090712000247218222817

theorem tailTrace_1723708 : CollatzResearch.WordTrace tailWord_1723708 prefixEnd_1723708 885090712000247218222817 := by
  unfold tailWord_1723708
  simp only [CollatzResearch.WordTrace]
  refine ⟨31434397819653888367125889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41912530426205184489501185 31434397819653888367125889)
  ·
    refine ⟨23575798364740416275344417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31434397819653888367125889 23575798364740416275344417)
    ·
      refine ⟨17681848773555312206508313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23575798364740416275344417 17681848773555312206508313)
      ·
        refine ⟨13261386580166484154881235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17681848773555312206508313 13261386580166484154881235)
        ·
          refine ⟨19892079870249726232321853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13261386580166484154881235 19892079870249726232321853)
          ·
            refine ⟨7459529951343647337120695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19892079870249726232321853 7459529951343647337120695)
            ·
              refine ⟨11189294927015471005681043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7459529951343647337120695 11189294927015471005681043)
              ·
                refine ⟨16783942390523206508521565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11189294927015471005681043 16783942390523206508521565)
                ·
                  refine ⟨6293978396446202440695587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16783942390523206508521565 6293978396446202440695587)
                  ·
                    refine ⟨9440967594669303661043381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6293978396446202440695587 9440967594669303661043381)
                    ·
                      refine ⟨885090712000247218222817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9440967594669303661043381 885090712000247218222817)
                      ·
                        rfl

theorem cell23_1723708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_1723708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723708 prefixEnd_1723708 := by exact prefixLift 1723708
  have htrace : WordTrace (prefixWord ++ tailWord_1723708) baseStart_1723708 baseEnd_1723708 := by
    simpa [prefixWord, tailWord_1723708, baseEnd_1723708] using wordTrace_append hprefix tailTrace_1723708
  have hstable : (prefixWord ++ tailWord_1723708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723708).length < 2 ^ (prefixWord ++ tailWord_1723708).sum := by decide
  have hdescent : baseEnd_1723708 < baseStart_1723708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723772 : List Nat := [2, 2, 2, 1, 1, 1, 5, 3, 2, 1, 3]
def baseStart_1723772 : Nat := 118140960795 + 1723772 * 2 ^ 59
def prefixEnd_1723772 : Nat := 4983230072969 + 3 ^ 40 * 1723772 * 2
def baseEnd_1723772 : Nat := 885123574762134967822523

theorem tailTrace_1723772 : CollatzResearch.WordTrace tailWord_1723772 prefixEnd_1723772 885123574762134967822523 := by
  unfold tailWord_1723772
  simp only [CollatzResearch.WordTrace]
  refine ⟨31435564955537957832290785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41914086607383943776387713 31435564955537957832290785)
  ·
    refine ⟨23576673716653468374218089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31435564955537957832290785 23576673716653468374218089)
    ·
      refine ⟨17682505287490101280663567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23576673716653468374218089 17682505287490101280663567)
      ·
        refine ⟨26523757931235151920995351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17682505287490101280663567 26523757931235151920995351)
        ·
          refine ⟨39785636896852727881493027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26523757931235151920995351 39785636896852727881493027)
          ·
            refine ⟨59678455345279091822239541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39785636896852727881493027 59678455345279091822239541)
            ·
              refine ⟨5594855188619914858334957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59678455345279091822239541 5594855188619914858334957)
              ·
                refine ⟨2098070695732468071875609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5594855188619914858334957 2098070695732468071875609)
                ·
                  refine ⟨1573553021799351053906707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2098070695732468071875609 1573553021799351053906707)
                  ·
                    refine ⟨2360329532699026580860061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1573553021799351053906707 2360329532699026580860061)
                    ·
                      refine ⟨885123574762134967822523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2360329532699026580860061 885123574762134967822523)
                      ·
                        rfl

theorem cell23_1723772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_1723772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723772 prefixEnd_1723772 := by exact prefixLift 1723772
  have htrace : WordTrace (prefixWord ++ tailWord_1723772) baseStart_1723772 baseEnd_1723772 := by
    simpa [prefixWord, tailWord_1723772, baseEnd_1723772] using wordTrace_append hprefix tailTrace_1723772
  have hstable : (prefixWord ++ tailWord_1723772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723772).length < 2 ^ (prefixWord ++ tailWord_1723772).sum := by decide
  have hdescent : baseEnd_1723772 < baseStart_1723772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723815 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_1723815 : Nat := 118140960795 + 1723815 * 2 ^ 59
def prefixEnd_1723815 : Nat := 4983230072969 + 3 ^ 40 * 1723815 * 2
def baseEnd_1723815 : Nat := 885145654430278299584825

theorem tailTrace_1723815 : CollatzResearch.WordTrace tailWord_1723815 prefixEnd_1723815 885145654430278299584825 := by
  unfold tailWord_1723815
  simp only [CollatzResearch.WordTrace]
  refine ⟨62872698249920134008396899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41915132166613422672264599 62872698249920134008396899)
  ·
    refine ⟨94309047374880201012595349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62872698249920134008396899 94309047374880201012595349)
    ·
      refine ⟨4420736595697509422465407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94309047374880201012595349 4420736595697509422465407)
      ·
        refine ⟨6631104893546264133698111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4420736595697509422465407 6631104893546264133698111)
        ·
          refine ⟨9946657340319396200547167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6631104893546264133698111 9946657340319396200547167)
          ·
            refine ⟨14919986010479094300820751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9946657340319396200547167 14919986010479094300820751)
            ·
              refine ⟨22379979015718641451231127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14919986010479094300820751 22379979015718641451231127)
              ·
                refine ⟨33569968523577962176846691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22379979015718641451231127 33569968523577962176846691)
                ·
                  refine ⟨50354952785366943265270037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33569968523577962176846691 50354952785366943265270037)
                  ·
                    refine ⟨2360388411814075465559533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50354952785366943265270037 2360388411814075465559533)
                    ·
                      refine ⟨885145654430278299584825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2360388411814075465559533 885145654430278299584825)
                      ·
                        rfl

theorem cell23_1723815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_1723815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723815 prefixEnd_1723815 := by exact prefixLift 1723815
  have htrace : WordTrace (prefixWord ++ tailWord_1723815) baseStart_1723815 baseEnd_1723815 := by
    simpa [prefixWord, tailWord_1723815, baseEnd_1723815] using wordTrace_append hprefix tailTrace_1723815
  have hstable : (prefixWord ++ tailWord_1723815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723815).length < 2 ^ (prefixWord ++ tailWord_1723815).sum := by decide
  have hdescent : baseEnd_1723815 < baseStart_1723815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723825 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 2, 2, 4]
def baseStart_1723825 : Nat := 118140960795 + 1723825 * 2 ^ 59
def prefixEnd_1723825 : Nat := 4983230072969 + 3 ^ 40 * 1723825 * 2
def baseEnd_1723825 : Nat := 885150789236823260459779

theorem tailTrace_1723825 : CollatzResearch.WordTrace tailWord_1723825 prefixEnd_1723825 885150789236823260459779 := by
  unfold tailWord_1723825
  simp only [CollatzResearch.WordTrace]
  refine ⟨62873062979883905716260929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41915375319922603810840619 62873062979883905716260929)
  ·
    refine ⟨47154797234912929287195697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62873062979883905716260929 47154797234912929287195697)
    ·
      refine ⟨35366097926184696965396773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47154797234912929287195697 35366097926184696965396773)
      ·
        refine ⟨6631143361159630681011895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35366097926184696965396773 6631143361159630681011895)
        ·
          refine ⟨9946715041739446021517843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6631143361159630681011895 9946715041739446021517843)
          ·
            refine ⟨14920072562609169032276765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9946715041739446021517843 14920072562609169032276765)
            ·
              refine ⟨5595027210978438387103787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14920072562609169032276765 5595027210978438387103787)
              ·
                refine ⟨8392540816467657580655681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5595027210978438387103787 8392540816467657580655681)
                ·
                  refine ⟨6294405612350743185491761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8392540816467657580655681 6294405612350743185491761)
                  ·
                    refine ⟨4720804209263057389118821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6294405612350743185491761 4720804209263057389118821)
                    ·
                      refine ⟨885150789236823260459779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4720804209263057389118821 885150789236823260459779)
                      ·
                        rfl

theorem cell23_1723825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_1723825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723825 prefixEnd_1723825 := by exact prefixLift 1723825
  have htrace : WordTrace (prefixWord ++ tailWord_1723825) baseStart_1723825 baseEnd_1723825 := by
    simpa [prefixWord, tailWord_1723825, baseEnd_1723825] using wordTrace_append hprefix tailTrace_1723825
  have hstable : (prefixWord ++ tailWord_1723825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723825).length < 2 ^ (prefixWord ++ tailWord_1723825).sum := by decide
  have hdescent : baseEnd_1723825 < baseStart_1723825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723829 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 1, 4, 2]
def baseStart_1723829 : Nat := 118140960795 + 1723829 * 2 ^ 59
def prefixEnd_1723829 : Nat := 4983230072969 + 3 ^ 40 * 1723829 * 2
def baseEnd_1723829 : Nat := 885152843159441244809761

theorem tailTrace_1723829 : CollatzResearch.WordTrace tailWord_1723829 prefixEnd_1723829 885152843159441244809761 := by
  unfold tailWord_1723829
  simp only [CollatzResearch.WordTrace]
  refine ⟨62873208871869414399406541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41915472581246276266271027 62873208871869414399406541)
  ·
    refine ⟨23577453326951030399777453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62873208871869414399406541 23577453326951030399777453)
    ·
      refine ⟨8841544997606636399916545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23577453326951030399777453 8841544997606636399916545)
      ·
        refine ⟨6631158748204977299937409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8841544997606636399916545 6631158748204977299937409)
        ·
          refine ⟨4973369061153732974953057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6631158748204977299937409 4973369061153732974953057)
          ·
            refine ⟨3730026795865299731214793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4973369061153732974953057 3730026795865299731214793)
            ·
              refine ⟨2797520096898974798411095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3730026795865299731214793 2797520096898974798411095)
              ·
                refine ⟨4196280145348462197616643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2797520096898974798411095 4196280145348462197616643)
                ·
                  refine ⟨6294420218022693296424965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4196280145348462197616643 6294420218022693296424965)
                  ·
                    refine ⟨1180203790879254993079681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6294420218022693296424965 1180203790879254993079681)
                    ·
                      refine ⟨885152843159441244809761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1180203790879254993079681 885152843159441244809761)
                      ·
                        rfl

theorem cell23_1723829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_1723829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723829 prefixEnd_1723829 := by exact prefixLift 1723829
  have htrace : WordTrace (prefixWord ++ tailWord_1723829) baseStart_1723829 baseEnd_1723829 := by
    simpa [prefixWord, tailWord_1723829, baseEnd_1723829] using wordTrace_append hprefix tailTrace_1723829
  have hstable : (prefixWord ++ tailWord_1723829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723829).length < 2 ^ (prefixWord ++ tailWord_1723829).sum := by decide
  have hdescent : baseEnd_1723829 < baseStart_1723829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723852 : List Nat := [2, 2, 1, 4, 2, 1, 1, 5, 5]
def baseStart_1723852 : Nat := 118140960795 + 1723852 * 2 ^ 59
def prefixEnd_1723852 : Nat := 4983230072969 + 3 ^ 40 * 1723852 * 2
def baseEnd_1723852 : Nat := 98351628134943850535795

theorem tailTrace_1723852 : CollatzResearch.WordTrace tailWord_1723852 prefixEnd_1723852 98351628134943850535795 := by
  unfold tailWord_1723852
  simp only [CollatzResearch.WordTrace]
  refine ⟨31437023875393044663746905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41916031833857392884995873 31437023875393044663746905)
  ·
    refine ⟨23577767906544783497810179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31437023875393044663746905 23577767906544783497810179)
    ·
      refine ⟨35366651859817175246715269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23577767906544783497810179 35366651859817175246715269)
      ·
        refine ⟨6631247223715720358759113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35366651859817175246715269 6631247223715720358759113)
        ·
          refine ⟨4973435417786790269069335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6631247223715720358759113 4973435417786790269069335)
          ·
            refine ⟨7460153126680185403604003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4973435417786790269069335 7460153126680185403604003)
            ·
              refine ⟨11190229690020278105406005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7460153126680185403604003 11190229690020278105406005)
              ·
                refine ⟨1049084033439401072381813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11190229690020278105406005 1049084033439401072381813)
                ·
                  refine ⟨98351628134943850535795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1049084033439401072381813 98351628134943850535795)
                  ·
                    rfl

theorem cell23_1723852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 5].length) (baseStart_1723852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723852 prefixEnd_1723852 := by exact prefixLift 1723852
  have htrace : WordTrace (prefixWord ++ tailWord_1723852) baseStart_1723852 baseEnd_1723852 := by
    simpa [prefixWord, tailWord_1723852, baseEnd_1723852] using wordTrace_append hprefix tailTrace_1723852
  have hstable : (prefixWord ++ tailWord_1723852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723852).length < 2 ^ (prefixWord ++ tailWord_1723852).sum := by decide
  have hdescent : baseEnd_1723852 < baseStart_1723852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723895 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 5, 4]
def baseStart_1723895 : Nat := 118140960795 + 1723895 * 2 ^ 59
def prefixEnd_1723895 : Nat := 4983230072969 + 3 ^ 40 * 1723895 * 2
def baseEnd_1723895 : Nat := 295062244294212662194819

theorem tailTrace_1723895 : CollatzResearch.WordTrace tailWord_1723895 prefixEnd_1723895 295062244294212662194819 := by
  unfold tailWord_1723895
  simp only [CollatzResearch.WordTrace]
  refine ⟨62875616089630307671309139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41917077393086871780872759 62875616089630307671309139)
  ·
    refine ⟨94313424134445461506963709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62875616089630307671309139 94313424134445461506963709)
    ·
      refine ⟨35367534050417048065111391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94313424134445461506963709 35367534050417048065111391)
      ·
        refine ⟨53051301075625572097667087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35367534050417048065111391 53051301075625572097667087)
        ·
          refine ⟨79576951613438358146500631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53051301075625572097667087 79576951613438358146500631)
          ·
            refine ⟨119365427420157537219750947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79576951613438358146500631 119365427420157537219750947)
            ·
              refine ⟨179048141130236305829626421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119365427420157537219750947 179048141130236305829626421)
              ·
                refine ⟨16785763230959653671527477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179048141130236305829626421 16785763230959653671527477)
                ·
                  refine ⟨1573665302902467531705701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16785763230959653671527477 1573665302902467531705701)
                  ·
                    refine ⟨295062244294212662194819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1573665302902467531705701 295062244294212662194819)
                    ·
                      rfl

theorem cell23_1723895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_1723895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723895 prefixEnd_1723895 := by exact prefixLift 1723895
  have htrace : WordTrace (prefixWord ++ tailWord_1723895) baseStart_1723895 baseEnd_1723895 := by
    simpa [prefixWord, tailWord_1723895, baseEnd_1723895] using wordTrace_append hprefix tailTrace_1723895
  have hstable : (prefixWord ++ tailWord_1723895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723895).length < 2 ^ (prefixWord ++ tailWord_1723895).sum := by decide
  have hdescent : baseEnd_1723895 < baseStart_1723895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723925 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 8]
def baseStart_1723925 : Nat := 118140960795 + 1723925 * 2 ^ 59
def prefixEnd_1723925 : Nat := 4983230072969 + 3 ^ 40 * 1723925 * 2
def baseEnd_1723925 : Nat := 98355793033585874356591

theorem tailTrace_1723925 : CollatzResearch.WordTrace tailWord_1723925 prefixEnd_1723925 98355793033585874356591 := by
  unfold tailWord_1723925
  simp only [CollatzResearch.WordTrace]
  refine ⟨62876710279521622794901229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41917806853014415196600819 62876710279521622794901229)
  ·
    refine ⟨23578766354820608548087961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62876710279521622794901229 23578766354820608548087961)
    ·
      refine ⟨17684074766115456411065971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23578766354820608548087961 17684074766115456411065971)
      ·
        refine ⟨26526112149173184616598957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17684074766115456411065971 26526112149173184616598957)
        ·
          refine ⟨9947292055939944231224609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26526112149173184616598957 9947292055939944231224609)
          ·
            refine ⟨7460469041954958173418457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9947292055939944231224609 7460469041954958173418457)
            ·
              refine ⟨5595351781466218630063843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7460469041954958173418457 5595351781466218630063843)
              ·
                refine ⟨8393027672199327945095765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5595351781466218630063843 8393027672199327945095765)
                ·
                  refine ⟨98355793033585874356591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8393027672199327945095765 98355793033585874356591)
                  ·
                    rfl

theorem cell23_1723925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 8].length) (baseStart_1723925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723925 prefixEnd_1723925 := by exact prefixLift 1723925
  have htrace : WordTrace (prefixWord ++ tailWord_1723925) baseStart_1723925 baseEnd_1723925 := by
    simpa [prefixWord, tailWord_1723925, baseEnd_1723925] using wordTrace_append hprefix tailTrace_1723925
  have hstable : (prefixWord ++ tailWord_1723925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723925).length < 2 ^ (prefixWord ++ tailWord_1723925).sum := by decide
  have hdescent : baseEnd_1723925 < baseStart_1723925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723952 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 5, 1, 3]
def baseStart_1723952 : Nat := 118140960795 + 1723952 * 2 ^ 59
def prefixEnd_1723952 : Nat := 4983230072969 + 3 ^ 40 * 1723952 * 2
def baseEnd_1723952 : Nat := 885216001279944263571695

theorem tailTrace_1723952 : CollatzResearch.WordTrace tailWord_1723952 prefixEnd_1723952 885216001279944263571695 := by
  unfold tailWord_1723952
  simp only [CollatzResearch.WordTrace]
  refine ⟨31438847525211903203067055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41918463366949204270756073 31438847525211903203067055)
  ·
    refine ⟨47158271287817854804600583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31438847525211903203067055 47158271287817854804600583)
    ·
      refine ⟨70737406931726782206900875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47158271287817854804600583 70737406931726782206900875)
      ·
        refine ⟨106106110397590173310351313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70737406931726782206900875 106106110397590173310351313)
        ·
          refine ⟨79579582798192629982763485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106106110397590173310351313 79579582798192629982763485)
          ·
            refine ⟨29842343549322236243536307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79579582798192629982763485 29842343549322236243536307)
            ·
              refine ⟨44763515323983354365304461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29842343549322236243536307 44763515323983354365304461)
              ·
                refine ⟨16786318246493757886989173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44763515323983354365304461 16786318246493757886989173)
                ·
                  refine ⟨1573717335608789801905235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16786318246493757886989173 1573717335608789801905235)
                  ·
                    refine ⟨2360576003413184702857853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1573717335608789801905235 2360576003413184702857853)
                    ·
                      refine ⟨885216001279944263571695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2360576003413184702857853 885216001279944263571695)
                      ·
                        rfl

theorem cell23_1723952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 5, 1, 3].length) (baseStart_1723952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723952 prefixEnd_1723952 := by exact prefixLift 1723952
  have htrace : WordTrace (prefixWord ++ tailWord_1723952) baseStart_1723952 baseEnd_1723952 := by
    simpa [prefixWord, tailWord_1723952, baseEnd_1723952] using wordTrace_append hprefix tailTrace_1723952
  have hstable : (prefixWord ++ tailWord_1723952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723952).length < 2 ^ (prefixWord ++ tailWord_1723952).sum := by decide
  have hdescent : baseEnd_1723952 < baseStart_1723952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723985 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 3, 6]
def baseStart_1723985 : Nat := 118140960795 + 1723985 * 2 ^ 59
def prefixEnd_1723985 : Nat := 4983230072969 + 3 ^ 40 * 1723985 * 2
def baseEnd_1723985 : Nat := 295077648713847544819681

theorem tailTrace_1723985 : CollatzResearch.WordTrace tailWord_1723985 prefixEnd_1723985 295077648713847544819681 := by
  unfold tailWord_1723985
  simp only [CollatzResearch.WordTrace]
  refine ⟨62878898659304253042085409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41919265772869502028056939 62878898659304253042085409)
  ·
    refine ⟨47159173994478189781564057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62878898659304253042085409 47159173994478189781564057)
    ·
      refine ⟨35369380495858642336173043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47159173994478189781564057 35369380495858642336173043)
      ·
        refine ⟨53054070743787963504259565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35369380495858642336173043 53054070743787963504259565)
        ·
          refine ⟨19895276528920486314097337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53054070743787963504259565 19895276528920486314097337)
          ·
            refine ⟨14921457396690364735573003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19895276528920486314097337 14921457396690364735573003)
            ·
              refine ⟨22382186095035547103359505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14921457396690364735573003 22382186095035547103359505)
              ·
                refine ⟨16786639571276660327519629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22382186095035547103359505 16786639571276660327519629)
                ·
                  refine ⟨6294989839228747622819861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16786639571276660327519629 6294989839228747622819861)
                  ·
                    refine ⟨295077648713847544819681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6294989839228747622819861 295077648713847544819681)
                    ·
                      rfl

theorem cell23_1723985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_1723985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723985 prefixEnd_1723985 := by exact prefixLift 1723985
  have htrace : WordTrace (prefixWord ++ tailWord_1723985) baseStart_1723985 baseEnd_1723985 := by
    simpa [prefixWord, tailWord_1723985, baseEnd_1723985] using wordTrace_append hprefix tailTrace_1723985
  have hstable : (prefixWord ++ tailWord_1723985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723985).length < 2 ^ (prefixWord ++ tailWord_1723985).sum := by decide
  have hdescent : baseEnd_1723985 < baseStart_1723985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1723992 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 2, 6, 2]
def baseStart_1723992 : Nat := 118140960795 + 1723992 * 2 ^ 59
def prefixEnd_1723992 : Nat := 4983230072969 + 3 ^ 40 * 1723992 * 2
def baseEnd_1723992 : Nat := 885236540506124107071511

theorem tailTrace_1723992 : CollatzResearch.WordTrace tailWord_1723992 prefixEnd_1723992 885236540506124107071511 := by
  unfold tailWord_1723992
  simp only [CollatzResearch.WordTrace]
  refine ⟨31439576985139446618795115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41919435980185928825060153 31439576985139446618795115)
  ·
    refine ⟨47159365477709169928192673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31439576985139446618795115 47159365477709169928192673)
    ·
      refine ⟨35369524108281877446144505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47159365477709169928192673 35369524108281877446144505)
      ·
        refine ⟨26527143081211408084608379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35369524108281877446144505 26527143081211408084608379)
        ·
          refine ⟨39790714621817112126912569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26527143081211408084608379 39790714621817112126912569)
          ·
            refine ⟨29843035966362834095184427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39790714621817112126912569 29843035966362834095184427)
            ·
              refine ⟨44764553949544251142776641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29843035966362834095184427 44764553949544251142776641)
              ·
                refine ⟨33573415462158188357082481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44764553949544251142776641 33573415462158188357082481)
                ·
                  refine ⟨25180061596618641267811861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33573415462158188357082481 25180061596618641267811861)
                  ·
                    refine ⟨1180315387341498809428681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25180061596618641267811861 1180315387341498809428681)
                    ·
                      refine ⟨885236540506124107071511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1180315387341498809428681 885236540506124107071511)
                      ·
                        rfl

theorem cell23_1723992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_1723992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1723992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1723992 prefixEnd_1723992 := by exact prefixLift 1723992
  have htrace : WordTrace (prefixWord ++ tailWord_1723992) baseStart_1723992 baseEnd_1723992 := by
    simpa [prefixWord, tailWord_1723992, baseEnd_1723992] using wordTrace_append hprefix tailTrace_1723992
  have hstable : (prefixWord ++ tailWord_1723992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1723992).length < 2 ^ (prefixWord ++ tailWord_1723992).sum := by decide
  have hdescent : baseEnd_1723992 < baseStart_1723992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1723992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724009 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 5, 2, 2]
def baseStart_1724009 : Nat := 118140960795 + 1724009 * 2 ^ 59
def prefixEnd_1724009 : Nat := 4983230072969 + 3 ^ 40 * 1724009 * 2
def baseEnd_1724009 : Nat := 885245269677250540558933

theorem tailTrace_1724009 : CollatzResearch.WordTrace tailWord_1724009 prefixEnd_1724009 885245269677250540558933 := by
  unfold tailWord_1724009
  simp only [CollatzResearch.WordTrace]
  refine ⟨62879774011217305140959081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41919849340811536760639387 62879774011217305140959081)
  ·
    refine ⟨47159830508412978855719311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62879774011217305140959081 47159830508412978855719311)
    ·
      refine ⟨70739745762619468283578967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47159830508412978855719311 70739745762619468283578967)
      ·
        refine ⟨106109618643929202425368451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70739745762619468283578967 106109618643929202425368451)
        ·
          refine ⟨159164427965893803638052677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106109618643929202425368451 159164427965893803638052677)
          ·
            refine ⟨29843330243605088182134877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159164427965893803638052677 29843330243605088182134877)
            ·
              refine ⟨11191248841351908068300579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29843330243605088182134877 11191248841351908068300579)
              ·
                refine ⟨16786873262027862102450869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11191248841351908068300579 16786873262027862102450869)
                ·
                  refine ⟨1573769368315112072104769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16786873262027862102450869 1573769368315112072104769)
                  ·
                    refine ⟨1180327026236334054078577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1573769368315112072104769 1180327026236334054078577)
                    ·
                      refine ⟨885245269677250540558933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1180327026236334054078577 885245269677250540558933)
                      ·
                        rfl

theorem cell23_1724009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 2, 2].length) (baseStart_1724009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724009 prefixEnd_1724009 := by exact prefixLift 1724009
  have htrace : WordTrace (prefixWord ++ tailWord_1724009) baseStart_1724009 baseEnd_1724009 := by
    simpa [prefixWord, tailWord_1724009, baseEnd_1724009] using wordTrace_append hprefix tailTrace_1724009
  have hstable : (prefixWord ++ tailWord_1724009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724009).length < 2 ^ (prefixWord ++ tailWord_1724009).sum := by decide
  have hdescent : baseEnd_1724009 < baseStart_1724009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724013 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 2, 3, 2]
def baseStart_1724013 : Nat := 118140960795 + 1724013 * 2 ^ 59
def prefixEnd_1724013 : Nat := 4983230072969 + 3 ^ 40 * 1724013 * 2
def baseEnd_1724013 : Nat := 885247323599868524908915

theorem tailTrace_1724013 : CollatzResearch.WordTrace tailWord_1724013 prefixEnd_1724013 885247323599868524908915 := by
  unfold tailWord_1724013
  simp only [CollatzResearch.WordTrace]
  refine ⟨62879919903202813824104693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41919946602135209216069795 62879919903202813824104693)
  ·
    refine ⟨5894992490925263796009815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62879919903202813824104693 5894992490925263796009815)
    ·
      refine ⟨8842488736387895694014723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5894992490925263796009815 8842488736387895694014723)
      ·
        refine ⟨13263733104581843541022085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8842488736387895694014723 13263733104581843541022085)
        ·
          refine ⟨2486949957109095663941641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13263733104581843541022085 2486949957109095663941641)
          ·
            refine ⟨1865212467831821747956231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2486949957109095663941641 1865212467831821747956231)
            ·
              refine ⟨2797818701747732621934347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865212467831821747956231 2797818701747732621934347)
              ·
                refine ⟨4196728052621598932901521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2797818701747732621934347 4196728052621598932901521)
                ·
                  refine ⟨3147546039466199199676141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4196728052621598932901521 3147546039466199199676141)
                  ·
                    refine ⟨1180329764799824699878553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3147546039466199199676141 1180329764799824699878553)
                    ·
                      refine ⟨885247323599868524908915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1180329764799824699878553 885247323599868524908915)
                      ·
                        rfl

theorem cell23_1724013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_1724013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724013 prefixEnd_1724013 := by exact prefixLift 1724013
  have htrace : WordTrace (prefixWord ++ tailWord_1724013) baseStart_1724013 baseEnd_1724013 := by
    simpa [prefixWord, tailWord_1724013, baseEnd_1724013] using wordTrace_append hprefix tailTrace_1724013
  have hstable : (prefixWord ++ tailWord_1724013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724013).length < 2 ^ (prefixWord ++ tailWord_1724013).sum := by decide
  have hdescent : baseEnd_1724013 < baseStart_1724013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724035 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 6]
def baseStart_1724035 : Nat := 118140960795 + 1724035 * 2 ^ 59
def prefixEnd_1724035 : Nat := 4983230072969 + 3 ^ 40 * 1724035 * 2
def baseEnd_1724035 : Nat := 885258620174267438833813

theorem tailTrace_1724035 : CollatzResearch.WordTrace tailWord_1724035 prefixEnd_1724035 885258620174267438833813 := by
  unfold tailWord_1724035
  simp only [CollatzResearch.WordTrace]
  refine ⟨62880722309123111581405559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41920481539415407720937039 62880722309123111581405559)
  ·
    refine ⟨94321083463684667372108339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62880722309123111581405559 94321083463684667372108339)
    ·
      refine ⟨141481625195527001058162509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94321083463684667372108339 141481625195527001058162509)
      ·
        refine ⟨53055609448322625396810941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141481625195527001058162509 53055609448322625396810941)
        ·
          refine ⟨19895853543120984523804103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53055609448322625396810941 19895853543120984523804103)
          ·
            refine ⟨29843780314681476785706155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19895853543120984523804103 29843780314681476785706155)
            ·
              refine ⟨44765670472022215178559233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29843780314681476785706155 44765670472022215178559233)
              ·
                refine ⟨33574252854016661383919425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44765670472022215178559233 33574252854016661383919425)
                ·
                  refine ⟨25180689640512496037939569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33574252854016661383919425 25180689640512496037939569)
                  ·
                    refine ⟨18885517230384372028454677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25180689640512496037939569 18885517230384372028454677)
                    ·
                      refine ⟨885258620174267438833813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18885517230384372028454677 885258620174267438833813)
                      ·
                        rfl

theorem cell23_1724035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_1724035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724035 prefixEnd_1724035 := by exact prefixLift 1724035
  have htrace : WordTrace (prefixWord ++ tailWord_1724035) baseStart_1724035 baseEnd_1724035 := by
    simpa [prefixWord, tailWord_1724035, baseEnd_1724035] using wordTrace_append hprefix tailTrace_1724035
  have hstable : (prefixWord ++ tailWord_1724035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724035).length < 2 ^ (prefixWord ++ tailWord_1724035).sum := by decide
  have hdescent : baseEnd_1724035 < baseStart_1724035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724063 : List Nat := [1, 1, 2, 7, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1724063 : Nat := 118140960795 + 1724063 * 2 ^ 59
def prefixEnd_1724063 : Nat := 4983230072969 + 3 ^ 40 * 1724063 * 2
def baseEnd_1724063 : Nat := 885272997632593329283685

theorem tailTrace_1724063 : CollatzResearch.WordTrace tailWord_1724063 prefixEnd_1724063 885272997632593329283685 := by
  unfold tailWord_1724063
  simp only [CollatzResearch.WordTrace]
  refine ⟨62881743553021672363424843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41921162368681114908949895 62881743553021672363424843)
  ·
    refine ⟨94322615329532508545137265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62881743553021672363424843 94322615329532508545137265)
    ·
      refine ⟨70741961497149381408852949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94322615329532508545137265 70741961497149381408852949)
      ·
        refine ⟨1658014722589438626769991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 70741961497149381408852949 1658014722589438626769991)
        ·
          refine ⟨2487022083884157940154987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1658014722589438626769991 2487022083884157940154987)
          ·
            refine ⟨3730533125826236910232481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487022083884157940154987 3730533125826236910232481)
            ·
              refine ⟨2797899844369677682674361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3730533125826236910232481 2797899844369677682674361)
              ·
                refine ⟨2098424883277258262005771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2797899844369677682674361 2098424883277258262005771)
                ·
                  refine ⟨3147637324915887393008657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2098424883277258262005771 3147637324915887393008657)
                  ·
                    refine ⟨2360727993686915544756493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3147637324915887393008657 2360727993686915544756493)
                    ·
                      refine ⟨885272997632593329283685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2360727993686915544756493 885272997632593329283685)
                      ·
                        rfl

theorem cell23_1724063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1724063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724063 prefixEnd_1724063 := by exact prefixLift 1724063
  have htrace : WordTrace (prefixWord ++ tailWord_1724063) baseStart_1724063 baseEnd_1724063 := by
    simpa [prefixWord, tailWord_1724063, baseEnd_1724063] using wordTrace_append hprefix tailTrace_1724063
  have hstable : (prefixWord ++ tailWord_1724063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724063).length < 2 ^ (prefixWord ++ tailWord_1724063).sum := by decide
  have hdescent : baseEnd_1724063 < baseStart_1724063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724069 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 3, 3, 2]
def baseStart_1724069 : Nat := 118140960795 + 1724069 * 2 ^ 59
def prefixEnd_1724069 : Nat := 4983230072969 + 3 ^ 40 * 1724069 * 2
def baseEnd_1724069 : Nat := 885276078516520305808657

theorem tailTrace_1724069 : CollatzResearch.WordTrace tailWord_1724069 prefixEnd_1724069 885276078516520305808657 := by
  unfold tailWord_1724069
  simp only [CollatzResearch.WordTrace]
  refine ⟨62881962390999935388143261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41921308260666623592095507 62881962390999935388143261)
  ·
    refine ⟨23580735896624975770553723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62881962390999935388143261 23580735896624975770553723)
    ·
      refine ⟨35371103844937463655830585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23580735896624975770553723 35371103844937463655830585)
      ·
        refine ⟨26528327883703097741872939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35371103844937463655830585 26528327883703097741872939)
        ·
          refine ⟨39792491825554646612809409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26528327883703097741872939 39792491825554646612809409)
          ·
            refine ⟨29844368869165984959607057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39792491825554646612809409 29844368869165984959607057)
            ·
              refine ⟨22383276651874488719705293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29844368869165984959607057 22383276651874488719705293)
              ·
                refine ⟨8393728744452933269889485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22383276651874488719705293 8393728744452933269889485)
                ·
                  refine ⟨3147648279169849976208557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8393728744452933269889485 3147648279169849976208557)
                  ·
                    refine ⟨1180368104688693741078209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3147648279169849976208557 1180368104688693741078209)
                    ·
                      refine ⟨885276078516520305808657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1180368104688693741078209 885276078516520305808657)
                      ·
                        rfl

theorem cell23_1724069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_1724069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724069 prefixEnd_1724069 := by exact prefixLift 1724069
  have htrace : WordTrace (prefixWord ++ tailWord_1724069) baseStart_1724069 baseEnd_1724069 := by
    simpa [prefixWord, tailWord_1724069, baseEnd_1724069] using wordTrace_append hprefix tailTrace_1724069
  have hstable : (prefixWord ++ tailWord_1724069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724069).length < 2 ^ (prefixWord ++ tailWord_1724069).sum := by decide
  have hdescent : baseEnd_1724069 < baseStart_1724069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724150 : List Nat := [5, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2]
def baseStart_1724150 : Nat := 118140960795 + 1724150 * 2 ^ 59
def prefixEnd_1724150 : Nat := 4983230072969 + 3 ^ 40 * 1724150 * 2
def baseEnd_1724150 : Nat := 885317670449534488895785

theorem tailTrace_1724150 : CollatzResearch.WordTrace tailWord_1724150 prefixEnd_1724150 885317670449534488895785 := by
  unfold tailWord_1724150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3930307293981655388865119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41923277802470990814561269 3930307293981655388865119)
  ·
    refine ⟨5895460940972483083297679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3930307293981655388865119 5895460940972483083297679)
    ·
      refine ⟨8843191411458724624946519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5895460940972483083297679 8843191411458724624946519)
      ·
        refine ⟨13264787117188086937419779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8843191411458724624946519 13264787117188086937419779)
        ·
          refine ⟨19897180675782130406129669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13264787117188086937419779 19897180675782130406129669)
          ·
            refine ⟨3730721376709149451149313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19897180675782130406129669 3730721376709149451149313)
            ·
              refine ⟨2798041032531862088361985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3730721376709149451149313 2798041032531862088361985)
              ·
                refine ⟨2098530774398896566271489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2798041032531862088361985 2098530774398896566271489)
                ·
                  refine ⟨1573898080799172424703617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2098530774398896566271489 1573898080799172424703617)
                  ·
                    refine ⟨1180423560599379318527713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1573898080799172424703617 1180423560599379318527713)
                    ·
                      refine ⟨885317670449534488895785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1180423560599379318527713 885317670449534488895785)
                      ·
                        rfl

theorem cell23_1724150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_1724150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724150 prefixEnd_1724150 := by exact prefixLift 1724150
  have htrace : WordTrace (prefixWord ++ tailWord_1724150) baseStart_1724150 baseEnd_1724150 := by
    simpa [prefixWord, tailWord_1724150, baseEnd_1724150] using wordTrace_append hprefix tailTrace_1724150
  have hstable : (prefixWord ++ tailWord_1724150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724150).length < 2 ^ (prefixWord ++ tailWord_1724150).sum := by decide
  have hdescent : baseEnd_1724150 < baseStart_1724150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724152 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 4, 5]
def baseStart_1724152 : Nat := 118140960795 + 1724152 * 2 ^ 59
def prefixEnd_1724152 : Nat := 4983230072969 + 3 ^ 40 * 1724152 * 2
def baseEnd_1724152 : Nat := 295106232470281160356925

theorem tailTrace_1724152 : CollatzResearch.WordTrace tailWord_1724152 prefixEnd_1724152 295106232470281160356925 := by
  unfold tailWord_1724152
  simp only [CollatzResearch.WordTrace]
  refine ⟨31442494824849620281707355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41923326433132827042276473 31442494824849620281707355)
  ·
    refine ⟨47163742237274430422561033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31442494824849620281707355 47163742237274430422561033)
    ·
      refine ⟨35372806677955822816920775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47163742237274430422561033 35372806677955822816920775)
      ·
        refine ⟨53059210016933734225381163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35372806677955822816920775 53059210016933734225381163)
        ·
          refine ⟨79588815025400601338071745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53059210016933734225381163 79588815025400601338071745)
          ·
            refine ⟨59691611269050451003553809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79588815025400601338071745 59691611269050451003553809)
            ·
              refine ⟨44768708451787838252665357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59691611269050451003553809 44768708451787838252665357)
              ·
                refine ⟨16788265669420439344749509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44768708451787838252665357 16788265669420439344749509)
                ·
                  refine ⟨3147799813016332377140533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16788265669420439344749509 3147799813016332377140533)
                  ·
                    refine ⟨295106232470281160356925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3147799813016332377140533 295106232470281160356925)
                    ·
                      rfl

theorem cell23_1724152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_1724152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724152 prefixEnd_1724152 := by exact prefixLift 1724152
  have htrace : WordTrace (prefixWord ++ tailWord_1724152) baseStart_1724152 baseEnd_1724152 := by
    simpa [prefixWord, tailWord_1724152, baseEnd_1724152] using wordTrace_append hprefix tailTrace_1724152
  have hstable : (prefixWord ++ tailWord_1724152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724152).length < 2 ^ (prefixWord ++ tailWord_1724152).sum := by decide
  have hdescent : baseEnd_1724152 < baseStart_1724152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724159 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 2, 5, 2]
def baseStart_1724159 : Nat := 118140960795 + 1724159 * 2 ^ 59
def prefixEnd_1724159 : Nat := 4983230072969 + 3 ^ 40 * 1724159 * 2
def baseEnd_1724159 : Nat := 885322291775424953683243

theorem tailTrace_1724159 : CollatzResearch.WordTrace tailWord_1724159 prefixEnd_1724159 885322291775424953683243 := by
  unfold tailWord_1724159
  simp only [CollatzResearch.WordTrace]
  refine ⟨62885244960673880758919531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41923496640449253839279687 62885244960673880758919531)
  ·
    refine ⟨94327867441010821138379297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62885244960673880758919531 94327867441010821138379297)
    ·
      refine ⟨70745900580758115853784473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94327867441010821138379297 70745900580758115853784473)
      ·
        refine ⟨53059425435568586890338355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70745900580758115853784473 53059425435568586890338355)
        ·
          refine ⟨79589138153352880335507533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53059425435568586890338355 79589138153352880335507533)
          ·
            refine ⟨29845926807507330125815325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79589138153352880335507533 29845926807507330125815325)
            ·
              refine ⟨11192222552815248797180747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29845926807507330125815325 11192222552815248797180747)
              ·
                refine ⟨16788333829222873195771121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11192222552815248797180747 16788333829222873195771121)
                ·
                  refine ⟨12591250371917154896828341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16788333829222873195771121 12591250371917154896828341)
                  ·
                    refine ⟨1180429722367233271577657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12591250371917154896828341 1180429722367233271577657)
                    ·
                      refine ⟨885322291775424953683243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1180429722367233271577657 885322291775424953683243)
                      ·
                        rfl

theorem cell23_1724159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 5, 2].length) (baseStart_1724159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724159 prefixEnd_1724159 := by exact prefixLift 1724159
  have htrace : WordTrace (prefixWord ++ tailWord_1724159) baseStart_1724159 baseEnd_1724159 := by
    simpa [prefixWord, tailWord_1724159, baseEnd_1724159] using wordTrace_append hprefix tailTrace_1724159
  have hstable : (prefixWord ++ tailWord_1724159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724159).length < 2 ^ (prefixWord ++ tailWord_1724159).sum := by decide
  have hdescent : baseEnd_1724159 < baseStart_1724159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724186 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 2, 5]
def baseStart_1724186 : Nat := 118140960795 + 1724186 * 2 ^ 59
def prefixEnd_1724186 : Nat := 4983230072969 + 3 ^ 40 * 1724186 * 2
def baseEnd_1724186 : Nat := 295112051917698782681873

theorem tailTrace_1724186 : CollatzResearch.WordTrace tailWord_1724186 prefixEnd_1724186 295112051917698782681873 := by
  unfold tailWord_1724186
  simp only [CollatzResearch.WordTrace]
  refine ⟨15721557432894016092538103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41924153154384042913434941 15721557432894016092538103)
  ·
    refine ⟨23582336149341024138807155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15721557432894016092538103 23582336149341024138807155)
    ·
      refine ⟨35373504224011536208210733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23582336149341024138807155 35373504224011536208210733)
      ·
        refine ⟨13265064084004326078079025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35373504224011536208210733 13265064084004326078079025)
        ·
          refine ⟨9948798063003244558559269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13265064084004326078079025 9948798063003244558559269)
          ·
            refine ⟨1865399636813108354729863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9948798063003244558559269 1865399636813108354729863)
            ·
              refine ⟨2798099455219662532094795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865399636813108354729863 2798099455219662532094795)
              ·
                refine ⟨4197149182829493798142193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798099455219662532094795 4197149182829493798142193)
                ·
                  refine ⟨3147861887122120348606645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4197149182829493798142193 3147861887122120348606645)
                  ·
                    refine ⟨295112051917698782681873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3147861887122120348606645 295112051917698782681873)
                    ·
                      rfl

theorem cell23_1724186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_1724186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724186 prefixEnd_1724186 := by exact prefixLift 1724186
  have htrace : WordTrace (prefixWord ++ tailWord_1724186) baseStart_1724186 baseEnd_1724186 := by
    simpa [prefixWord, tailWord_1724186, baseEnd_1724186] using wordTrace_append hprefix tailTrace_1724186
  have hstable : (prefixWord ++ tailWord_1724186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724186).length < 2 ^ (prefixWord ++ tailWord_1724186).sum := by decide
  have hdescent : baseEnd_1724186 < baseStart_1724186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724216 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 3, 4]
def baseStart_1724216 : Nat := 118140960795 + 1724216 * 2 ^ 59
def prefixEnd_1724216 : Nat := 4983230072969 + 3 ^ 40 * 1724216 * 2
def baseEnd_1724216 : Nat := 295117186724243743556827

theorem tailTrace_1724216 : CollatzResearch.WordTrace tailWord_1724216 prefixEnd_1724216 295117186724243743556827 := by
  unfold tailWord_1724216
  simp only [CollatzResearch.WordTrace]
  refine ⟨31443661960733689746872251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41924882614311586329163001 31443661960733689746872251)
  ·
    refine ⟨47165492941100534620308377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31443661960733689746872251 47165492941100534620308377)
    ·
      refine ⟨35374119705825400965231283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47165492941100534620308377 35374119705825400965231283)
      ·
        refine ⟨53061179558738101447846925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35374119705825400965231283 53061179558738101447846925)
        ·
          refine ⟨19897942334526788042942597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53061179558738101447846925 19897942334526788042942597)
          ·
            refine ⟨3730864187723772758051737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19897942334526788042942597 3730864187723772758051737)
            ·
              refine ⟨2798148140792829568538803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3730864187723772758051737 2798148140792829568538803)
              ·
                refine ⟨4197222211189244352808205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798148140792829568538803 4197222211189244352808205)
                ·
                  refine ⟨1573958329195966632303077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4197222211189244352808205 1573958329195966632303077)
                  ·
                    refine ⟨295117186724243743556827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1573958329195966632303077 295117186724243743556827)
                    ·
                      rfl

theorem cell23_1724216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_1724216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724216 prefixEnd_1724216 := by exact prefixLift 1724216
  have htrace : WordTrace (prefixWord ++ tailWord_1724216) baseStart_1724216 baseEnd_1724216 := by
    simpa [prefixWord, tailWord_1724216, baseEnd_1724216] using wordTrace_append hprefix tailTrace_1724216
  have hstable : (prefixWord ++ tailWord_1724216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724216).length < 2 ^ (prefixWord ++ tailWord_1724216).sum := by decide
  have hdescent : baseEnd_1724216 < baseStart_1724216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724306 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 3, 6]
def baseStart_1724306 : Nat := 118140960795 + 1724306 * 2 ^ 59
def prefixEnd_1724306 : Nat := 4983230072969 + 3 ^ 40 * 1724306 * 2
def baseEnd_1724306 : Nat := 295132591143878626181689

theorem tailTrace_1724306 : CollatzResearch.WordTrace tailWord_1724306 prefixEnd_1724306 295132591143878626181689 := by
  unfold tailWord_1724306
  simp only [CollatzResearch.WordTrace]
  refine ⟨15722651622785331216130193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41927070994094216576347181 15722651622785331216130193)
  ·
    refine ⟨11791988717088998412097645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15722651622785331216130193 11791988717088998412097645)
    ·
      refine ⟨4421995768908374404536617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11791988717088998412097645 4421995768908374404536617)
      ·
        refine ⟨3316496826681280803402463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4421995768908374404536617 3316496826681280803402463)
        ·
          refine ⟨4974745240021921205103695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3316496826681280803402463 4974745240021921205103695)
          ·
            refine ⟨7462117860032881807655543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4974745240021921205103695 7462117860032881807655543)
            ·
              refine ⟨11193176790049322711483315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7462117860032881807655543 11193176790049322711483315)
              ·
                refine ⟨16789765185073984067224973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11193176790049322711483315 16789765185073984067224973)
                ·
                  refine ⟨6296161944402744025209365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16789765185073984067224973 6296161944402744025209365)
                  ·
                    refine ⟨295132591143878626181689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6296161944402744025209365 295132591143878626181689)
                    ·
                      rfl

theorem cell23_1724306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_1724306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724306 prefixEnd_1724306 := by exact prefixLift 1724306
  have htrace : WordTrace (prefixWord ++ tailWord_1724306) baseStart_1724306 baseEnd_1724306 := by
    simpa [prefixWord, tailWord_1724306, baseEnd_1724306] using wordTrace_append hprefix tailTrace_1724306
  have hstable : (prefixWord ++ tailWord_1724306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724306).length < 2 ^ (prefixWord ++ tailWord_1724306).sum := by decide
  have hdescent : baseEnd_1724306 < baseStart_1724306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724319 : List Nat := [1, 1, 2, 5, 3, 11]
def baseStart_1724319 : Nat := 118140960795 + 1724319 * 2 ^ 59
def prefixEnd_1724319 : Nat := 4983230072969 + 3 ^ 40 * 1724319 * 2
def baseEnd_1724319 : Nat := 3643639706502651554249

theorem tailTrace_1724319 : CollatzResearch.WordTrace tailWord_1724319 prefixEnd_1724319 3643639706502651554249 := by
  unfold tailWord_1724319
  simp only [CollatzResearch.WordTrace]
  refine ⟨62891080640094228084744011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41927387093396152056496007 62891080640094228084744011)
  ·
    refine ⟨94336620960141342127116017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62891080640094228084744011 94336620960141342127116017)
    ·
      refine ⟨70752465720106006595337013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94336620960141342127116017 70752465720106006595337013)
      ·
        refine ⟨6633043661259938118312845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70752465720106006595337013 6633043661259938118312845)
        ·
          refine ⟨2487391372972476794367317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6633043661259938118312845 2487391372972476794367317)
          ·
            refine ⟨3643639706502651554249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2487391372972476794367317 3643639706502651554249)
            ·
              rfl

theorem cell23_1724319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 11].length) (baseStart_1724319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724319 prefixEnd_1724319 := by exact prefixLift 1724319
  have htrace : WordTrace (prefixWord ++ tailWord_1724319) baseStart_1724319 baseEnd_1724319 := by
    simpa [prefixWord, tailWord_1724319, baseEnd_1724319] using wordTrace_append hprefix tailTrace_1724319
  have hstable : (prefixWord ++ tailWord_1724319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724319).length < 2 ^ (prefixWord ++ tailWord_1724319).sum := by decide
  have hdescent : baseEnd_1724319 < baseStart_1724319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724340 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_1724340 : Nat := 118140960795 + 1724340 * 2 ^ 59
def prefixEnd_1724340 : Nat := 4983230072969 + 3 ^ 40 * 1724340 * 2
def baseEnd_1724340 : Nat := 295138410591296248506637

theorem tailTrace_1724340 : CollatzResearch.WordTrace tailWord_1724340 prefixEnd_1724340 295138410591296248506637 := by
  unfold tailWord_1724340
  simp only [CollatzResearch.WordTrace]
  refine ⟨31445923286509074335629237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41927897715345432447505649 31445923286509074335629237)
  ·
    refine ⟨2948055308110225718965241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31445923286509074335629237 2948055308110225718965241)
    ·
      refine ⟨2211041481082669289223931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2948055308110225718965241 2211041481082669289223931)
      ·
        refine ⟨3316562221624003933835897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2211041481082669289223931 3316562221624003933835897)
        ·
          refine ⟨2487421666218002950376923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3316562221624003933835897 2487421666218002950376923)
          ·
            refine ⟨3731132499327004425565385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487421666218002950376923 3731132499327004425565385)
            ·
              refine ⟨2798349374495253319174039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3731132499327004425565385 2798349374495253319174039)
              ·
                refine ⟨4197524061742879978761059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798349374495253319174039 4197524061742879978761059)
                ·
                  refine ⟨6296286092614319968141589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4197524061742879978761059 6296286092614319968141589)
                  ·
                    refine ⟨295138410591296248506637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6296286092614319968141589 295138410591296248506637)
                    ·
                      rfl

theorem cell23_1724340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_1724340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724340 prefixEnd_1724340 := by exact prefixLift 1724340
  have htrace : WordTrace (prefixWord ++ tailWord_1724340) baseStart_1724340 baseEnd_1724340 := by
    simpa [prefixWord, tailWord_1724340, baseEnd_1724340] using wordTrace_append hprefix tailTrace_1724340
  have hstable : (prefixWord ++ tailWord_1724340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724340).length < 2 ^ (prefixWord ++ tailWord_1724340).sum := by decide
  have hdescent : baseEnd_1724340 < baseStart_1724340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724359 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_1724359 : Nat := 118140960795 + 1724359 * 2 ^ 59
def prefixEnd_1724359 : Nat := 4983230072969 + 3 ^ 40 * 1724359 * 2
def baseEnd_1724359 : Nat := 885424987906324171182323

theorem tailTrace_1724359 : CollatzResearch.WordTrace tailWord_1724359 prefixEnd_1724359 885424987906324171182323 := by
  unfold tailWord_1724359
  simp only [CollatzResearch.WordTrace]
  refine ⟨62892539559949314916200131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41928359706632876610800087 62892539559949314916200131)
  ·
    refine ⟨94338809339923972374300197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62892539559949314916200131 94338809339923972374300197)
    ·
      refine ⟨17688526751235744820181287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94338809339923972374300197 17688526751235744820181287)
      ·
        refine ⟨26532790126853617230271931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17688526751235744820181287 26532790126853617230271931)
        ·
          refine ⟨39799185190280425845407897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26532790126853617230271931 39799185190280425845407897)
          ·
            refine ⟨29849388892710319384055923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39799185190280425845407897 29849388892710319384055923)
            ·
              refine ⟨44774083339065479076083885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29849388892710319384055923 44774083339065479076083885)
              ·
                refine ⟨16790281252149554653531457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44774083339065479076083885 16790281252149554653531457)
                ·
                  refine ⟨12592710939112165990148593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16790281252149554653531457 12592710939112165990148593)
                  ·
                    refine ⟨9444533204334124492611445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12592710939112165990148593 9444533204334124492611445)
                    ·
                      refine ⟨885424987906324171182323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9444533204334124492611445 885424987906324171182323)
                      ·
                        rfl

theorem cell23_1724359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_1724359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724359 prefixEnd_1724359 := by exact prefixLift 1724359
  have htrace : WordTrace (prefixWord ++ tailWord_1724359) baseStart_1724359 baseEnd_1724359 := by
    simpa [prefixWord, tailWord_1724359, baseEnd_1724359] using wordTrace_append hprefix tailTrace_1724359
  have hstable : (prefixWord ++ tailWord_1724359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724359).length < 2 ^ (prefixWord ++ tailWord_1724359).sum := by decide
  have hdescent : baseEnd_1724359 < baseStart_1724359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724369 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 1, 5, 4]
def baseStart_1724369 : Nat := 118140960795 + 1724369 * 2 ^ 59
def prefixEnd_1724369 : Nat := 4983230072969 + 3 ^ 40 * 1724369 * 2
def baseEnd_1724369 : Nat := 885430122712869132057277

theorem tailTrace_1724369 : CollatzResearch.WordTrace tailWord_1724369 prefixEnd_1724369 885430122712869132057277 := by
  unfold tailWord_1724369
  simp only [CollatzResearch.WordTrace]
  refine ⟨62892904289913086624064161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41928602859942057749376107 62892904289913086624064161)
  ·
    refine ⟨47169678217434814968048121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62892904289913086624064161 47169678217434814968048121)
    ·
      refine ⟨35377258663076111226036091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47169678217434814968048121 35377258663076111226036091)
      ·
        refine ⟨53065887994614166839054137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35377258663076111226036091 53065887994614166839054137)
        ·
          refine ⟨39799415995960625129290603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53065887994614166839054137 39799415995960625129290603)
          ·
            refine ⟨59699123993940937693935905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39799415995960625129290603 59699123993940937693935905)
            ·
              refine ⟨44774342995455703270451929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59699123993940937693935905 44774342995455703270451929)
              ·
                refine ⟨33580757246591777452838947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44774342995455703270451929 33580757246591777452838947)
                ·
                  refine ⟨50371135869887666179258421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33580757246591777452838947 50371135869887666179258421)
                  ·
                    refine ⟨4722293987801968704305477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50371135869887666179258421 4722293987801968704305477)
                    ·
                      refine ⟨885430122712869132057277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4722293987801968704305477 885430122712869132057277)
                      ·
                        rfl

theorem cell23_1724369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_1724369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724369 prefixEnd_1724369 := by exact prefixLift 1724369
  have htrace : WordTrace (prefixWord ++ tailWord_1724369) baseStart_1724369 baseEnd_1724369 := by
    simpa [prefixWord, tailWord_1724369, baseEnd_1724369] using wordTrace_append hprefix tailTrace_1724369
  have hstable : (prefixWord ++ tailWord_1724369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724369).length < 2 ^ (prefixWord ++ tailWord_1724369).sum := by decide
  have hdescent : baseEnd_1724369 < baseStart_1724369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724374 : List Nat := [5, 2, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_1724374 : Nat := 118140960795 + 1724374 * 2 ^ 59
def prefixEnd_1724374 : Nat := 4983230072969 + 3 ^ 40 * 1724374 * 2
def baseEnd_1724374 : Nat := 295144230038713870831585

theorem tailTrace_1724374 : CollatzResearch.WordTrace tailWord_1724374 prefixEnd_1724374 295144230038713870831585 := by
  unfold tailWord_1724374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3930817915930935779874761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41928724436596648318664117 3930817915930935779874761)
  ·
    refine ⟨2948113436948201834906071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3930817915930935779874761 2948113436948201834906071)
    ·
      refine ⟨4422170155422302752359107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2948113436948201834906071 4422170155422302752359107)
      ·
        refine ⟨6633255233133454128538661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4422170155422302752359107 6633255233133454128538661)
        ·
          refine ⟨1243735356212522649100999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6633255233133454128538661 1243735356212522649100999)
          ·
            refine ⟨1865603034318783973651499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243735356212522649100999 1865603034318783973651499)
            ·
              refine ⟨2798404551478175960477249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865603034318783973651499 2798404551478175960477249)
              ·
                refine ⟨2098803413608631970357937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2798404551478175960477249 2098803413608631970357937)
                ·
                  refine ⟨1574102560206473977768453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2098803413608631970357937 1574102560206473977768453)
                  ·
                    refine ⟨295144230038713870831585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1574102560206473977768453 295144230038713870831585)
                    ·
                      rfl

theorem cell23_1724374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_1724374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724374 prefixEnd_1724374 := by exact prefixLift 1724374
  have htrace : WordTrace (prefixWord ++ tailWord_1724374) baseStart_1724374 baseEnd_1724374 := by
    simpa [prefixWord, tailWord_1724374, baseEnd_1724374] using wordTrace_append hprefix tailTrace_1724374
  have hstable : (prefixWord ++ tailWord_1724374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724374).length < 2 ^ (prefixWord ++ tailWord_1724374).sum := by decide
  have hdescent : baseEnd_1724374 < baseStart_1724374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724397 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1724397 : Nat := 118140960795 + 1724397 * 2 ^ 59
def prefixEnd_1724397 : Nat := 4983230072969 + 3 ^ 40 * 1724397 * 2
def baseEnd_1724397 : Nat := 885444500171195022507149

theorem tailTrace_1724397 : CollatzResearch.WordTrace tailWord_1724397 prefixEnd_1724397 885444500171195022507149 := by
  unfold tailWord_1724397
  simp only [CollatzResearch.WordTrace]
  refine ⟨62893925533811647406083445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41929283689207764937388963 62893925533811647406083445)
  ·
    refine ⟨5896305518794841944320323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62893925533811647406083445 5896305518794841944320323)
    ·
      refine ⟨8844458278192262916480485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5896305518794841944320323 8844458278192262916480485)
      ·
        refine ⟨1658335927161049296840091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8844458278192262916480485 1658335927161049296840091)
        ·
          refine ⟨2487503890741573945260137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1658335927161049296840091 2487503890741573945260137)
          ·
            refine ⟨1865627918056180458945103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2487503890741573945260137 1865627918056180458945103)
            ·
              refine ⟨2798441877084270688417655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865627918056180458945103 2798441877084270688417655)
              ·
                refine ⟨4197662815626406032626483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798441877084270688417655 4197662815626406032626483)
                ·
                  refine ⟨6296494223439609048939725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4197662815626406032626483 6296494223439609048939725)
                  ·
                    refine ⟨2361185333789853393352397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6296494223439609048939725 2361185333789853393352397)
                    ·
                      refine ⟨885444500171195022507149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2361185333789853393352397 885444500171195022507149)
                      ·
                        rfl

theorem cell23_1724397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1724397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724397 prefixEnd_1724397 := by exact prefixLift 1724397
  have htrace : WordTrace (prefixWord ++ tailWord_1724397) baseStart_1724397 baseEnd_1724397 := by
    simpa [prefixWord, tailWord_1724397, baseEnd_1724397] using wordTrace_append hprefix tailTrace_1724397
  have hstable : (prefixWord ++ tailWord_1724397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724397).length < 2 ^ (prefixWord ++ tailWord_1724397).sum := by decide
  have hdescent : baseEnd_1724397 < baseStart_1724397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724496 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 3]
def baseStart_1724496 : Nat := 118140960795 + 1724496 * 2 ^ 59
def prefixEnd_1724496 : Nat := 4983230072969 + 3 ^ 40 * 1724496 * 2
def baseEnd_1724496 : Nat := 885495334755990135169193

theorem tailTrace_1724496 : CollatzResearch.WordTrace tailWord_1724496 prefixEnd_1724496 885495334755990135169193 := by
  unfold tailWord_1724496
  simp only [CollatzResearch.WordTrace]
  refine ⟨31448768180226493656968671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41931690906968658209291561 31448768180226493656968671)
  ·
    refine ⟨47173152270339740485453007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31448768180226493656968671 47173152270339740485453007)
    ·
      refine ⟨70759728405509610728179511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47173152270339740485453007 70759728405509610728179511)
      ·
        refine ⟨106139592608264416092269267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70759728405509610728179511 106139592608264416092269267)
        ·
          refine ⟨159209388912396624138403901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106139592608264416092269267 159209388912396624138403901)
          ·
            refine ⟨59703520842148734051901463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159209388912396624138403901 59703520842148734051901463)
            ·
              refine ⟨89555281263223101077852195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59703520842148734051901463 89555281263223101077852195)
              ·
                refine ⟨134332921894834651616778293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89555281263223101077852195 134332921894834651616778293)
                ·
                  refine ⟨12593711427640748589072965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134332921894834651616778293 12593711427640748589072965)
                  ·
                    refine ⟨2361320892682640360451181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12593711427640748589072965 2361320892682640360451181)
                    ·
                      refine ⟨885495334755990135169193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2361320892682640360451181 885495334755990135169193)
                      ·
                        rfl

theorem cell23_1724496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 3].length) (baseStart_1724496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724496 prefixEnd_1724496 := by exact prefixLift 1724496
  have htrace : WordTrace (prefixWord ++ tailWord_1724496) baseStart_1724496 baseEnd_1724496 := by
    simpa [prefixWord, tailWord_1724496, baseEnd_1724496] using wordTrace_append hprefix tailTrace_1724496
  have hstable : (prefixWord ++ tailWord_1724496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724496).length < 2 ^ (prefixWord ++ tailWord_1724496).sum := by decide
  have hdescent : baseEnd_1724496 < baseStart_1724496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724530 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 2, 2, 3]
def baseStart_1724530 : Nat := 118140960795 + 1724530 * 2 ^ 59
def prefixEnd_1724530 : Nat := 4983230072969 + 3 ^ 40 * 1724530 * 2
def baseEnd_1724530 : Nat := 885512793098243002144037

theorem tailTrace_1724530 : CollatzResearch.WordTrace tailWord_1724530 prefixEnd_1724530 885512793098243002144037 := by
  unfold tailWord_1724530
  simp only [CollatzResearch.WordTrace]
  refine ⟨15724694110582452780168761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41932517628219874080450029 15724694110582452780168761)
  ·
    refine ⟨11793520582936839585126571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15724694110582452780168761 11793520582936839585126571)
    ·
      refine ⟨17690280874405259377689857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11793520582936839585126571 17690280874405259377689857)
      ·
        refine ⟨13267710655803944533267393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17690280874405259377689857 13267710655803944533267393)
        ·
          refine ⟨9950782991852958399950545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13267710655803944533267393 9950782991852958399950545)
          ·
            refine ⟨7463087243889718799962909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9950782991852958399950545 7463087243889718799962909)
            ·
              refine ⟨2798657716458644549986091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7463087243889718799962909 2798657716458644549986091)
              ·
                refine ⟨4197986574687966824979137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798657716458644549986091 4197986574687966824979137)
                ·
                  refine ⟨3148489931015975118734353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4197986574687966824979137 3148489931015975118734353)
                  ·
                    refine ⟨2361367448261981339050765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3148489931015975118734353 2361367448261981339050765)
                    ·
                      refine ⟨885512793098243002144037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2361367448261981339050765 885512793098243002144037)
                      ·
                        rfl

theorem cell23_1724530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_1724530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724530 prefixEnd_1724530 := by exact prefixLift 1724530
  have htrace : WordTrace (prefixWord ++ tailWord_1724530) baseStart_1724530 baseEnd_1724530 := by
    simpa [prefixWord, tailWord_1724530, baseEnd_1724530] using wordTrace_append hprefix tailTrace_1724530
  have hstable : (prefixWord ++ tailWord_1724530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724530).length < 2 ^ (prefixWord ++ tailWord_1724530).sum := by decide
  have hdescent : baseEnd_1724530 < baseStart_1724530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724537 : List Nat := [1, 2, 1, 3, 4, 2, 2, 3, 1, 4]
def baseStart_1724537 : Nat := 118140960795 + 1724537 * 2 ^ 59
def prefixEnd_1724537 : Nat := 4983230072969 + 3 ^ 40 * 1724537 * 2
def baseEnd_1724537 : Nat := 295172129154274824918835

theorem tailTrace_1724537 : CollatzResearch.WordTrace tailWord_1724537 prefixEnd_1724537 295172129154274824918835 := by
  unfold tailWord_1724537
  simp only [CollatzResearch.WordTrace]
  refine ⟨62899031753304451316179865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41932687835536300877453243 62899031753304451316179865)
  ·
    refine ⟨47174273814978338487134899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62899031753304451316179865 47174273814978338487134899)
    ·
      refine ⟨70761410722467507730702349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47174273814978338487134899 70761410722467507730702349)
      ·
        refine ⟨26535529020925315399013381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70761410722467507730702349 26535529020925315399013381)
        ·
          refine ⟨4975411691423496637315009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26535529020925315399013381 4975411691423496637315009)
          ·
            refine ⟨3731558768567622477986257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4975411691423496637315009 3731558768567622477986257)
            ·
              refine ⟨2798669076425716858489693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3731558768567622477986257 2798669076425716858489693)
              ·
                refine ⟨1049500903659643821933635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2798669076425716858489693 1049500903659643821933635)
                ·
                  refine ⟨1574251355489465732900453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1049500903659643821933635 1574251355489465732900453)
                  ·
                    refine ⟨295172129154274824918835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1574251355489465732900453 295172129154274824918835)
                    ·
                      rfl

theorem cell23_1724537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 1, 4].length) (baseStart_1724537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724537 prefixEnd_1724537 := by exact prefixLift 1724537
  have htrace : WordTrace (prefixWord ++ tailWord_1724537) baseStart_1724537 baseEnd_1724537 := by
    simpa [prefixWord, tailWord_1724537, baseEnd_1724537] using wordTrace_append hprefix tailTrace_1724537
  have hstable : (prefixWord ++ tailWord_1724537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724537).length < 2 ^ (prefixWord ++ tailWord_1724537).sum := by decide
  have hdescent : baseEnd_1724537 < baseStart_1724537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724560 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 3, 1, 3]
def baseStart_1724560 : Nat := 118140960795 + 1724560 * 2 ^ 59
def prefixEnd_1724560 : Nat := 4983230072969 + 3 ^ 40 * 1724560 * 2
def baseEnd_1724560 : Nat := 885528197517877884768899

theorem tailTrace_1724560 : CollatzResearch.WordTrace tailWord_1724560 prefixEnd_1724560 885528197517877884768899 := by
  unfold tailWord_1724560
  simp only [CollatzResearch.WordTrace]
  refine ⟨31449935316110563122133567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41933247088147417496178089 31449935316110563122133567)
  ·
    refine ⟨47174902974165844683200351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31449935316110563122133567 47174902974165844683200351)
    ·
      refine ⟨70762354461248767024800527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47174902974165844683200351 70762354461248767024800527)
      ·
        refine ⟨106143531691873150537200791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70762354461248767024800527 106143531691873150537200791)
        ·
          refine ⟨159215297537809725805801187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106143531691873150537200791 159215297537809725805801187)
          ·
            refine ⟨238822946306714588708701781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159215297537809725805801187 238822946306714588708701781)
            ·
              refine ⟨2798706402031811586430099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 238822946306714588708701781 2798706402031811586430099)
              ·
                refine ⟨4198059603047717379645149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798706402031811586430099 4198059603047717379645149)
                ·
                  refine ⟨1574272351142894017366931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4198059603047717379645149 1574272351142894017366931)
                  ·
                    refine ⟨2361408526714341026050397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1574272351142894017366931 2361408526714341026050397)
                    ·
                      refine ⟨885528197517877884768899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2361408526714341026050397 885528197517877884768899)
                      ·
                        rfl

theorem cell23_1724560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 3, 1, 3].length) (baseStart_1724560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724560 prefixEnd_1724560 := by exact prefixLift 1724560
  have htrace : WordTrace (prefixWord ++ tailWord_1724560) baseStart_1724560 baseEnd_1724560 := by
    simpa [prefixWord, tailWord_1724560, baseEnd_1724560] using wordTrace_append hprefix tailTrace_1724560
  have hstable : (prefixWord ++ tailWord_1724560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724560).length < 2 ^ (prefixWord ++ tailWord_1724560).sum := by decide
  have hdescent : baseEnd_1724560 < baseStart_1724560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724603 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 5]
def baseStart_1724603 : Nat := 118140960795 + 1724603 * 2 ^ 59
def prefixEnd_1724603 : Nat := 4983230072969 + 3 ^ 40 * 1724603 * 2
def baseEnd_1724603 : Nat := 885550277186021216531201

theorem tailTrace_1724603 : CollatzResearch.WordTrace tailWord_1724603 prefixEnd_1724603 885550277186021216531201 := by
  unfold tailWord_1724603
  simp only [CollatzResearch.WordTrace]
  refine ⟨62901438971065344588082463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41934292647376896392054975 62901438971065344588082463)
  ·
    refine ⟨94352158456598016882123695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62901438971065344588082463 94352158456598016882123695)
    ·
      refine ⟨141528237684897025323185543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94352158456598016882123695 141528237684897025323185543)
      ·
        refine ⟨212292356527345537984778315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141528237684897025323185543 212292356527345537984778315)
        ·
          refine ⟨318438534791018306977167473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212292356527345537984778315 318438534791018306977167473)
          ·
            refine ⟨238828901093263730232875605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318438534791018306977167473 238828901093263730232875605)
            ·
              refine ⟨2798776184686684338666511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 238828901093263730232875605 2798776184686684338666511)
              ·
                refine ⟨4198164277030026507999767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798776184686684338666511 4198164277030026507999767)
                ·
                  refine ⟨6297246415545039761999651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4198164277030026507999767 6297246415545039761999651)
                  ·
                    refine ⟨9445869623317559642999477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6297246415545039761999651 9445869623317559642999477)
                    ·
                      refine ⟨885550277186021216531201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9445869623317559642999477 885550277186021216531201)
                      ·
                        rfl

theorem cell23_1724603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 5].length) (baseStart_1724603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724603 prefixEnd_1724603 := by exact prefixLift 1724603
  have htrace : WordTrace (prefixWord ++ tailWord_1724603) baseStart_1724603 baseEnd_1724603 := by
    simpa [prefixWord, tailWord_1724603, baseEnd_1724603] using wordTrace_append hprefix tailTrace_1724603
  have hstable : (prefixWord ++ tailWord_1724603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724603).length < 2 ^ (prefixWord ++ tailWord_1724603).sum := by decide
  have hdescent : baseEnd_1724603 < baseStart_1724603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724637 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1724637 : Nat := 118140960795 + 1724637 * 2 ^ 59
def prefixEnd_1724637 : Nat := 4983230072969 + 3 ^ 40 * 1724637 * 2
def baseEnd_1724637 : Nat := 885567735528274083506045

theorem tailTrace_1724637 : CollatzResearch.WordTrace tailWord_1724637 prefixEnd_1724637 885567735528274083506045 := by
  unfold tailWord_1724637
  simp only [CollatzResearch.WordTrace]
  refine ⟨62902679052942168394820165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41935119368628112263213443 62902679052942168394820165)
  ·
    refine ⟨11794252322426656574028781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62902679052942168394820165 11794252322426656574028781)
    ·
      refine ⟨4422844620909996215260793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11794252322426656574028781 4422844620909996215260793)
      ·
        refine ⟨3317133465682497161445595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4422844620909996215260793 3317133465682497161445595)
        ·
          refine ⟨4975700198523745742168393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3317133465682497161445595 4975700198523745742168393)
          ·
            refine ⟨3731775148892809306626295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4975700198523745742168393 3731775148892809306626295)
            ·
              refine ⟨5597662723339213959939443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3731775148892809306626295 5597662723339213959939443)
              ·
                refine ⟨8396494085008820939909165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5597662723339213959939443 8396494085008820939909165)
                ·
                  refine ⟨3148685281878307852465937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8396494085008820939909165 3148685281878307852465937)
                  ·
                    refine ⟨2361513961408730889349453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3148685281878307852465937 2361513961408730889349453)
                    ·
                      refine ⟨885567735528274083506045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2361513961408730889349453 885567735528274083506045)
                      ·
                        rfl

theorem cell23_1724637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1724637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724637 prefixEnd_1724637 := by exact prefixLift 1724637
  have htrace : WordTrace (prefixWord ++ tailWord_1724637) baseStart_1724637 baseEnd_1724637 := by
    simpa [prefixWord, tailWord_1724637, baseEnd_1724637] using wordTrace_append hprefix tailTrace_1724637
  have hstable : (prefixWord ++ tailWord_1724637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724637).length < 2 ^ (prefixWord ++ tailWord_1724637).sum := by decide
  have hdescent : baseEnd_1724637 < baseStart_1724637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724650 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_1724650 : Nat := 118140960795 + 1724650 * 2 ^ 59
def prefixEnd_1724650 : Nat := 4983230072969 + 3 ^ 40 * 1724650 * 2
def baseEnd_1724650 : Nat := 885574410776782532643485

theorem tailTrace_1724650 : CollatzResearch.WordTrace tailWord_1724650 prefixEnd_1724650 885574410776782532643485 := by
  unfold tailWord_1724650
  simp only [CollatzResearch.WordTrace]
  refine ⟨15725788300473767903760851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41935435467930047743362269 15725788300473767903760851)
  ·
    refine ⟨23588682450710651855641277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15725788300473767903760851 23588682450710651855641277)
    ·
      refine ⟨8845755919016494445865479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23588682450710651855641277 8845755919016494445865479)
      ·
        refine ⟨13268633878524741668798219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8845755919016494445865479 13268633878524741668798219)
        ·
          refine ⟨19902950817787112503197329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13268633878524741668798219 19902950817787112503197329)
          ·
            refine ⟨14927213113340334377397997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19902950817787112503197329 14927213113340334377397997)
            ·
              refine ⟨5597704917502625391524249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14927213113340334377397997 5597704917502625391524249)
              ·
                refine ⟨4198278688126969043643187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5597704917502625391524249 4198278688126969043643187)
                ·
                  refine ⟨6297418032190453565464781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4198278688126969043643187 6297418032190453565464781)
                  ·
                    refine ⟨2361531762071420087049293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6297418032190453565464781 2361531762071420087049293)
                    ·
                      refine ⟨885574410776782532643485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2361531762071420087049293 885574410776782532643485)
                      ·
                        rfl

theorem cell23_1724650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_1724650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724650 prefixEnd_1724650 := by exact prefixLift 1724650
  have htrace : WordTrace (prefixWord ++ tailWord_1724650) baseStart_1724650 baseEnd_1724650 := by
    simpa [prefixWord, tailWord_1724650, baseEnd_1724650] using wordTrace_append hprefix tailTrace_1724650
  have hstable : (prefixWord ++ tailWord_1724650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724650).length < 2 ^ (prefixWord ++ tailWord_1724650).sum := by decide
  have hdescent : baseEnd_1724650 < baseStart_1724650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724668 : List Nat := [2, 2, 2, 1, 4, 3, 2, 2, 1, 2, 2]
def baseStart_1724668 : Nat := 118140960795 + 1724668 * 2 ^ 59
def prefixEnd_1724668 : Nat := 4983230072969 + 3 ^ 40 * 1724668 * 2
def baseEnd_1724668 : Nat := 885583653428563462218403

theorem tailTrace_1724668 : CollatzResearch.WordTrace tailWord_1724668 prefixEnd_1724668 885583653428563462218403 := by
  unfold tailWord_1724668
  simp only [CollatzResearch.WordTrace]
  refine ⟨31451904857914930344599329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41935873143886573792799105 31451904857914930344599329)
  ·
    refine ⟨23588928643436197758449497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31451904857914930344599329 23588928643436197758449497)
    ·
      refine ⟨17691696482577148318837123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23588928643436197758449497 17691696482577148318837123)
      ·
        refine ⟨26537544723865722478255685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17691696482577148318837123 26537544723865722478255685)
        ·
          refine ⟨4975789635724822964672941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26537544723865722478255685 4975789635724822964672941)
          ·
            refine ⟨1865921113396808611752353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4975789635724822964672941 1865921113396808611752353)
            ·
              refine ⟨1399440835047606458814265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1865921113396808611752353 1399440835047606458814265)
              ·
                refine ⟨1049580626285704844110699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1399440835047606458814265 1049580626285704844110699)
                ·
                  refine ⟨1574370939428557266166049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1049580626285704844110699 1574370939428557266166049)
                  ·
                    refine ⟨1180778204571417949624537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1574370939428557266166049 1180778204571417949624537)
                    ·
                      refine ⟨885583653428563462218403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1180778204571417949624537 885583653428563462218403)
                      ·
                        rfl

theorem cell23_1724668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_1724668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724668 prefixEnd_1724668 := by exact prefixLift 1724668
  have htrace : WordTrace (prefixWord ++ tailWord_1724668) baseStart_1724668 baseEnd_1724668 := by
    simpa [prefixWord, tailWord_1724668, baseEnd_1724668] using wordTrace_append hprefix tailTrace_1724668
  have hstable : (prefixWord ++ tailWord_1724668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724668).length < 2 ^ (prefixWord ++ tailWord_1724668).sum := by decide
  have hdescent : baseEnd_1724668 < baseStart_1724668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724673 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_1724673 : Nat := 118140960795 + 1724673 * 2 ^ 59
def prefixEnd_1724673 : Nat := 4983230072969 + 3 ^ 40 * 1724673 * 2
def baseEnd_1724673 : Nat := 885586220831835942655879

theorem tailTrace_1724673 : CollatzResearch.WordTrace tailWord_1724673 prefixEnd_1724673 885586220831835942655879 := by
  unfold tailWord_1724673
  simp only [CollatzResearch.WordTrace]
  refine ⟨62903992080811746543130673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41935994720541164362087115 62903992080811746543130673)
  ·
    refine ⟨47177994060608809907348005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62903992080811746543130673 47177994060608809907348005)
    ·
      refine ⟨8845873886364151857627751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47177994060608809907348005 8845873886364151857627751)
      ·
        refine ⟨13268810829546227786441627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8845873886364151857627751 13268810829546227786441627)
        ·
          refine ⟨19903216244319341679662441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13268810829546227786441627 19903216244319341679662441)
          ·
            refine ⟨14927412183239506259746831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19903216244319341679662441 14927412183239506259746831)
            ·
              refine ⟨22391118274859259389620247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14927412183239506259746831 22391118274859259389620247)
              ·
                refine ⟨33586677412288889084430371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22391118274859259389620247 33586677412288889084430371)
                ·
                  refine ⟨50380016118433333626645557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33586677412288889084430371 50380016118433333626645557)
                  ·
                    refine ⟨4723126511103125027498021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50380016118433333626645557 4723126511103125027498021)
                    ·
                      refine ⟨885586220831835942655879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4723126511103125027498021 885586220831835942655879)
                      ·
                        rfl

theorem cell23_1724673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_1724673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724673 prefixEnd_1724673 := by exact prefixLift 1724673
  have htrace : WordTrace (prefixWord ++ tailWord_1724673) baseStart_1724673 baseEnd_1724673 := by
    simpa [prefixWord, tailWord_1724673, baseEnd_1724673] using wordTrace_append hprefix tailTrace_1724673
  have hstable : (prefixWord ++ tailWord_1724673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724673).length < 2 ^ (prefixWord ++ tailWord_1724673).sum := by decide
  have hdescent : baseEnd_1724673 < baseStart_1724673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724683 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 2, 6]
def baseStart_1724683 : Nat := 118140960795 + 1724683 * 2 ^ 59
def prefixEnd_1724683 : Nat := 4983230072969 + 3 ^ 40 * 1724683 * 2
def baseEnd_1724683 : Nat := 295197118546126967843611

theorem tailTrace_1724683 : CollatzResearch.WordTrace tailWord_1724683 prefixEnd_1724683 295197118546126967843611 := by
  unfold tailWord_1724683
  simp only [CollatzResearch.WordTrace]
  refine ⟨62904356810775518250994703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41936237873850345500663135 62904356810775518250994703)
  ·
    refine ⟨94356535216163277376492055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62904356810775518250994703 94356535216163277376492055)
    ·
      refine ⟨141534802824244916064738083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94356535216163277376492055 141534802824244916064738083)
      ·
        refine ⟨212302204236367374097107125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141534802824244916064738083 212302204236367374097107125)
        ·
          refine ⟨19903331647159441321603793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 212302204236367374097107125 19903331647159441321603793)
          ·
            refine ⟨14927498735369580991202845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19903331647159441321603793 14927498735369580991202845)
            ·
              refine ⟨5597812025763592871701067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14927498735369580991202845 5597812025763592871701067)
              ·
                refine ⟨8396718038645389307551601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5597812025763592871701067 8396718038645389307551601)
                ·
                  refine ⟨6297538528984041980663701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8396718038645389307551601 6297538528984041980663701)
                  ·
                    refine ⟨295197118546126967843611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6297538528984041980663701 295197118546126967843611)
                    ·
                      rfl

theorem cell23_1724683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 6].length) (baseStart_1724683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724683 prefixEnd_1724683 := by exact prefixLift 1724683
  have htrace : WordTrace (prefixWord ++ tailWord_1724683) baseStart_1724683 baseEnd_1724683 := by
    simpa [prefixWord, tailWord_1724683, baseEnd_1724683] using wordTrace_append hprefix tailTrace_1724683
  have hstable : (prefixWord ++ tailWord_1724683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724683).length < 2 ^ (prefixWord ++ tailWord_1724683).sum := by decide
  have hdescent : baseEnd_1724683 < baseStart_1724683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724693 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_1724693 : Nat := 118140960795 + 1724693 * 2 ^ 59
def prefixEnd_1724693 : Nat := 4983230072969 + 3 ^ 40 * 1724693 * 2
def baseEnd_1724693 : Nat := 885596490444925864405787

theorem tailTrace_1724693 : CollatzResearch.WordTrace tailWord_1724693 prefixEnd_1724693 885596490444925864405787 := by
  unfold tailWord_1724693
  simp only [CollatzResearch.WordTrace]
  refine ⟨62904721540739289958858733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41936481027159526639239155 62904721540739289958858733)
  ·
    refine ⟨23589270577777233734572025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62904721540739289958858733 23589270577777233734572025)
    ·
      refine ⟨17691952933332925300929019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23589270577777233734572025 17691952933332925300929019)
      ·
        refine ⟨26537929399999387951393529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17691952933332925300929019 26537929399999387951393529)
        ·
          refine ⟨19903447049999540963545147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26537929399999387951393529 19903447049999540963545147)
          ·
            refine ⟨29855170574999311445317721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19903447049999540963545147 29855170574999311445317721)
            ·
              refine ⟨22391377931249483583988291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29855170574999311445317721 22391377931249483583988291)
              ·
                refine ⟨33587066896874225375982437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22391377931249483583988291 33587066896874225375982437)
                ·
                  refine ⟨6297575043163917257996707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33587066896874225375982437 6297575043163917257996707)
                  ·
                    refine ⟨9446362564745875886995061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6297575043163917257996707 9446362564745875886995061)
                    ·
                      refine ⟨885596490444925864405787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9446362564745875886995061 885596490444925864405787)
                      ·
                        rfl

theorem cell23_1724693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_1724693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724693 prefixEnd_1724693 := by exact prefixLift 1724693
  have htrace : WordTrace (prefixWord ++ tailWord_1724693) baseStart_1724693 baseEnd_1724693 := by
    simpa [prefixWord, tailWord_1724693, baseEnd_1724693] using wordTrace_append hprefix tailTrace_1724693
  have hstable : (prefixWord ++ tailWord_1724693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724693).length < 2 ^ (prefixWord ++ tailWord_1724693).sum := by decide
  have hdescent : baseEnd_1724693 < baseStart_1724693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724707 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 4, 2, 2]
def baseStart_1724707 : Nat := 118140960795 + 1724707 * 2 ^ 59
def prefixEnd_1724707 : Nat := 4983230072969 + 3 ^ 40 * 1724707 * 2
def baseEnd_1724707 : Nat := 885603679174088809630723

theorem tailTrace_1724707 : CollatzResearch.WordTrace tailWord_1724707 prefixEnd_1724707 885603679174088809630723 := by
  unfold tailWord_1724707
  simp only [CollatzResearch.WordTrace]
  refine ⟨62905232162688570349868375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41936821441792380233245583 62905232162688570349868375)
  ·
    refine ⟨94357848244032855524802563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62905232162688570349868375 94357848244032855524802563)
    ·
      refine ⟨141536772366049283287203845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94357848244032855524802563 141536772366049283287203845)
      ·
        refine ⟨26538144818634240616350721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141536772366049283287203845 26538144818634240616350721)
        ·
          refine ⟨19903608613975680462263041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26538144818634240616350721 19903608613975680462263041)
          ·
            refine ⟨14927706460481760346697281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19903608613975680462263041 14927706460481760346697281)
            ·
              refine ⟨11195779845361320260022961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14927706460481760346697281 11195779845361320260022961)
              ·
                refine ⟨8396834884020990195017221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11195779845361320260022961 8396834884020990195017221)
                ·
                  refine ⟨1574406540753935661565729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8396834884020990195017221 1574406540753935661565729)
                  ·
                    refine ⟨1180804905565451746174297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1574406540753935661565729 1180804905565451746174297)
                    ·
                      refine ⟨885603679174088809630723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1180804905565451746174297 885603679174088809630723)
                      ·
                        rfl

theorem cell23_1724707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_1724707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724707 prefixEnd_1724707 := by exact prefixLift 1724707
  have htrace : WordTrace (prefixWord ++ tailWord_1724707) baseStart_1724707 baseEnd_1724707 := by
    simpa [prefixWord, tailWord_1724707, baseEnd_1724707] using wordTrace_append hprefix tailTrace_1724707
  have hstable : (prefixWord ++ tailWord_1724707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724707).length < 2 ^ (prefixWord ++ tailWord_1724707).sum := by decide
  have hdescent : baseEnd_1724707 < baseStart_1724707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724718 : List Nat := [4, 1, 3, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1724718 : Nat := 118140960795 + 1724718 * 2 ^ 59
def prefixEnd_1724718 : Nat := 4983230072969 + 3 ^ 40 * 1724718 * 2
def baseEnd_1724718 : Nat := 885609327461288266593173

theorem tailTrace_1724718 : CollatzResearch.WordTrace tailWord_1724718 prefixEnd_1724718 885609327461288266593173 := by
  unfold tailWord_1724718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7863204170706089903564851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41937088910432479485679205 7863204170706089903564851)
  ·
    refine ⟨11794806256059134855347277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7863204170706089903564851 11794806256059134855347277)
    ·
      refine ⟨4423052346022175570755229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11794806256059134855347277 4423052346022175570755229)
      ·
        refine ⟨1658644629758315839033211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4423052346022175570755229 1658644629758315839033211)
        ·
          refine ⟨2487966944637473758549817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1658644629758315839033211 2487966944637473758549817)
          ·
            refine ⟨1865975208478105318912363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2487966944637473758549817 1865975208478105318912363)
            ·
              refine ⟨2798962812717157978368545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865975208478105318912363 2798962812717157978368545)
              ·
                refine ⟨2099222109537868483776409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2798962812717157978368545 2099222109537868483776409)
                ·
                  refine ⟨1574416582153401362832307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2099222109537868483776409 1574416582153401362832307)
                  ·
                    refine ⟨2361624873230102044248461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1574416582153401362832307 2361624873230102044248461)
                    ·
                      refine ⟨885609327461288266593173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2361624873230102044248461 885609327461288266593173)
                      ·
                        rfl

theorem cell23_1724718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1724718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724718 prefixEnd_1724718 := by exact prefixLift 1724718
  have htrace : WordTrace (prefixWord ++ tailWord_1724718) baseStart_1724718 baseEnd_1724718 := by
    simpa [prefixWord, tailWord_1724718, baseEnd_1724718] using wordTrace_append hprefix tailTrace_1724718
  have hstable : (prefixWord ++ tailWord_1724718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724718).length < 2 ^ (prefixWord ++ tailWord_1724718).sum := by decide
  have hdescent : baseEnd_1724718 < baseStart_1724718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724730 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 7]
def baseStart_1724730 : Nat := 118140960795 + 1724730 * 2 ^ 59
def prefixEnd_1724730 : Nat := 4983230072969 + 3 ^ 40 * 1724730 * 2
def baseEnd_1724730 : Nat := 98401721025460246627013

theorem tailTrace_1724730 : CollatzResearch.WordTrace tailWord_1724730 prefixEnd_1724730 98401721025460246627013 := by
  unfold tailWord_1724730
  simp only [CollatzResearch.WordTrace]
  refine ⟨15726517760401311319488911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41937380694403496851970429 15726517760401311319488911)
  ·
    refine ⟨23589776640601966979233367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15726517760401311319488911 23589776640601966979233367)
    ·
      refine ⟨35384664960902950468850051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23589776640601966979233367 35384664960902950468850051)
      ·
        refine ⟨53076997441354425703275077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35384664960902950468850051 53076997441354425703275077)
        ·
          refine ⟨9951937020253954819364077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53076997441354425703275077 9951937020253954819364077)
          ·
            refine ⟨3731976382595233057261529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9951937020253954819364077 3731976382595233057261529)
            ·
              refine ⟨2798982286946424792946147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3731976382595233057261529 2798982286946424792946147)
              ·
                refine ⟨4198473430419637189419221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798982286946424792946147 4198473430419637189419221)
                ·
                  refine ⟨98401721025460246627013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4198473430419637189419221 98401721025460246627013)
                  ·
                    rfl

theorem cell23_1724730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 7].length) (baseStart_1724730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724730 prefixEnd_1724730 := by exact prefixLift 1724730
  have htrace : WordTrace (prefixWord ++ tailWord_1724730) baseStart_1724730 baseEnd_1724730 := by
    simpa [prefixWord, tailWord_1724730, baseEnd_1724730] using wordTrace_append hprefix tailTrace_1724730
  have hstable : (prefixWord ++ tailWord_1724730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724730).length < 2 ^ (prefixWord ++ tailWord_1724730).sum := by decide
  have hdescent : baseEnd_1724730 < baseStart_1724730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724743 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 3, 7]
def baseStart_1724743 : Nat := 118140960795 + 1724743 * 2 ^ 59
def prefixEnd_1724743 : Nat := 4983230072969 + 3 ^ 40 * 1724743 * 2
def baseEnd_1724743 : Nat := 295207388159216889593519

theorem tailTrace_1724743 : CollatzResearch.WordTrace tailWord_1724743 prefixEnd_1724743 295207388159216889593519 := by
  unfold tailWord_1724743
  simp only [CollatzResearch.WordTrace]
  refine ⟨62906545190558148498178883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41937696793705432332119255 62906545190558148498178883)
  ·
    refine ⟨94359817785837222747268325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62906545190558148498178883 94359817785837222747268325)
    ·
      refine ⟨17692465834844479265112811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94359817785837222747268325 17692465834844479265112811)
      ·
        refine ⟨26538698752266718897669217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17692465834844479265112811 26538698752266718897669217)
        ·
          refine ⟨19904024064200039173251913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26538698752266718897669217 19904024064200039173251913)
          ·
            refine ⟨14928018048150029379938935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19904024064200039173251913 14928018048150029379938935)
            ·
              refine ⟨22392027072225044069908403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14928018048150029379938935 22392027072225044069908403)
              ·
                refine ⟨33588040608337566104862605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22392027072225044069908403 33588040608337566104862605)
                ·
                  refine ⟨12595515228126587289323477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33588040608337566104862605 12595515228126587289323477)
                  ·
                    refine ⟨295207388159216889593519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12595515228126587289323477 295207388159216889593519)
                    ·
                      rfl

theorem cell23_1724743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_1724743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724743 prefixEnd_1724743 := by exact prefixLift 1724743
  have htrace : WordTrace (prefixWord ++ tailWord_1724743) baseStart_1724743 baseEnd_1724743 := by
    simpa [prefixWord, tailWord_1724743, baseEnd_1724743] using wordTrace_append hprefix tailTrace_1724743
  have hstable : (prefixWord ++ tailWord_1724743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724743).length < 2 ^ (prefixWord ++ tailWord_1724743).sum := by decide
  have hdescent : baseEnd_1724743 < baseStart_1724743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724783 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 5]
def baseStart_1724783 : Nat := 118140960795 + 1724783 * 2 ^ 59
def prefixEnd_1724783 : Nat := 4983230072969 + 3 ^ 40 * 1724783 * 2
def baseEnd_1724783 : Nat := 885642703703830512280373

theorem tailTrace_1724783 : CollatzResearch.WordTrace tailWord_1724783 prefixEnd_1724783 885642703703830512280373 := by
  unfold tailWord_1724783
  simp only [CollatzResearch.WordTrace]
  refine ⟨62908004110413235329635003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41938669406942156886423335 62908004110413235329635003)
  ·
    refine ⟨94362006165619852994452505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62908004110413235329635003 94362006165619852994452505)
    ·
      refine ⟨70771504624214889745839379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94362006165619852994452505 70771504624214889745839379)
      ·
        refine ⟨106157256936322334618759069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70771504624214889745839379 106157256936322334618759069)
        ·
          refine ⟨39808971351120875482034651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106157256936322334618759069 39808971351120875482034651)
          ·
            refine ⟨59713457026681313223051977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39808971351120875482034651 59713457026681313223051977)
            ·
              refine ⟨44785092770010984917288983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59713457026681313223051977 44785092770010984917288983)
              ·
                refine ⟨67177639155016477375933475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44785092770010984917288983 67177639155016477375933475)
                ·
                  refine ⟨100766458732524716063900213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67177639155016477375933475 100766458732524716063900213)
                  ·
                    refine ⟨9446855506174192130990645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100766458732524716063900213 9446855506174192130990645)
                    ·
                      refine ⟨885642703703830512280373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9446855506174192130990645 885642703703830512280373)
                      ·
                        rfl

theorem cell23_1724783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_1724783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724783 prefixEnd_1724783 := by exact prefixLift 1724783
  have htrace : WordTrace (prefixWord ++ tailWord_1724783) baseStart_1724783 baseEnd_1724783 := by
    simpa [prefixWord, tailWord_1724783, baseEnd_1724783] using wordTrace_append hprefix tailTrace_1724783
  have hstable : (prefixWord ++ tailWord_1724783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724783).length < 2 ^ (prefixWord ++ tailWord_1724783).sum := by decide
  have hdescent : baseEnd_1724783 < baseStart_1724783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724814 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4]
def baseStart_1724814 : Nat := 118140960795 + 1724814 * 2 ^ 59
def prefixEnd_1724814 : Nat := 4983230072969 + 3 ^ 40 * 1724814 * 2
def baseEnd_1724814 : Nat := 885658621604119890992731

theorem tailTrace_1724814 : CollatzResearch.WordTrace tailWord_1724814 prefixEnd_1724814 885658621604119890992731 := by
  unfold tailWord_1724814
  simp only [CollatzResearch.WordTrace]
  refine ⟨7863641846662615953001687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41939423182200618416008997 7863641846662615953001687)
  ·
    refine ⟨11795462769993923929502531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7863641846662615953001687 11795462769993923929502531)
    ·
      refine ⟨17693194154990885894253797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11795462769993923929502531 17693194154990885894253797)
      ·
        refine ⟨3317473904060791105172587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17693194154990885894253797 3317473904060791105172587)
        ·
          refine ⟨4976210856091186657758881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3317473904060791105172587 4976210856091186657758881)
          ·
            refine ⟨3732158142068389993319161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4976210856091186657758881 3732158142068389993319161)
            ·
              refine ⟨2799118606551292494989371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3732158142068389993319161 2799118606551292494989371)
              ·
                refine ⟨4198677909826938742484057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2799118606551292494989371 4198677909826938742484057)
                ·
                  refine ⟨3149008432370204056863043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4198677909826938742484057 3149008432370204056863043)
                  ·
                    refine ⟨4723512648555306085294565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3149008432370204056863043 4723512648555306085294565)
                    ·
                      refine ⟨885658621604119890992731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4723512648555306085294565 885658621604119890992731)
                      ·
                        rfl

theorem cell23_1724814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_1724814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724814 prefixEnd_1724814 := by exact prefixLift 1724814
  have htrace : WordTrace (prefixWord ++ tailWord_1724814) baseStart_1724814 baseEnd_1724814 := by
    simpa [prefixWord, tailWord_1724814, baseEnd_1724814] using wordTrace_append hprefix tailTrace_1724814
  have hstable : (prefixWord ++ tailWord_1724814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724814).length < 2 ^ (prefixWord ++ tailWord_1724814).sum := by decide
  have hdescent : baseEnd_1724814 < baseStart_1724814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724850 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 5, 5]
def baseStart_1724850 : Nat := 118140960795 + 1724850 * 2 ^ 59
def prefixEnd_1724850 : Nat := 4983230072969 + 3 ^ 40 * 1724850 * 2
def baseEnd_1724850 : Nat := 295225702302560583380855

theorem tailTrace_1724850 : CollatzResearch.WordTrace tailWord_1724850 prefixEnd_1724850 295225702302560583380855 := by
  unfold tailWord_1724850
  simp only [CollatzResearch.WordTrace]
  refine ⟨15727611950292626443081001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41940298534113670514882669 15727611950292626443081001)
  ·
    refine ⟨11795708962719469832310751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15727611950292626443081001 11795708962719469832310751)
    ·
      refine ⟨17693563444079204748466127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11795708962719469832310751 17693563444079204748466127)
      ·
        refine ⟨26540345166118807122699191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17693563444079204748466127 26540345166118807122699191)
        ·
          refine ⟨39810517749178210684048787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26540345166118807122699191 39810517749178210684048787)
          ·
            refine ⟨59715776623767316026073181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39810517749178210684048787 59715776623767316026073181)
            ·
              refine ⟨22393416233912743509777443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59715776623767316026073181 22393416233912743509777443)
              ·
                refine ⟨33590124350869115264666165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22393416233912743509777443 33590124350869115264666165)
                ·
                  refine ⟨3149074157893979556062453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33590124350869115264666165 3149074157893979556062453)
                  ·
                    refine ⟨295225702302560583380855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3149074157893979556062453 295225702302560583380855)
                    ·
                      rfl

theorem cell23_1724850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_1724850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724850 prefixEnd_1724850 := by exact prefixLift 1724850
  have htrace : WordTrace (prefixWord ++ tailWord_1724850) baseStart_1724850 baseEnd_1724850 := by
    simpa [prefixWord, tailWord_1724850, baseEnd_1724850] using wordTrace_append hprefix tailTrace_1724850
  have hstable : (prefixWord ++ tailWord_1724850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724850).length < 2 ^ (prefixWord ++ tailWord_1724850).sum := by decide
  have hdescent : baseEnd_1724850 < baseStart_1724850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724865 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_1724865 : Nat := 118140960795 + 1724865 * 2 ^ 59
def prefixEnd_1724865 : Nat := 4983230072969 + 3 ^ 40 * 1724865 * 2
def baseEnd_1724865 : Nat := 885684809117499191454997

theorem tailTrace_1724865 : CollatzResearch.WordTrace tailWord_1724865 prefixEnd_1724865 885684809117499191454997 := by
  unfold tailWord_1724865
  simp only [CollatzResearch.WordTrace]
  refine ⟨62910994896116163334120049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41940663264077442222746699 62910994896116163334120049)
  ·
    refine ⟨47183246172087122500590037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62910994896116163334120049 47183246172087122500590037)
    ·
      refine ⟨1105857332158291933607579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 47183246172087122500590037 1105857332158291933607579)
      ·
        refine ⟨1658785998237437900411369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1105857332158291933607579 1658785998237437900411369)
        ·
          refine ⟨1244089498678078425308527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1658785998237437900411369 1244089498678078425308527)
          ·
            refine ⟨1866134248017117637962791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244089498678078425308527 1866134248017117637962791)
            ·
              refine ⟨2799201372025676456944187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866134248017117637962791 2799201372025676456944187)
              ·
                refine ⟨4198802058038514685416281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2799201372025676456944187 4198802058038514685416281)
                ·
                  refine ⟨3149101543528886014062211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4198802058038514685416281 3149101543528886014062211)
                  ·
                    refine ⟨4723652315293329021093317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3149101543528886014062211 4723652315293329021093317)
                    ·
                      refine ⟨885684809117499191454997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4723652315293329021093317 885684809117499191454997)
                      ·
                        rfl

theorem cell23_1724865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_1724865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724865 prefixEnd_1724865 := by exact prefixLift 1724865
  have htrace : WordTrace (prefixWord ++ tailWord_1724865) baseStart_1724865 baseEnd_1724865 := by
    simpa [prefixWord, tailWord_1724865, baseEnd_1724865] using wordTrace_append hprefix tailTrace_1724865
  have hstable : (prefixWord ++ tailWord_1724865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724865).length < 2 ^ (prefixWord ++ tailWord_1724865).sum := by decide
  have hdescent : baseEnd_1724865 < baseStart_1724865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724868 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_1724868 : Nat := 118140960795 + 1724868 * 2 ^ 59
def prefixEnd_1724868 : Nat := 4983230072969 + 3 ^ 40 * 1724868 * 2
def baseEnd_1724868 : Nat := 885686349559462679717483

theorem tailTrace_1724868 : CollatzResearch.WordTrace tailWord_1724868 prefixEnd_1724868 885686349559462679717483 := by
  unfold tailWord_1724868
  simp only [CollatzResearch.WordTrace]
  refine ⟨31455552157552647423239629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41940736210070196564319505 31455552157552647423239629)
  ·
    refine ⟨11795832059082242783714861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31455552157552647423239629 11795832059082242783714861)
    ·
      refine ⟨4423437022155841043893073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11795832059082242783714861 4423437022155841043893073)
      ·
        refine ⟨3317577766616880782919805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4423437022155841043893073 3317577766616880782919805)
        ·
          refine ⟨1244091662481330293594927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3317577766616880782919805 1244091662481330293594927)
          ·
            refine ⟨1866137493721995440392391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244091662481330293594927 1866137493721995440392391)
            ·
              refine ⟨2799206240582993160588587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866137493721995440392391 2799206240582993160588587)
              ·
                refine ⟨4198809360874489740882881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2799206240582993160588587 4198809360874489740882881)
                ·
                  refine ⟨3149107020655867305662161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4198809360874489740882881 3149107020655867305662161)
                  ·
                    refine ⟨2361830265491900479246621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3149107020655867305662161 2361830265491900479246621)
                    ·
                      refine ⟨885686349559462679717483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2361830265491900479246621 885686349559462679717483)
                      ·
                        rfl

theorem cell23_1724868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_1724868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724868 prefixEnd_1724868 := by exact prefixLift 1724868
  have htrace : WordTrace (prefixWord ++ tailWord_1724868) baseStart_1724868 baseEnd_1724868 := by
    simpa [prefixWord, tailWord_1724868, baseEnd_1724868] using wordTrace_append hprefix tailTrace_1724868
  have hstable : (prefixWord ++ tailWord_1724868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724868).length < 2 ^ (prefixWord ++ tailWord_1724868).sum := by decide
  have hdescent : baseEnd_1724868 < baseStart_1724868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724884 : List Nat := [2, 4, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_1724884 : Nat := 118140960795 + 1724884 * 2 ^ 59
def prefixEnd_1724884 : Nat := 4983230072969 + 3 ^ 40 * 1724884 * 2
def baseEnd_1724884 : Nat := 295231521749978205705803

theorem tailTrace_1724884 : CollatzResearch.WordTrace tailWord_1724884 prefixEnd_1724884 295231521749978205705803 := by
  unfold tailWord_1724884
  simp only [CollatzResearch.WordTrace]
  refine ⟨31455843941523664789530853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41941125255364886386041137 31455843941523664789530853)
  ·
    refine ⟨5897970739035687148037035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31455843941523664789530853 5897970739035687148037035)
    ·
      refine ⟨8846956108553530722055553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5897970739035687148037035 8846956108553530722055553)
      ·
        refine ⟨6635217081415148041541665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8846956108553530722055553 6635217081415148041541665)
        ·
          refine ⟨4976412811061361031156249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6635217081415148041541665 4976412811061361031156249)
          ·
            refine ⟨3732309608296020773367187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4976412811061361031156249 3732309608296020773367187)
            ·
              refine ⟨5598464412444031160050781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3732309608296020773367187 5598464412444031160050781)
              ·
                refine ⟨2099424154666511685019043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5598464412444031160050781 2099424154666511685019043)
                ·
                  refine ⟨3149136231999767527528565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2099424154666511685019043 3149136231999767527528565)
                  ·
                    refine ⟨295231521749978205705803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3149136231999767527528565 295231521749978205705803)
                    ·
                      rfl

theorem cell23_1724884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_1724884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724884 prefixEnd_1724884 := by exact prefixLift 1724884
  have htrace : WordTrace (prefixWord ++ tailWord_1724884) baseStart_1724884 baseEnd_1724884 := by
    simpa [prefixWord, tailWord_1724884, baseEnd_1724884] using wordTrace_append hprefix tailTrace_1724884
  have hstable : (prefixWord ++ tailWord_1724884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724884).length < 2 ^ (prefixWord ++ tailWord_1724884).sum := by decide
  have hdescent : baseEnd_1724884 < baseStart_1724884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724897 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 4, 4]
def baseStart_1724897 : Nat := 118140960795 + 1724897 * 2 ^ 59
def prefixEnd_1724897 : Nat := 4983230072969 + 3 ^ 40 * 1724897 * 2
def baseEnd_1724897 : Nat := 295233746832814355418283

theorem tailTrace_1724897 : CollatzResearch.WordTrace tailWord_1724897 prefixEnd_1724897 295233746832814355418283 := by
  unfold tailWord_1724897
  simp only [CollatzResearch.WordTrace]
  refine ⟨62912162032000232799284945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41941441354666821866189963 62912162032000232799284945)
  ·
    refine ⟨47184121524000174599463709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62912162032000232799284945 47184121524000174599463709)
    ·
      refine ⟨17694045571500065474798891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47184121524000174599463709 17694045571500065474798891)
      ·
        refine ⟨26541068357250098212198337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17694045571500065474798891 26541068357250098212198337)
        ·
          refine ⟨19905801267937573659148753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26541068357250098212198337 19905801267937573659148753)
          ·
            refine ⟨14929350950953180244361565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19905801267937573659148753 14929350950953180244361565)
            ·
              refine ⟨5598506606607442591635587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14929350950953180244361565 5598506606607442591635587)
              ·
                refine ⟨8397759909911163887453381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5598506606607442591635587 8397759909911163887453381)
                ·
                  refine ⟨1574579983108343228897509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8397759909911163887453381 1574579983108343228897509)
                  ·
                    refine ⟨295233746832814355418283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1574579983108343228897509 295233746832814355418283)
                    ·
                      rfl

theorem cell23_1724897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_1724897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724897 prefixEnd_1724897 := by exact prefixLift 1724897
  have htrace : WordTrace (prefixWord ++ tailWord_1724897) baseStart_1724897 baseEnd_1724897 := by
    simpa [prefixWord, tailWord_1724897, baseEnd_1724897] using wordTrace_append hprefix tailTrace_1724897
  have hstable : (prefixWord ++ tailWord_1724897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724897).length < 2 ^ (prefixWord ++ tailWord_1724897).sum := by decide
  have hdescent : baseEnd_1724897 < baseStart_1724897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724900 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_1724900 : Nat := 118140960795 + 1724900 * 2 ^ 59
def prefixEnd_1724900 : Nat := 4983230072969 + 3 ^ 40 * 1724900 * 2
def baseEnd_1724900 : Nat := 885702780940406554517335

theorem tailTrace_1724900 : CollatzResearch.WordTrace tailWord_1724900 prefixEnd_1724900 885702780940406554517335 := by
  unfold tailWord_1724900
  simp only [CollatzResearch.WordTrace]
  refine ⟨31456135725494682155822077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41941514300659576207762769 31456135725494682155822077)
  ·
    refine ⟨11796050897060505808433279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31456135725494682155822077 11796050897060505808433279)
    ·
      refine ⟨17694076345590758712649919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11796050897060505808433279 17694076345590758712649919)
      ·
        refine ⟨26541114518386138068974879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17694076345590758712649919 26541114518386138068974879)
        ·
          refine ⟨39811671777579207103462319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26541114518386138068974879 39811671777579207103462319)
          ·
            refine ⟨59717507666368810655193479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39811671777579207103462319 59717507666368810655193479)
            ·
              refine ⟨89576261499553215982790219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59717507666368810655193479 89576261499553215982790219)
              ·
                refine ⟨134364392249329823974185329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89576261499553215982790219 134364392249329823974185329)
                ·
                  refine ⟨100773294186997367980638997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134364392249329823974185329 100773294186997367980638997)
                  ·
                    refine ⟨4723748165015501624092453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100773294186997367980638997 4723748165015501624092453)
                    ·
                      refine ⟨885702780940406554517335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4723748165015501624092453 885702780940406554517335)
                      ·
                        rfl

theorem cell23_1724900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_1724900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724900 prefixEnd_1724900 := by exact prefixLift 1724900
  have htrace : WordTrace (prefixWord ++ tailWord_1724900) baseStart_1724900 baseEnd_1724900 := by
    simpa [prefixWord, tailWord_1724900, baseEnd_1724900] using wordTrace_append hprefix tailTrace_1724900
  have hstable : (prefixWord ++ tailWord_1724900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724900).length < 2 ^ (prefixWord ++ tailWord_1724900).sum := by decide
  have hdescent : baseEnd_1724900 < baseStart_1724900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724941 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1724941 : Nat := 118140960795 + 1724941 * 2 ^ 59
def prefixEnd_1724941 : Nat := 4983230072969 + 3 ^ 40 * 1724941 * 2
def baseEnd_1724941 : Nat := 885723833647240894104647

theorem tailTrace_1724941 : CollatzResearch.WordTrace tailWord_1724941 prefixEnd_1724941 885723833647240894104647 := by
  unfold tailWord_1724941
  simp only [CollatzResearch.WordTrace]
  refine ⟨62913766843840828313886677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41942511229227218875924451 62913766843840828313886677)
  ·
    refine ⟨1474541410402519413606719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 62913766843840828313886677 1474541410402519413606719)
    ·
      refine ⟨2211812115603779120410079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1474541410402519413606719 2211812115603779120410079)
      ·
        refine ⟨3317718173405668680615119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2211812115603779120410079 3317718173405668680615119)
        ·
          refine ⟨4976577260108503020922679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3317718173405668680615119 4976577260108503020922679)
          ·
            refine ⟨7464865890162754531384019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4976577260108503020922679 7464865890162754531384019)
            ·
              refine ⟨11197298835244131797076029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7464865890162754531384019 11197298835244131797076029)
              ·
                refine ⟨4198987063216549423903511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11197298835244131797076029 4198987063216549423903511)
                ·
                  refine ⟨6298480594824824135855267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4198987063216549423903511 6298480594824824135855267)
                  ·
                    refine ⟨9447720892237236203782901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6298480594824824135855267 9447720892237236203782901)
                    ·
                      refine ⟨885723833647240894104647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9447720892237236203782901 885723833647240894104647)
                      ·
                        rfl

theorem cell23_1724941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1724941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724941 prefixEnd_1724941 := by exact prefixLift 1724941
  have htrace : WordTrace (prefixWord ++ tailWord_1724941) baseStart_1724941 baseEnd_1724941 := by
    simpa [prefixWord, tailWord_1724941, baseEnd_1724941] using wordTrace_append hprefix tailTrace_1724941
  have hstable : (prefixWord ++ tailWord_1724941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724941).length < 2 ^ (prefixWord ++ tailWord_1724941).sum := by decide
  have hdescent : baseEnd_1724941 < baseStart_1724941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724954 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3]
def baseStart_1724954 : Nat := 118140960795 + 1724954 * 2 ^ 59
def prefixEnd_1724954 : Nat := 4983230072969 + 3 ^ 40 * 1724954 * 2
def baseEnd_1724954 : Nat := 885730508895749343242087

theorem tailTrace_1724954 : CollatzResearch.WordTrace tailWord_1724954 prefixEnd_1724954 885730508895749343242087 := by
  unfold tailWord_1724954
  simp only [CollatzResearch.WordTrace]
  refine ⟨15728560248198432883527479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41942827328529154356073277 15728560248198432883527479)
  ·
    refine ⟨23592840372297649325291219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15728560248198432883527479 23592840372297649325291219)
    ·
      refine ⟨35389260558446473987936829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23592840372297649325291219 35389260558446473987936829)
      ·
        refine ⟨13270972709417427745476311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35389260558446473987936829 13270972709417427745476311)
        ·
          refine ⟨19906459064126141618214467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13270972709417427745476311 19906459064126141618214467)
          ·
            refine ⟨29859688596189212427321701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19906459064126141618214467 29859688596189212427321701)
            ·
              refine ⟨5598691611785477330122819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29859688596189212427321701 5598691611785477330122819)
              ·
                refine ⟨8398037417678215995184229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5598691611785477330122819 8398037417678215995184229)
                ·
                  refine ⟨1574632015814665499097043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8398037417678215995184229 1574632015814665499097043)
                  ·
                    refine ⟨2361948023721998248645565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1574632015814665499097043 2361948023721998248645565)
                    ·
                      refine ⟨885730508895749343242087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2361948023721998248645565 885730508895749343242087)
                      ·
                        rfl

theorem cell23_1724954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_1724954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724954 prefixEnd_1724954 := by exact prefixLift 1724954
  have htrace : WordTrace (prefixWord ++ tailWord_1724954) baseStart_1724954 baseEnd_1724954 := by
    simpa [prefixWord, tailWord_1724954, baseEnd_1724954] using wordTrace_append hprefix tailTrace_1724954
  have hstable : (prefixWord ++ tailWord_1724954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724954).length < 2 ^ (prefixWord ++ tailWord_1724954).sum := by decide
  have hdescent : baseEnd_1724954 < baseStart_1724954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1724997 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 2, 1, 5]
def baseStart_1724997 : Nat := 118140960795 + 1724997 * 2 ^ 59
def prefixEnd_1724997 : Nat := 4983230072969 + 3 ^ 40 * 1724997 * 2
def baseEnd_1724997 : Nat := 885752588563892675004389

theorem tailTrace_1724997 : CollatzResearch.WordTrace tailWord_1724997 prefixEnd_1724997 885752588563892675004389 := by
  unfold tailWord_1724997
  simp only [CollatzResearch.WordTrace]
  refine ⟨62915809331637949877925245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41943872887758633251950163 62915809331637949877925245)
  ·
    refine ⟨23593428499364231204221967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62915809331637949877925245 23593428499364231204221967)
    ·
      refine ⟨35390142749046346806332951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23593428499364231204221967 35390142749046346806332951)
      ·
        refine ⟨53085214123569520209499427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35390142749046346806332951 53085214123569520209499427)
        ·
          refine ⟨79627821185354280314249141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53085214123569520209499427 79627821185354280314249141)
          ·
            refine ⟨7465108236126963779460857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79627821185354280314249141 7465108236126963779460857)
            ·
              refine ⟨5598831177095222834595643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7465108236126963779460857 5598831177095222834595643)
              ·
                refine ⟨8398246765642834251893465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5598831177095222834595643 8398246765642834251893465)
                ·
                  refine ⟨6298685074232125688920099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8398246765642834251893465 6298685074232125688920099)
                  ·
                    refine ⟨9448027611348188533380149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6298685074232125688920099 9448027611348188533380149)
                    ·
                      refine ⟨885752588563892675004389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9448027611348188533380149 885752588563892675004389)
                      ·
                        rfl

theorem cell23_1724997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_1724997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1724997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1724997 prefixEnd_1724997 := by exact prefixLift 1724997
  have htrace : WordTrace (prefixWord ++ tailWord_1724997) baseStart_1724997 baseEnd_1724997 := by
    simpa [prefixWord, tailWord_1724997, baseEnd_1724997] using wordTrace_append hprefix tailTrace_1724997
  have hstable : (prefixWord ++ tailWord_1724997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1724997).length < 2 ^ (prefixWord ++ tailWord_1724997).sum := by decide
  have hdescent : baseEnd_1724997 < baseStart_1724997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1724997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725084 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_1725084 : Nat := 118140960795 + 1725084 * 2 ^ 59
def prefixEnd_1725084 : Nat := 4983230072969 + 3 ^ 40 * 1725084 * 2
def baseEnd_1725084 : Nat := 885797261380833834616489

theorem tailTrace_1725084 : CollatzResearch.WordTrace tailWord_1725084 prefixEnd_1725084 885797261380833834616489 := by
  unfold tailWord_1725084
  simp only [CollatzResearch.WordTrace]
  refine ⟨31459491241161381868171153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41945988321548509157561537 31459491241161381868171153)
  ·
    refine ⟨23594618430871036401128365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31459491241161381868171153 23594618430871036401128365)
    ·
      refine ⟨8847981911576638650423137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23594618430871036401128365 8847981911576638650423137)
      ·
        refine ⟨6635986433682478987817353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8847981911576638650423137 6635986433682478987817353)
        ·
          refine ⟨4976989825261859240863015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6635986433682478987817353 4976989825261859240863015)
          ·
            refine ⟨7465484737892788861294523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4976989825261859240863015 7465484737892788861294523)
            ·
              refine ⟨11198227106839183291941785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7465484737892788861294523 11198227106839183291941785)
              ·
                refine ⟨8398670330129387468956339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11198227106839183291941785 8398670330129387468956339)
                ·
                  refine ⟨12598005495194081203434509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8398670330129387468956339 12598005495194081203434509)
                  ·
                    refine ⟨4724252060697780451287941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12598005495194081203434509 4724252060697780451287941)
                    ·
                      refine ⟨885797261380833834616489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4724252060697780451287941 885797261380833834616489)
                      ·
                        rfl

theorem cell23_1725084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_1725084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725084 prefixEnd_1725084 := by exact prefixLift 1725084
  have htrace : WordTrace (prefixWord ++ tailWord_1725084) baseStart_1725084 baseEnd_1725084 := by
    simpa [prefixWord, tailWord_1725084, baseEnd_1725084] using wordTrace_append hprefix tailTrace_1725084
  have hstable : (prefixWord ++ tailWord_1725084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725084).length < 2 ^ (prefixWord ++ tailWord_1725084).sum := by decide
  have hdescent : baseEnd_1725084 < baseStart_1725084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725104 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 3]
def baseStart_1725104 : Nat := 118140960795 + 1725104 * 2 ^ 59
def prefixEnd_1725104 : Nat := 4983230072969 + 3 ^ 40 * 1725104 * 2
def baseEnd_1725104 : Nat := 885807530993923756366397

theorem tailTrace_1725104 : CollatzResearch.WordTrace tailWord_1725104 prefixEnd_1725104 885807530993923756366397 := by
  unfold tailWord_1725104
  simp only [CollatzResearch.WordTrace]
  refine ⟨31459855971125153576035183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41946474628166871434713577 31459855971125153576035183)
  ·
    refine ⟨47189783956687730364052775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31459855971125153576035183 47189783956687730364052775)
    ·
      refine ⟨70784675935031595546079163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47189783956687730364052775 70784675935031595546079163)
      ·
        refine ⟨106177013902547393319118745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70784675935031595546079163 106177013902547393319118745)
        ·
          refine ⟨79632760426910544989339059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106177013902547393319118745 79632760426910544989339059)
          ·
            refine ⟨119449140640365817484008589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79632760426910544989339059 119449140640365817484008589)
            ·
              refine ⟨44793427740137181556503221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119449140640365817484008589 44793427740137181556503221)
              ·
                refine ⟨4199383850637860770922177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44793427740137181556503221 4199383850637860770922177)
                ·
                  refine ⟨3149537887978395578191633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4199383850637860770922177 3149537887978395578191633)
                  ·
                    refine ⟨2362153415983796683643725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3149537887978395578191633 2362153415983796683643725)
                    ·
                      refine ⟨885807530993923756366397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2362153415983796683643725 885807530993923756366397)
                      ·
                        rfl

theorem cell23_1725104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 3].length) (baseStart_1725104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725104 prefixEnd_1725104 := by exact prefixLift 1725104
  have htrace : WordTrace (prefixWord ++ tailWord_1725104) baseStart_1725104 baseEnd_1725104 := by
    simpa [prefixWord, tailWord_1725104, baseEnd_1725104] using wordTrace_append hprefix tailTrace_1725104
  have hstable : (prefixWord ++ tailWord_1725104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725104).length < 2 ^ (prefixWord ++ tailWord_1725104).sum := by decide
  have hdescent : baseEnd_1725104 < baseStart_1725104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725107 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 8]
def baseStart_1725107 : Nat := 118140960795 + 1725107 * 2 ^ 59
def prefixEnd_1725107 : Nat := 4983230072969 + 3 ^ 40 * 1725107 * 2
def baseEnd_1725107 : Nat := 98423230159543027180987

theorem tailTrace_1725107 : CollatzResearch.WordTrace tailWord_1725107 prefixEnd_1725107 98423230159543027180987 := by
  unfold tailWord_1725107
  simp only [CollatzResearch.WordTrace]
  refine ⟨62919821361239438664429575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41946547574159625776286383 62919821361239438664429575)
  ·
    refine ⟨94379732041859157996644363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62919821361239438664429575 94379732041859157996644363)
    ·
      refine ⟨141569598062788736994966545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94379732041859157996644363 141569598062788736994966545)
      ·
        refine ⟨106177198547091552746224909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141569598062788736994966545 106177198547091552746224909)
        ·
          refine ⟨39816449455159332279834341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106177198547091552746224909 39816449455159332279834341)
          ·
            refine ⟨7465584272842374802468939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39816449455159332279834341 7465584272842374802468939)
            ·
              refine ⟨11198376409263562203703409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7465584272842374802468939 11198376409263562203703409)
              ·
                refine ⟨8398782306947671652777557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11198376409263562203703409 8398782306947671652777557)
                ·
                  refine ⟨98423230159543027180987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8398782306947671652777557 98423230159543027180987)
                  ·
                    rfl

theorem cell23_1725107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 8].length) (baseStart_1725107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725107 prefixEnd_1725107 := by exact prefixLift 1725107
  have htrace : WordTrace (prefixWord ++ tailWord_1725107) baseStart_1725107 baseEnd_1725107 := by
    simpa [prefixWord, tailWord_1725107, baseEnd_1725107] using wordTrace_append hprefix tailTrace_1725107
  have hstable : (prefixWord ++ tailWord_1725107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725107).length < 2 ^ (prefixWord ++ tailWord_1725107).sum := by decide
  have hdescent : baseEnd_1725107 < baseStart_1725107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725124 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 8]
def baseStart_1725124 : Nat := 118140960795 + 1725124 * 2 ^ 59
def prefixEnd_1725124 : Nat := 4983230072969 + 3 ^ 40 * 1725124 * 2
def baseEnd_1725124 : Nat := 98424200067445964235145

theorem tailTrace_1725124 : CollatzResearch.WordTrace tailWord_1725124 prefixEnd_1725124 98424200067445964235145 := by
  unfold tailWord_1725124
  simp only [CollatzResearch.WordTrace]
  refine ⟨31460220701088925283899213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41946960934785233711865617 31460220701088925283899213)
  ·
    refine ⟨11797582762908346981462205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31460220701088925283899213 11797582762908346981462205)
    ·
      refine ⟨4424093536090630118048327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11797582762908346981462205 4424093536090630118048327)
      ·
        refine ⟨6636140304135945177072491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4424093536090630118048327 6636140304135945177072491)
        ·
          refine ⟨9954210456203917765608737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6636140304135945177072491 9954210456203917765608737)
          ·
            refine ⟨7465657842152938324206553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9954210456203917765608737 7465657842152938324206553)
            ·
              refine ⟨5599243381614703743154915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7465657842152938324206553 5599243381614703743154915)
              ·
                refine ⟨8398865072422055614732373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5599243381614703743154915 8398865072422055614732373)
                ·
                  refine ⟨98424200067445964235145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8398865072422055614732373 98424200067445964235145)
                  ·
                    rfl

theorem cell23_1725124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_1725124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725124 prefixEnd_1725124 := by exact prefixLift 1725124
  have htrace : WordTrace (prefixWord ++ tailWord_1725124) baseStart_1725124 baseEnd_1725124 := by
    simpa [prefixWord, tailWord_1725124, baseEnd_1725124] using wordTrace_append hprefix tailTrace_1725124
  have hstable : (prefixWord ++ tailWord_1725124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725124).length < 2 ^ (prefixWord ++ tailWord_1725124).sum := by decide
  have hdescent : baseEnd_1725124 < baseStart_1725124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725127 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_1725127 : Nat := 118140960795 + 1725127 * 2 ^ 59
def prefixEnd_1725127 : Nat := 4983230072969 + 3 ^ 40 * 1725127 * 2
def baseEnd_1725127 : Nat := 885819341048977166378791

theorem tailTrace_1725127 : CollatzResearch.WordTrace tailWord_1725127 prefixEnd_1725127 885819341048977166378791 := by
  unfold tailWord_1725127
  simp only [CollatzResearch.WordTrace]
  refine ⟨62920550821166982080157635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41947033880777988053438423 62920550821166982080157635)
  ·
    refine ⟨94380826231750473120236453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62920550821166982080157635 94380826231750473120236453)
    ·
      refine ⟨17696404918453213710044335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94380826231750473120236453 17696404918453213710044335)
      ·
        refine ⟨26544607377679820565066503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17696404918453213710044335 26544607377679820565066503)
        ·
          refine ⟨39816911066519730847599755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26544607377679820565066503 39816911066519730847599755)
          ·
            refine ⟨59725366599779596271399633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39816911066519730847599755 59725366599779596271399633)
            ·
              refine ⟨44794024949834697203549725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59725366599779596271399633 44794024949834697203549725)
              ·
                refine ⟨16797759356188011451331147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44794024949834697203549725 16797759356188011451331147)
                ·
                  refine ⟨25196639034282017176996721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16797759356188011451331147 25196639034282017176996721)
                  ·
                    refine ⟨18897479275711512882747541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25196639034282017176996721 18897479275711512882747541)
                    ·
                      refine ⟨885819341048977166378791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18897479275711512882747541 885819341048977166378791)
                      ·
                        rfl

theorem cell23_1725127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_1725127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725127 prefixEnd_1725127 := by exact prefixLift 1725127
  have htrace : WordTrace (prefixWord ++ tailWord_1725127) baseStart_1725127 baseEnd_1725127 := by
    simpa [prefixWord, tailWord_1725127, baseEnd_1725127] using wordTrace_append hprefix tailTrace_1725127
  have hstable : (prefixWord ++ tailWord_1725127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725127).length < 2 ^ (prefixWord ++ tailWord_1725127).sum := by decide
  have hdescent : baseEnd_1725127 < baseStart_1725127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725161 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 2, 3, 2]
def baseStart_1725161 : Nat := 118140960795 + 1725161 * 2 ^ 59
def prefixEnd_1725161 : Nat := 4983230072969 + 3 ^ 40 * 1725161 * 2
def baseEnd_1725161 : Nat := 885836799391230033353635

theorem tailTrace_1725161 : CollatzResearch.WordTrace tailWord_1725161 prefixEnd_1725161 885836799391230033353635 := by
  unfold tailWord_1725161
  simp only [CollatzResearch.WordTrace]
  refine ⟨62921790903043805886895337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41947860602029203924596891 62921790903043805886895337)
  ·
    refine ⟨47191343177282854415171503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62921790903043805886895337 47191343177282854415171503)
    ·
      refine ⟨70787014765924281622757255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47191343177282854415171503 70787014765924281622757255)
      ·
        refine ⟨106180522148886422434135883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70787014765924281622757255 106180522148886422434135883)
        ·
          refine ⟨159270783223329633651203825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106180522148886422434135883 159270783223329633651203825)
          ·
            refine ⟨119453087417497225238402869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159270783223329633651203825 119453087417497225238402869)
            ·
              refine ⟨11198726945390364866100269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119453087417497225238402869 11198726945390364866100269)
              ·
                refine ⟨4199522604521386824787601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11198726945390364866100269 4199522604521386824787601)
                ·
                  refine ⟨3149641953391040118590701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4199522604521386824787601 3149641953391040118590701)
                  ·
                    refine ⟨1181115732521640044471513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3149641953391040118590701 1181115732521640044471513)
                    ·
                      refine ⟨885836799391230033353635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1181115732521640044471513 885836799391230033353635)
                      ·
                        rfl

theorem cell23_1725161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 3, 2].length) (baseStart_1725161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725161 prefixEnd_1725161 := by exact prefixLift 1725161
  have htrace : WordTrace (prefixWord ++ tailWord_1725161) baseStart_1725161 baseEnd_1725161 := by
    simpa [prefixWord, tailWord_1725161, baseEnd_1725161] using wordTrace_append hprefix tailTrace_1725161
  have hstable : (prefixWord ++ tailWord_1725161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725161).length < 2 ^ (prefixWord ++ tailWord_1725161).sum := by decide
  have hdescent : baseEnd_1725161 < baseStart_1725161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725168 : List Nat := [2, 1, 1, 1, 3, 1, 4, 5, 1, 1, 3]
def baseStart_1725168 : Nat := 118140960795 + 1725168 * 2 ^ 59
def prefixEnd_1725168 : Nat := 4983230072969 + 3 ^ 40 * 1725168 * 2
def baseEnd_1725168 : Nat := 885840393755811505966103

theorem tailTrace_1725168 : CollatzResearch.WordTrace tailWord_1725168 prefixEnd_1725168 885840393755811505966103 := by
  unfold tailWord_1725168
  simp only [CollatzResearch.WordTrace]
  refine ⟨31461023107009223041200079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41948030809345630721600105 31461023107009223041200079)
  ·
    refine ⟨47191534660513834561800119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31461023107009223041200079 47191534660513834561800119)
    ·
      refine ⟨70787301990770751842700179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47191534660513834561800119 70787301990770751842700179)
      ·
        refine ⟨106180952986156127764050269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70787301990770751842700179 106180952986156127764050269)
        ·
          refine ⟨39817857369808547911518851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106180952986156127764050269 39817857369808547911518851)
          ·
            refine ⟨59726786054712821867278277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39817857369808547911518851 59726786054712821867278277)
            ·
              refine ⟨11198772385258654100114677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59726786054712821867278277 11198772385258654100114677)
              ·
                refine ⟨1049884911117998821885751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11198772385258654100114677 1049884911117998821885751)
                ·
                  refine ⟨1574827366676998232828627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1049884911117998821885751 1574827366676998232828627)
                  ·
                    refine ⟨2362241050015497349242941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1574827366676998232828627 2362241050015497349242941)
                    ·
                      refine ⟨885840393755811505966103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2362241050015497349242941 885840393755811505966103)
                      ·
                        rfl

theorem cell23_1725168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 1, 1, 3].length) (baseStart_1725168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725168 prefixEnd_1725168 := by exact prefixLift 1725168
  have htrace : WordTrace (prefixWord ++ tailWord_1725168) baseStart_1725168 baseEnd_1725168 := by
    simpa [prefixWord, tailWord_1725168, baseEnd_1725168] using wordTrace_append hprefix tailTrace_1725168
  have hstable : (prefixWord ++ tailWord_1725168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725168).length < 2 ^ (prefixWord ++ tailWord_1725168).sum := by decide
  have hdescent : baseEnd_1725168 < baseStart_1725168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725191 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1725191 : Nat := 118140960795 + 1725191 * 2 ^ 59
def prefixEnd_1725191 : Nat := 4983230072969 + 3 ^ 40 * 1725191 * 2
def baseEnd_1725191 : Nat := 885852203810864915978497

theorem tailTrace_1725191 : CollatzResearch.WordTrace tailWord_1725191 prefixEnd_1725191 885852203810864915978497 := by
  unfold tailWord_1725191
  simp only [CollatzResearch.WordTrace]
  refine ⟨62922885092935121010487427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41948590061956747340324951 62922885092935121010487427)
  ·
    refine ⟨94384327639402681515731141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62922885092935121010487427 94384327639402681515731141)
    ·
      refine ⟨17697061432388002784199589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94384327639402681515731141 17697061432388002784199589)
      ·
        refine ⟨3318199018572750522037423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17697061432388002784199589 3318199018572750522037423)
        ·
          refine ⟨4977298527859125783056135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3318199018572750522037423 4977298527859125783056135)
          ·
            refine ⟨7465947791788688674584203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4977298527859125783056135 7465947791788688674584203)
            ·
              refine ⟨11198921687683033011876305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7465947791788688674584203 11198921687683033011876305)
              ·
                refine ⟨8399191265762274758907229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11198921687683033011876305 8399191265762274758907229)
                ·
                  refine ⟨3149696724660853034590211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8399191265762274758907229 3149696724660853034590211)
                  ·
                    refine ⟨4724545086991279551885317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3149696724660853034590211 4724545086991279551885317)
                    ·
                      refine ⟨885852203810864915978497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4724545086991279551885317 885852203810864915978497)
                      ·
                        rfl

theorem cell23_1725191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1725191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725191 prefixEnd_1725191 := by exact prefixLift 1725191
  have htrace : WordTrace (prefixWord ++ tailWord_1725191) baseStart_1725191 baseEnd_1725191 := by
    simpa [prefixWord, tailWord_1725191, baseEnd_1725191] using wordTrace_append hprefix tailTrace_1725191
  have hstable : (prefixWord ++ tailWord_1725191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725191).length < 2 ^ (prefixWord ++ tailWord_1725191).sum := by decide
  have hdescent : baseEnd_1725191 < baseStart_1725191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725194 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_1725194 : Nat := 118140960795 + 1725194 * 2 ^ 59
def prefixEnd_1725194 : Nat := 4983230072969 + 3 ^ 40 * 1725194 * 2
def baseEnd_1725194 : Nat := 885853744252828404240983

theorem tailTrace_1725194 : CollatzResearch.WordTrace tailWord_1725194 prefixEnd_1725194 885853744252828404240983 := by
  unfold tailWord_1725194
  simp only [CollatzResearch.WordTrace]
  refine ⟨15730748627981063130711659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41948663007949501681897757 15730748627981063130711659)
  ·
    refine ⟨23596122941971594696067489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15730748627981063130711659 23596122941971594696067489)
    ·
      refine ⟨17697092206478696022050617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23596122941971594696067489 17697092206478696022050617)
      ·
        refine ⟨13272819154859022016537963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17697092206478696022050617 13272819154859022016537963)
        ·
          refine ⟨19909228732288533024806945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13272819154859022016537963 19909228732288533024806945)
          ·
            refine ⟨14931921549216399768605209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19909228732288533024806945 14931921549216399768605209)
            ·
              refine ⟨11198941161912299826453907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14931921549216399768605209 11198941161912299826453907)
              ·
                refine ⟨16798411742868449739680861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11198941161912299826453907 16798411742868449739680861)
                ·
                  refine ⟨6299404403575668652380323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16798411742868449739680861 6299404403575668652380323)
                  ·
                    refine ⟨9449106605363502978570485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6299404403575668652380323 9449106605363502978570485)
                    ·
                      refine ⟨885853744252828404240983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9449106605363502978570485 885853744252828404240983)
                      ·
                        rfl

theorem cell23_1725194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_1725194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725194 prefixEnd_1725194 := by exact prefixLift 1725194
  have htrace : WordTrace (prefixWord ++ tailWord_1725194) baseStart_1725194 baseEnd_1725194 := by
    simpa [prefixWord, tailWord_1725194, baseEnd_1725194] using wordTrace_append hprefix tailTrace_1725194
  have hstable : (prefixWord ++ tailWord_1725194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725194).length < 2 ^ (prefixWord ++ tailWord_1725194).sum := by decide
  have hdescent : baseEnd_1725194 < baseStart_1725194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725201 : List Nat := [1, 2, 2, 1, 1, 3, 4, 3, 2, 4]
def baseStart_1725201 : Nat := 118140960795 + 1725201 * 2 ^ 59
def prefixEnd_1725201 : Nat := 4983230072969 + 3 ^ 40 * 1725201 * 2
def baseEnd_1725201 : Nat := 295285779539136625617817

theorem tailTrace_1725201 : CollatzResearch.WordTrace tailWord_1725201 prefixEnd_1725201 295285779539136625617817 := by
  unfold tailWord_1725201
  simp only [CollatzResearch.WordTrace]
  refine ⟨62923249822898892718351457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41948833215265928478900971 62923249822898892718351457)
  ·
    refine ⟨47192437367174169538763593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62923249822898892718351457 47192437367174169538763593)
    ·
      refine ⟨35394328025380627154072695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47192437367174169538763593 35394328025380627154072695)
      ·
        refine ⟨53091492038070940731109043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35394328025380627154072695 53091492038070940731109043)
        ·
          refine ⟨79637238057106411096663565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53091492038070940731109043 79637238057106411096663565)
          ·
            refine ⟨29863964271414904161248837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79637238057106411096663565 29863964271414904161248837)
            ·
              refine ⟨5599493300890294530234157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29863964271414904161248837 5599493300890294530234157)
              ·
                refine ⟨2099809987833860448837809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5599493300890294530234157 2099809987833860448837809)
                ·
                  refine ⟨1574857490875395336628357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2099809987833860448837809 1574857490875395336628357)
                  ·
                    refine ⟨295285779539136625617817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1574857490875395336628357 295285779539136625617817)
                    ·
                      rfl

theorem cell23_1725201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_1725201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725201 prefixEnd_1725201 := by exact prefixLift 1725201
  have htrace : WordTrace (prefixWord ++ tailWord_1725201) baseStart_1725201 baseEnd_1725201 := by
    simpa [prefixWord, tailWord_1725201, baseEnd_1725201] using wordTrace_append hprefix tailTrace_1725201
  have hstable : (prefixWord ++ tailWord_1725201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725201).length < 2 ^ (prefixWord ++ tailWord_1725201).sum := by decide
  have hdescent : baseEnd_1725201 < baseStart_1725201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725252 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 1, 6]
def baseStart_1725252 : Nat := 118140960795 + 1725252 * 2 ^ 59
def prefixEnd_1725252 : Nat := 4983230072969 + 3 ^ 40 * 1725252 * 2
def baseEnd_1725252 : Nat := 295294508710263059105239

theorem tailTrace_1725252 : CollatzResearch.WordTrace tailWord_1725252 prefixEnd_1725252 295294508710263059105239 := by
  unfold tailWord_1725252
  simp only [CollatzResearch.WordTrace]
  refine ⟨31462554972857064214229005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41950073297142752285638673 31462554972857064214229005)
  ·
    refine ⟨11798458114821399080335877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31462554972857064214229005 11798458114821399080335877)
    ·
      refine ⟨2212210896529012327562977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11798458114821399080335877 2212210896529012327562977)
      ·
        refine ⟨1659158172396759245672233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2212210896529012327562977 1659158172396759245672233)
        ·
          refine ⟨1244368629297569434254175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1659158172396759245672233 1244368629297569434254175)
          ·
            refine ⟨1866552943946354151381263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244368629297569434254175 1866552943946354151381263)
            ·
              refine ⟨2799829415919531227071895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866552943946354151381263 2799829415919531227071895)
              ·
                refine ⟨4199744123879296840607843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2799829415919531227071895 4199744123879296840607843)
                ·
                  refine ⟨6299616185818945260911765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4199744123879296840607843 6299616185818945260911765)
                  ·
                    refine ⟨295294508710263059105239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6299616185818945260911765 295294508710263059105239)
                    ·
                      rfl

theorem cell23_1725252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_1725252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725252 prefixEnd_1725252 := by exact prefixLift 1725252
  have htrace : WordTrace (prefixWord ++ tailWord_1725252) baseStart_1725252 baseEnd_1725252 := by
    simpa [prefixWord, tailWord_1725252, baseEnd_1725252] using wordTrace_append hprefix tailTrace_1725252
  have hstable : (prefixWord ++ tailWord_1725252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725252).length < 2 ^ (prefixWord ++ tailWord_1725252).sum := by decide
  have hdescent : baseEnd_1725252 < baseStart_1725252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725264 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 4]
def baseStart_1725264 : Nat := 118140960795 + 1725264 * 2 ^ 59
def prefixEnd_1725264 : Nat := 4983230072969 + 3 ^ 40 * 1725264 * 2
def baseEnd_1725264 : Nat := 885889687898643130365661

theorem tailTrace_1725264 : CollatzResearch.WordTrace tailWord_1725264 prefixEnd_1725264 885889687898643130365661 := by
  unfold tailWord_1725264
  simp only [CollatzResearch.WordTrace]
  refine ⟨31462773810835327238947423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41950365081113769651929897 31462773810835327238947423)
  ·
    refine ⟨47194160716252990858421135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31462773810835327238947423 47194160716252990858421135)
    ·
      refine ⟨70791241074379486287631703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47194160716252990858421135 70791241074379486287631703)
      ·
        refine ⟨106186861611569229431447555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70791241074379486287631703 106186861611569229431447555)
        ·
          refine ⟨159280292417353844147171333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106186861611569229431447555 159280292417353844147171333)
          ·
            refine ⟨29865054828253845777594625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159280292417353844147171333 29865054828253845777594625)
            ·
              refine ⟨22398791121190384333195969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29865054828253845777594625 22398791121190384333195969)
              ·
                refine ⟨16799093340892788249896977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22398791121190384333195969 16799093340892788249896977)
                ·
                  refine ⟨12599320005669591187422733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16799093340892788249896977 12599320005669591187422733)
                  ·
                    refine ⟨4724745002126096695283525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12599320005669591187422733 4724745002126096695283525)
                    ·
                      refine ⟨885889687898643130365661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4724745002126096695283525 885889687898643130365661)
                      ·
                        rfl

theorem cell23_1725264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_1725264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725264 prefixEnd_1725264 := by exact prefixLift 1725264
  have htrace : WordTrace (prefixWord ++ tailWord_1725264) baseStart_1725264 baseEnd_1725264 := by
    simpa [prefixWord, tailWord_1725264, baseEnd_1725264] using wordTrace_append hprefix tailTrace_1725264
  have hstable : (prefixWord ++ tailWord_1725264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725264).length < 2 ^ (prefixWord ++ tailWord_1725264).sum := by decide
  have hdescent : baseEnd_1725264 < baseStart_1725264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725304 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 7]
def baseStart_1725304 : Nat := 118140960795 + 1725304 * 2 ^ 59
def prefixEnd_1725304 : Nat := 4983230072969 + 3 ^ 40 * 1725304 * 2
def baseEnd_1725304 : Nat := 98434469680535885985053

theorem tailTrace_1725304 : CollatzResearch.WordTrace tailWord_1725304 prefixEnd_1725304 98434469680535885985053 := by
  unfold tailWord_1725304
  simp only [CollatzResearch.WordTrace]
  refine ⟨31463503270762870654675483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41951337694350494206233977 31463503270762870654675483)
  ·
    refine ⟨47195254906144305982013225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31463503270762870654675483 47195254906144305982013225)
    ·
      refine ⟨35396441179608229486509919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47195254906144305982013225 35396441179608229486509919)
      ·
        refine ⟨53094661769412344229764879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35396441179608229486509919 53094661769412344229764879)
        ·
          refine ⟨79641992654118516344647319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53094661769412344229764879 79641992654118516344647319)
          ·
            refine ⟨119462988981177774516970979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79641992654118516344647319 119462988981177774516970979)
            ·
              refine ⟨179194483471766661775456469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119462988981177774516970979 179194483471766661775456469)
              ·
                refine ⟨4199870706369531135362261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 179194483471766661775456469 4199870706369531135362261)
                ·
                  refine ⟨98434469680535885985053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4199870706369531135362261 98434469680535885985053)
                  ·
                    rfl

theorem cell23_1725304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 7].length) (baseStart_1725304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725304 prefixEnd_1725304 := by exact prefixLift 1725304
  have htrace : WordTrace (prefixWord ++ tailWord_1725304) baseStart_1725304 baseEnd_1725304 := by
    simpa [prefixWord, tailWord_1725304, baseEnd_1725304] using wordTrace_append hprefix tailTrace_1725304
  have hstable : (prefixWord ++ tailWord_1725304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725304).length < 2 ^ (prefixWord ++ tailWord_1725304).sum := by decide
  have hdescent : baseEnd_1725304 < baseStart_1725304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725315 : List Nat := [1, 1, 1, 3, 4, 1, 3, 3, 2, 2, 2]
def baseStart_1725315 : Nat := 118140960795 + 1725315 * 2 ^ 59
def prefixEnd_1725315 : Nat := 4983230072969 + 3 ^ 40 * 1725315 * 2
def baseEnd_1725315 : Nat := 885915875412022430827927

theorem tailTrace_1725315 : CollatzResearch.WordTrace tailWord_1725315 prefixEnd_1725315 885915875412022430827927 := by
  unfold tailWord_1725315
  simp only [CollatzResearch.WordTrace]
  refine ⟨62927407744485890188001399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41951605162990593458667599 62927407744485890188001399)
  ·
    refine ⟨94391111616728835282002099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62927407744485890188001399 94391111616728835282002099)
    ·
      refine ⟨141586667425093252923003149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94391111616728835282002099 141586667425093252923003149)
      ·
        refine ⟨53095000284409969846126181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141586667425093252923003149 53095000284409969846126181)
        ·
          refine ⟨9955312553326869346148659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53095000284409969846126181 9955312553326869346148659)
          ·
            refine ⟨14932968829990304019222989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9955312553326869346148659 14932968829990304019222989)
            ·
              refine ⟨5599863311246364007208621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14932968829990304019222989 5599863311246364007208621)
              ·
                refine ⟨2099948741717386502703233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5599863311246364007208621 2099948741717386502703233)
                ·
                  refine ⟨1574961556288039877027425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2099948741717386502703233 1574961556288039877027425)
                  ·
                    refine ⟨1181221167216029907770569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1574961556288039877027425 1181221167216029907770569)
                    ·
                      refine ⟨885915875412022430827927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1181221167216029907770569 885915875412022430827927)
                      ·
                        rfl

theorem cell23_1725315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 2, 2].length) (baseStart_1725315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725315 prefixEnd_1725315 := by exact prefixLift 1725315
  have htrace : WordTrace (prefixWord ++ tailWord_1725315) baseStart_1725315 baseEnd_1725315 := by
    simpa [prefixWord, tailWord_1725315, baseEnd_1725315] using wordTrace_append hprefix tailTrace_1725315
  have hstable : (prefixWord ++ tailWord_1725315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725315).length < 2 ^ (prefixWord ++ tailWord_1725315).sum := by decide
  have hdescent : baseEnd_1725315 < baseStart_1725315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725366 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_1725366 : Nat := 118140960795 + 1725366 * 2 ^ 59
def prefixEnd_1725366 : Nat := 4983230072969 + 3 ^ 40 * 1725366 * 2
def baseEnd_1725366 : Nat := 885942062925401731290193

theorem tailTrace_1725366 : CollatzResearch.WordTrace tailWord_1725366 prefixEnd_1725366 885942062925401731290193 := by
  unfold tailWord_1725366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3933079241706320368631747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41952845244867417265405301 3933079241706320368631747)
  ·
    refine ⟨5899618862559480552947621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3933079241706320368631747 5899618862559480552947621)
    ·
      refine ⟨1106178536729902603677679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5899618862559480552947621 1106178536729902603677679)
      ·
        refine ⟨1659267805094853905516519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1106178536729902603677679 1659267805094853905516519)
        ·
          refine ⟨2488901707642280858274779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1659267805094853905516519 2488901707642280858274779)
          ·
            refine ⟨3733352561463421287412169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2488901707642280858274779 3733352561463421287412169)
            ·
              refine ⟨2800014421097565965559127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3733352561463421287412169 2800014421097565965559127)
              ·
                refine ⟨4200021631646348948338691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2800014421097565965559127 4200021631646348948338691)
                ·
                  refine ⟨6300032447469523422508037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4200021631646348948338691 6300032447469523422508037)
                  ·
                    refine ⟨1181256083900535641720257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6300032447469523422508037 1181256083900535641720257)
                    ·
                      refine ⟨885942062925401731290193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1181256083900535641720257 885942062925401731290193)
                      ·
                        rfl

theorem cell23_1725366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_1725366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725366 prefixEnd_1725366 := by exact prefixLift 1725366
  have htrace : WordTrace (prefixWord ++ tailWord_1725366) baseStart_1725366 baseEnd_1725366 := by
    simpa [prefixWord, tailWord_1725366, baseEnd_1725366] using wordTrace_append hprefix tailTrace_1725366
  have hstable : (prefixWord ++ tailWord_1725366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725366).length < 2 ^ (prefixWord ++ tailWord_1725366).sum := by decide
  have hdescent : baseEnd_1725366 < baseStart_1725366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725388 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 1, 6, 2]
def baseStart_1725388 : Nat := 118140960795 + 1725388 * 2 ^ 59
def prefixEnd_1725388 : Nat := 4983230072969 + 3 ^ 40 * 1725388 * 2
def baseEnd_1725388 : Nat := 885953359499800645215091

theorem tailTrace_1725388 : CollatzResearch.WordTrace tailWord_1725388 prefixEnd_1725388 885953359499800645215091 := by
  unfold tailWord_1725388
  simp only [CollatzResearch.WordTrace]
  refine ⟨31465035136610711827704409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41953380182147615770272545 31465035136610711827704409)
  ·
    refine ⟨23598776352458033870778307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31465035136610711827704409 23598776352458033870778307)
    ·
      refine ⟨35398164528687050806167461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23598776352458033870778307 35398164528687050806167461)
      ·
        refine ⟨6637155849128822026156399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35398164528687050806167461 6637155849128822026156399)
        ·
          refine ⟨9955733773693233039234599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6637155849128822026156399 9955733773693233039234599)
          ·
            refine ⟨14933600660539849558851899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9955733773693233039234599 14933600660539849558851899)
            ·
              refine ⟨22400400990809774338277849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14933600660539849558851899 22400400990809774338277849)
              ·
                refine ⟨16800300743107330753708387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22400400990809774338277849 16800300743107330753708387)
                ·
                  refine ⟨25200451114660996130562581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16800300743107330753708387 25200451114660996130562581)
                  ·
                    refine ⟨1181271145999734193620121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25200451114660996130562581 1181271145999734193620121)
                    ·
                      refine ⟨885953359499800645215091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1181271145999734193620121 885953359499800645215091)
                      ·
                        rfl

theorem cell23_1725388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_1725388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725388 prefixEnd_1725388 := by exact prefixLift 1725388
  have htrace : WordTrace (prefixWord ++ tailWord_1725388) baseStart_1725388 baseEnd_1725388 := by
    simpa [prefixWord, tailWord_1725388, baseEnd_1725388] using wordTrace_append hprefix tailTrace_1725388
  have hstable : (prefixWord ++ tailWord_1725388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725388).length < 2 ^ (prefixWord ++ tailWord_1725388).sum := by decide
  have hdescent : baseEnd_1725388 < baseStart_1725388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725401 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 2, 1, 6]
def baseStart_1725401 : Nat := 118140960795 + 1725401 * 2 ^ 59
def prefixEnd_1725401 : Nat := 4983230072969 + 3 ^ 40 * 1725401 * 2
def baseEnd_1725401 : Nat := 885960034748309094352531

theorem tailTrace_1725401 : CollatzResearch.WordTrace tailWord_1725401 prefixEnd_1725401 885960034748309094352531 := by
  unfold tailWord_1725401
  simp only [CollatzResearch.WordTrace]
  refine ⟨62930544422174326875632057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41953696281449551250421371 62930544422174326875632057)
  ·
    refine ⟨47197908316630745156724043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62930544422174326875632057 47197908316630745156724043)
    ·
      refine ⟨70796862474946117735086065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47197908316630745156724043 70796862474946117735086065)
      ·
        refine ⟨53097646856209588301314549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70796862474946117735086065 53097646856209588301314549)
        ·
          refine ⟨4977904392769648903248239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53097646856209588301314549 4977904392769648903248239)
          ·
            refine ⟨7466856589154473354872359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4977904392769648903248239 7466856589154473354872359)
            ·
              refine ⟨11200284883731710032308539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7466856589154473354872359 11200284883731710032308539)
              ·
                refine ⟨16800427325597565048462809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11200284883731710032308539 16800427325597565048462809)
                ·
                  refine ⟨12600320494198173786347107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16800427325597565048462809 12600320494198173786347107)
                  ·
                    refine ⟨18900480741297260679520661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12600320494198173786347107 18900480741297260679520661)
                    ·
                      refine ⟨885960034748309094352531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18900480741297260679520661 885960034748309094352531)
                      ·
                        rfl

theorem cell23_1725401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_1725401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725401 prefixEnd_1725401 := by exact prefixLift 1725401
  have htrace : WordTrace (prefixWord ++ tailWord_1725401) baseStart_1725401 baseEnd_1725401 := by
    simpa [prefixWord, tailWord_1725401, baseEnd_1725401] using wordTrace_append hprefix tailTrace_1725401
  have hstable : (prefixWord ++ tailWord_1725401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725401).length < 2 ^ (prefixWord ++ tailWord_1725401).sum := by decide
  have hdescent : baseEnd_1725401 < baseStart_1725401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725405 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_1725405 : Nat := 118140960795 + 1725405 * 2 ^ 59
def prefixEnd_1725405 : Nat := 4983230072969 + 3 ^ 40 * 1725405 * 2
def baseEnd_1725405 : Nat := 885962088670927078702513

theorem tailTrace_1725405 : CollatzResearch.WordTrace tailWord_1725405 prefixEnd_1725405 885962088670927078702513 := by
  unfold tailWord_1725405
  simp only [CollatzResearch.WordTrace]
  refine ⟨62930690314159835558777669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41953793542773223705851779 62930690314159835558777669)
  ·
    refine ⟨11799504433904969167270813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62930690314159835558777669 11799504433904969167270813)
    ·
      refine ⟨4424814162714363437726555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11799504433904969167270813 4424814162714363437726555)
      ·
        refine ⟨6637221244071545156589833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4424814162714363437726555 6637221244071545156589833)
        ·
          refine ⟨4977915933053658867442375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6637221244071545156589833 4977915933053658867442375)
          ·
            refine ⟨7466873899580488301163563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4977915933053658867442375 7466873899580488301163563)
            ·
              refine ⟨11200310849370732451745345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7466873899580488301163563 11200310849370732451745345)
              ·
                refine ⟨8400233137028049338809009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11200310849370732451745345 8400233137028049338809009)
                ·
                  refine ⟨6300174852771037004106757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8400233137028049338809009 6300174852771037004106757)
                  ·
                    refine ⟨1181282784894569438270017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6300174852771037004106757 1181282784894569438270017)
                    ·
                      refine ⟨885962088670927078702513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1181282784894569438270017 885962088670927078702513)
                      ·
                        rfl

theorem cell23_1725405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_1725405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725405 prefixEnd_1725405 := by exact prefixLift 1725405
  have htrace : WordTrace (prefixWord ++ tailWord_1725405) baseStart_1725405 baseEnd_1725405 := by
    simpa [prefixWord, tailWord_1725405, baseEnd_1725405] using wordTrace_append hprefix tailTrace_1725405
  have hstable : (prefixWord ++ tailWord_1725405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725405).length < 2 ^ (prefixWord ++ tailWord_1725405).sum := by decide
  have hdescent : baseEnd_1725405 < baseStart_1725405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725411 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 8]
def baseStart_1725411 : Nat := 118140960795 + 1725411 * 2 ^ 59
def prefixEnd_1725411 : Nat := 4983230072969 + 3 ^ 40 * 1725411 * 2
def baseEnd_1725411 : Nat := 98440574394983783914165

theorem tailTrace_1725411 : CollatzResearch.WordTrace tailWord_1725411 prefixEnd_1725411 98440574394983783914165 := by
  unfold tailWord_1725411
  simp only [CollatzResearch.WordTrace]
  refine ⟨62930909152138098583496087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41953939434758732388997391 62930909152138098583496087)
  ·
    refine ⟨94396363728207147875244131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62930909152138098583496087 94396363728207147875244131)
    ·
      refine ⟨141594545592310721812866197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94396363728207147875244131 141594545592310721812866197)
      ·
        refine ⟨6637244324639565084978103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 141594545592310721812866197 6637244324639565084978103)
        ·
          refine ⟨9955866486959347627467155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6637244324639565084978103 9955866486959347627467155)
          ·
            refine ⟨14933799730439021441200733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9955866486959347627467155 14933799730439021441200733)
            ·
              refine ⟨5600174898914633040450275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14933799730439021441200733 5600174898914633040450275)
              ·
                refine ⟨8400262348371949560675413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5600174898914633040450275 8400262348371949560675413)
                ·
                  refine ⟨98440574394983783914165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8400262348371949560675413 98440574394983783914165)
                  ·
                    rfl

theorem cell23_1725411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 8].length) (baseStart_1725411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725411 prefixEnd_1725411 := by exact prefixLift 1725411
  have htrace : WordTrace (prefixWord ++ tailWord_1725411) baseStart_1725411 baseEnd_1725411 := by
    simpa [prefixWord, tailWord_1725411, baseEnd_1725411] using wordTrace_append hprefix tailTrace_1725411
  have hstable : (prefixWord ++ tailWord_1725411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725411).length < 2 ^ (prefixWord ++ tailWord_1725411).sum := by decide
  have hdescent : baseEnd_1725411 < baseStart_1725411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725415 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 3, 4]
def baseStart_1725415 : Nat := 118140960795 + 1725415 * 2 ^ 59
def prefixEnd_1725415 : Nat := 4983230072969 + 3 ^ 40 * 1725415 * 2
def baseEnd_1725415 : Nat := 295322407825824013192489

theorem tailTrace_1725415 : CollatzResearch.WordTrace tailWord_1725415 prefixEnd_1725415 295322407825824013192489 := by
  unfold tailWord_1725415
  simp only [CollatzResearch.WordTrace]
  refine ⟨62931055044123607266641699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41954036696082404844427799 62931055044123607266641699)
  ·
    refine ⟨94396582566185410899962549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62931055044123607266641699 94396582566185410899962549)
    ·
      refine ⟨8849679615579882271871489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94396582566185410899962549 8849679615579882271871489)
      ·
        refine ⟨6637259711684911703903617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8849679615579882271871489 6637259711684911703903617)
        ·
          refine ⟨4977944783763683777927713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6637259711684911703903617 4977944783763683777927713)
          ·
            refine ⟨3733458587822762833445785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4977944783763683777927713 3733458587822762833445785)
            ·
              refine ⟨2800093940867072125084339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3733458587822762833445785 2800093940867072125084339)
              ·
                refine ⟨4200140911300608187626509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2800093940867072125084339 4200140911300608187626509)
                ·
                  refine ⟨1575052841737728070359941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4200140911300608187626509 1575052841737728070359941)
                  ·
                    refine ⟨295322407825824013192489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1575052841737728070359941 295322407825824013192489)
                    ·
                      rfl

theorem cell23_1725415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_1725415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725415 prefixEnd_1725415 := by exact prefixLift 1725415
  have htrace : WordTrace (prefixWord ++ tailWord_1725415) baseStart_1725415 baseEnd_1725415 := by
    simpa [prefixWord, tailWord_1725415, baseEnd_1725415] using wordTrace_append hprefix tailTrace_1725415
  have hstable : (prefixWord ++ tailWord_1725415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725415).length < 2 ^ (prefixWord ++ tailWord_1725415).sum := by decide
  have hdescent : baseEnd_1725415 < baseStart_1725415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725492 : List Nat := [2, 5, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_1725492 : Nat := 118140960795 + 1725492 * 2 ^ 59
def prefixEnd_1725492 : Nat := 4983230072969 + 3 ^ 40 * 1725492 * 2
def baseEnd_1725492 : Nat := 295335587162622746104871

theorem tailTrace_1725492 : CollatzResearch.WordTrace tailWord_1725492 prefixEnd_1725492 295335587162622746104871 := by
  unfold tailWord_1725492
  simp only [CollatzResearch.WordTrace]
  refine ⟨31466931732422324708597365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41955908976563099611463153 31466931732422324708597365)
  ·
    refine ⟨2950024849914592941431003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31466931732422324708597365 2950024849914592941431003)
    ·
      refine ⟨4425037274871889412146505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2950024849914592941431003 4425037274871889412146505)
      ·
        refine ⟨3318777956153917059109879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4425037274871889412146505 3318777956153917059109879)
        ·
          refine ⟨4978166934230875588664819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3318777956153917059109879 4978166934230875588664819)
          ·
            refine ⟨7467250401346313382997229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4978166934230875588664819 7467250401346313382997229)
            ·
              refine ⟨2800218900504867518623961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7467250401346313382997229 2800218900504867518623961)
              ·
                refine ⟨2100164175378650638967971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2800218900504867518623961 2100164175378650638967971)
                ·
                  refine ⟨3150246263067975958451957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2100164175378650638967971 3150246263067975958451957)
                  ·
                    refine ⟨295335587162622746104871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3150246263067975958451957 295335587162622746104871)
                    ·
                      rfl

theorem cell23_1725492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_1725492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725492 prefixEnd_1725492 := by exact prefixLift 1725492
  have htrace : WordTrace (prefixWord ++ tailWord_1725492) baseStart_1725492 baseEnd_1725492 := by
    simpa [prefixWord, tailWord_1725492, baseEnd_1725492] using wordTrace_append hprefix tailTrace_1725492
  have hstable : (prefixWord ++ tailWord_1725492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725492).length < 2 ^ (prefixWord ++ tailWord_1725492).sum := by decide
  have hdescent : baseEnd_1725492 < baseStart_1725492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725495 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 5, 2, 2]
def baseStart_1725495 : Nat := 118140960795 + 1725495 * 2 ^ 59
def prefixEnd_1725495 : Nat := 4983230072969 + 3 ^ 40 * 1725495 * 2
def baseEnd_1725495 : Nat := 886008301929831726577099

theorem tailTrace_1725495 : CollatzResearch.WordTrace tailWord_1725495 prefixEnd_1725495 886008301929831726577099 := by
  unfold tailWord_1725495
  simp only [CollatzResearch.WordTrace]
  refine ⟨62933972883833780929553939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41955981922555853953035959 62933972883833780929553939)
  ·
    refine ⟨94400959325750671394330909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62933972883833780929553939 94400959325750671394330909)
    ·
      refine ⟨35400359747156501772874091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94400959325750671394330909 35400359747156501772874091)
      ·
        refine ⟨53100539620734752659311137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35400359747156501772874091 53100539620734752659311137)
        ·
          refine ⟨39825404715551064494483353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53100539620734752659311137 39825404715551064494483353)
          ·
            refine ⟨29869053536663298370862515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39825404715551064494483353 29869053536663298370862515)
            ·
              refine ⟨44803580304994947556293773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29869053536663298370862515 44803580304994947556293773)
              ·
                refine ⟨16801342614373105333610165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44803580304994947556293773 16801342614373105333610165)
                ·
                  refine ⟨1575125870097478625025953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16801342614373105333610165 1575125870097478625025953)
                  ·
                    refine ⟨1181344402573108968769465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1575125870097478625025953 1181344402573108968769465)
                    ·
                      refine ⟨886008301929831726577099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1181344402573108968769465 886008301929831726577099)
                      ·
                        rfl

theorem cell23_1725495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 2, 2].length) (baseStart_1725495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725495 prefixEnd_1725495 := by exact prefixLift 1725495
  have htrace : WordTrace (prefixWord ++ tailWord_1725495) baseStart_1725495 baseEnd_1725495 := by
    simpa [prefixWord, tailWord_1725495, baseEnd_1725495] using wordTrace_append hprefix tailTrace_1725495
  have hstable : (prefixWord ++ tailWord_1725495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725495).length < 2 ^ (prefixWord ++ tailWord_1725495).sum := by decide
  have hdescent : baseEnd_1725495 < baseStart_1725495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725505 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 1, 6]
def baseStart_1725505 : Nat := 118140960795 + 1725505 * 2 ^ 59
def prefixEnd_1725505 : Nat := 4983230072969 + 3 ^ 40 * 1725505 * 2
def baseEnd_1725505 : Nat := 295337812245458895817351

theorem tailTrace_1725505 : CollatzResearch.WordTrace tailWord_1725505 prefixEnd_1725505 295337812245458895817351 := by
  unfold tailWord_1725505
  simp only [CollatzResearch.WordTrace]
  refine ⟨62934337613797552637417969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41956225075865035091611979 62934337613797552637417969)
  ·
    refine ⟨47200753210348164478063477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62934337613797552637417969 47200753210348164478063477)
    ·
      refine ⟨4425070613470140419818451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47200753210348164478063477 4425070613470140419818451)
      ·
        refine ⟨6637605920205210629727677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4425070613470140419818451 6637605920205210629727677)
        ·
          refine ⟨2489102220076953986147879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6637605920205210629727677 2489102220076953986147879)
          ·
            refine ⟨3733653330115430979221819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2489102220076953986147879 3733653330115430979221819)
            ·
              refine ⟨5600479995173146468832729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3733653330115430979221819 5600479995173146468832729)
              ·
                refine ⟨4200359996379859851624547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5600479995173146468832729 4200359996379859851624547)
                ·
                  refine ⟨6300539994569789777436821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4200359996379859851624547 6300539994569789777436821)
                  ·
                    refine ⟨295337812245458895817351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6300539994569789777436821 295337812245458895817351)
                    ·
                      rfl

theorem cell23_1725505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_1725505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725505 prefixEnd_1725505 := by exact prefixLift 1725505
  have htrace : WordTrace (prefixWord ++ tailWord_1725505) baseStart_1725505 baseEnd_1725505 := by
    simpa [prefixWord, tailWord_1725505, baseEnd_1725505] using wordTrace_append hprefix tailTrace_1725505
  have hstable : (prefixWord ++ tailWord_1725505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725505).length < 2 ^ (prefixWord ++ tailWord_1725505).sum := by decide
  have hdescent : baseEnd_1725505 < baseStart_1725505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725522 : List Nat := [3, 2, 2, 1, 3, 2, 2, 2, 2, 4]
def baseStart_1725522 : Nat := 118140960795 + 1725522 * 2 ^ 59
def prefixEnd_1725522 : Nat := 4983230072969 + 3 ^ 40 * 1725522 * 2
def baseEnd_1725522 : Nat := 295340721969167706979825

theorem tailTrace_1725522 : CollatzResearch.WordTrace tailWord_1725522 prefixEnd_1725522 295340721969167706979825 := by
  unfold tailWord_1725522
  simp only [CollatzResearch.WordTrace]
  refine ⟨15733739413683991135196705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41956638436490643027191213 15733739413683991135196705)
  ·
    refine ⟨11800304560262993351397529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15733739413683991135196705 11800304560262993351397529)
    ·
      refine ⟨8850228420197245013548147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11800304560262993351397529 8850228420197245013548147)
      ·
        refine ⟨13275342630295867520322221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8850228420197245013548147 13275342630295867520322221)
        ·
          refine ⟨4978253486360950320120833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13275342630295867520322221 4978253486360950320120833)
          ·
            refine ⟨3733690114770712740090625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4978253486360950320120833 3733690114770712740090625)
            ·
              refine ⟨2800267586078034555067969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3733690114770712740090625 2800267586078034555067969)
              ·
                refine ⟨2100200689558525916300977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2800267586078034555067969 2100200689558525916300977)
                ·
                  refine ⟨1575150517168894437225733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2100200689558525916300977 1575150517168894437225733)
                  ·
                    refine ⟨295340721969167706979825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1575150517168894437225733 295340721969167706979825)
                    ·
                      rfl

theorem cell23_1725522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_1725522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725522 prefixEnd_1725522 := by exact prefixLift 1725522
  have htrace : WordTrace (prefixWord ++ tailWord_1725522) baseStart_1725522 baseEnd_1725522 := by
    simpa [prefixWord, tailWord_1725522, baseEnd_1725522] using wordTrace_append hprefix tailTrace_1725522
  have hstable : (prefixWord ++ tailWord_1725522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725522).length < 2 ^ (prefixWord ++ tailWord_1725522).sum := by decide
  have hdescent : baseEnd_1725522 < baseStart_1725522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725528 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 3, 3, 3]
def baseStart_1725528 : Nat := 118140960795 + 1725528 * 2 ^ 59
def prefixEnd_1725528 : Nat := 4983230072969 + 3 ^ 40 * 1725528 * 2
def baseEnd_1725528 : Nat := 886025246791430097464447

theorem tailTrace_1725528 : CollatzResearch.WordTrace tailWord_1725528 prefixEnd_1725528 886025246791430097464447 := by
  unfold tailWord_1725528
  simp only [CollatzResearch.WordTrace]
  refine ⟨31467588246357113782752619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41956784328476151710336825 31467588246357113782752619)
  ·
    refine ⟨47201382369535670674128929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31467588246357113782752619 47201382369535670674128929)
    ·
      refine ⟨35401036777151753005596697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47201382369535670674128929 35401036777151753005596697)
      ·
        refine ⟨26550777582863814754197523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35401036777151753005596697 26550777582863814754197523)
        ·
          refine ⟨39826166374295722131296285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26550777582863814754197523 39826166374295722131296285)
          ·
            refine ⟨14934812390360895799236107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39826166374295722131296285 14934812390360895799236107)
            ·
              refine ⟨22402218585541343698854161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14934812390360895799236107 22402218585541343698854161)
              ·
                refine ⟨16801663939156007774140621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22402218585541343698854161 16801663939156007774140621)
                ·
                  refine ⟨6300623977183502915302733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16801663939156007774140621 6300623977183502915302733)
                  ·
                    refine ⟨2362733991443813593238525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6300623977183502915302733 2362733991443813593238525)
                    ·
                      refine ⟨886025246791430097464447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2362733991443813593238525 886025246791430097464447)
                      ·
                        rfl

theorem cell23_1725528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_1725528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725528 prefixEnd_1725528 := by exact prefixLift 1725528
  have htrace : WordTrace (prefixWord ++ tailWord_1725528) baseStart_1725528 baseEnd_1725528 := by
    simpa [prefixWord, tailWord_1725528, baseEnd_1725528] using wordTrace_append hprefix tailTrace_1725528
  have hstable : (prefixWord ++ tailWord_1725528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725528).length < 2 ^ (prefixWord ++ tailWord_1725528).sum := by decide
  have hdescent : baseEnd_1725528 < baseStart_1725528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725545 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 1, 3, 3]
def baseStart_1725545 : Nat := 118140960795 + 1725545 * 2 ^ 59
def prefixEnd_1725545 : Nat := 4983230072969 + 3 ^ 40 * 1725545 * 2
def baseEnd_1725545 : Nat := 886033975962556530951869

theorem tailTrace_1725545 : CollatzResearch.WordTrace tailWord_1725545 prefixEnd_1725545 886033975962556530951869 := by
  unfold tailWord_1725545
  simp only [CollatzResearch.WordTrace]
  refine ⟨62935796533652639468874089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41957197689101759645916059 62935796533652639468874089)
  ·
    refine ⟨47201847400239479601655567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62935796533652639468874089 47201847400239479601655567)
    ·
      refine ⟨70802771100359219402483351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47201847400239479601655567 70802771100359219402483351)
      ·
        refine ⟨106204156650538829103725027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70802771100359219402483351 106204156650538829103725027)
        ·
          refine ⟨159306234975808243655587541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106204156650538829103725027 159306234975808243655587541)
          ·
            refine ⟨3733739882245505710677833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 159306234975808243655587541 3733739882245505710677833)
            ·
              refine ⟨2800304911684129283008375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3733739882245505710677833 2800304911684129283008375)
              ·
                refine ⟨4200457367526193924512563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2800304911684129283008375 4200457367526193924512563)
                ·
                  refine ⟨6300686051289290886768845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4200457367526193924512563 6300686051289290886768845)
                  ·
                    refine ⟨2362757269233484082538317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6300686051289290886768845 2362757269233484082538317)
                    ·
                      refine ⟨886033975962556530951869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2362757269233484082538317 886033975962556530951869)
                      ·
                        rfl

theorem cell23_1725545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 3, 3].length) (baseStart_1725545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725545 prefixEnd_1725545 := by exact prefixLift 1725545
  have htrace : WordTrace (prefixWord ++ tailWord_1725545) baseStart_1725545 baseEnd_1725545 := by
    simpa [prefixWord, tailWord_1725545, baseEnd_1725545] using wordTrace_append hprefix tailTrace_1725545
  have hstable : (prefixWord ++ tailWord_1725545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725545).length < 2 ^ (prefixWord ++ tailWord_1725545).sum := by decide
  have hdescent : baseEnd_1725545 < baseStart_1725545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725578 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 4, 6]
def baseStart_1725578 : Nat := 118140960795 + 1725578 * 2 ^ 59
def prefixEnd_1725578 : Nat := 4983230072969 + 3 ^ 40 * 1725578 * 2
def baseEnd_1725578 : Nat := 295350306941384967279739

theorem tailTrace_1725578 : CollatzResearch.WordTrace tailWord_1725578 prefixEnd_1725578 295350306941384967279739 := by
  unfold tailWord_1725578
  simp only [CollatzResearch.WordTrace]
  refine ⟨15734250035633271526206347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41958000095022057403216925 15734250035633271526206347)
  ·
    refine ⟨23601375053449907289309521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15734250035633271526206347 23601375053449907289309521)
    ·
      refine ⟨17701031290087430466982141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23601375053449907289309521 17701031290087430466982141)
      ·
        refine ⟨6637886733782786425118303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17701031290087430466982141 6637886733782786425118303)
        ·
          refine ⟨9956830100674179637677455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6637886733782786425118303 9956830100674179637677455)
          ·
            refine ⟨14935245151011269456516183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9956830100674179637677455 14935245151011269456516183)
            ·
              refine ⟨22402867726516904184774275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14935245151011269456516183 22402867726516904184774275)
              ·
                refine ⟨33604301589775356277161413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22402867726516904184774275 33604301589775356277161413)
                ·
                  refine ⟨6300806548082879301967765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33604301589775356277161413 6300806548082879301967765)
                  ·
                    refine ⟨295350306941384967279739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6300806548082879301967765 295350306941384967279739)
                    ·
                      rfl

theorem cell23_1725578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_1725578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725578 prefixEnd_1725578 := by exact prefixLift 1725578
  have htrace : WordTrace (prefixWord ++ tailWord_1725578) baseStart_1725578 baseEnd_1725578 := by
    simpa [prefixWord, tailWord_1725578, baseEnd_1725578] using wordTrace_append hprefix tailTrace_1725578
  have hstable : (prefixWord ++ tailWord_1725578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725578).length < 2 ^ (prefixWord ++ tailWord_1725578).sum := by decide
  have hdescent : baseEnd_1725578 < baseStart_1725578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725653 : List Nat := [1, 3, 2, 4, 1, 3, 2, 1, 2, 2, 2]
def baseStart_1725653 : Nat := 118140960795 + 1725653 * 2 ^ 59
def prefixEnd_1725653 : Nat := 4983230072969 + 3 ^ 40 * 1725653 * 2
def baseEnd_1725653 : Nat := 886089431873242108401373

theorem tailTrace_1725653 : CollatzResearch.WordTrace tailWord_1725653 prefixEnd_1725653 886089431873242108401373 := by
  unfold tailWord_1725653
  simp only [CollatzResearch.WordTrace]
  refine ⟨62939735617261373913805613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41959823744840915942537075 62939735617261373913805613)
  ·
    refine ⟨23602400856473015217677105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62939735617261373913805613 23602400856473015217677105)
    ·
      refine ⟨17701800642354761413257829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23602400856473015217677105 17701800642354761413257829)
      ·
        refine ⟨3319087620441517764985843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17701800642354761413257829 3319087620441517764985843)
        ·
          refine ⟨4978631430662276647478765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3319087620441517764985843 4978631430662276647478765)
          ·
            refine ⟨1866986786498353742804537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4978631430662276647478765 1866986786498353742804537)
            ·
              refine ⟨1400240089873765307103403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1866986786498353742804537 1400240089873765307103403)
              ·
                refine ⟨2100360134810647960655105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1400240089873765307103403 2100360134810647960655105)
                ·
                  refine ⟨1575270101107985970491329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2100360134810647960655105 1575270101107985970491329)
                  ·
                    refine ⟨1181452575830989477868497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1575270101107985970491329 1181452575830989477868497)
                    ·
                      refine ⟨886089431873242108401373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1181452575830989477868497 886089431873242108401373)
                      ·
                        rfl

theorem cell23_1725653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_1725653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725653 prefixEnd_1725653 := by exact prefixLift 1725653
  have htrace : WordTrace (prefixWord ++ tailWord_1725653) baseStart_1725653 baseEnd_1725653 := by
    simpa [prefixWord, tailWord_1725653, baseEnd_1725653] using wordTrace_append hprefix tailTrace_1725653
  have hstable : (prefixWord ++ tailWord_1725653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725653).length < 2 ^ (prefixWord ++ tailWord_1725653).sum := by decide
  have hdescent : baseEnd_1725653 < baseStart_1725653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725668 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 2, 8]
def baseStart_1725668 : Nat := 118140960795 + 1725668 * 2 ^ 59
def prefixEnd_1725668 : Nat := 4983230072969 + 3 ^ 40 * 1725668 * 2
def baseEnd_1725668 : Nat := 295365711361019849904601

theorem tailTrace_1725668 : CollatzResearch.WordTrace tailWord_1725668 prefixEnd_1725668 295365711361019849904601 := by
  unfold tailWord_1725668
  simp only [CollatzResearch.WordTrace]
  refine ⟨31470141356103515737800829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41960188474804687650401105 31470141356103515737800829)
  ·
    refine ⟨11801303008538818401675311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31470141356103515737800829 11801303008538818401675311)
    ·
      refine ⟨17701954512808227602512967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11801303008538818401675311 17701954512808227602512967)
      ·
        refine ⟨26552931769212341403769451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17701954512808227602512967 26552931769212341403769451)
        ·
          refine ⟨39829397653818512105654177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26552931769212341403769451 39829397653818512105654177)
          ·
            refine ⟨29872048240363884079240633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39829397653818512105654177 29872048240363884079240633)
            ·
              refine ⟨22404036180272913059430475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29872048240363884079240633 22404036180272913059430475)
              ·
                refine ⟨33606054270409369589145713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22404036180272913059430475 33606054270409369589145713)
                ·
                  refine ⟨25204540702807027191859285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33606054270409369589145713 25204540702807027191859285)
                  ·
                    refine ⟨295365711361019849904601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25204540702807027191859285 295365711361019849904601)
                    ·
                      rfl

theorem cell23_1725668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_1725668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725668 prefixEnd_1725668 := by exact prefixLift 1725668
  have htrace : WordTrace (prefixWord ++ tailWord_1725668) baseStart_1725668 baseEnd_1725668 := by
    simpa [prefixWord, tailWord_1725668, baseEnd_1725668] using wordTrace_append hprefix tailTrace_1725668
  have hstable : (prefixWord ++ tailWord_1725668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725668).length < 2 ^ (prefixWord ++ tailWord_1725668).sum := by decide
  have hdescent : baseEnd_1725668 < baseStart_1725668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725675 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 4]
def baseStart_1725675 : Nat := 118140960795 + 1725675 * 2 ^ 59
def prefixEnd_1725675 : Nat := 4983230072969 + 3 ^ 40 * 1725675 * 2
def baseEnd_1725675 : Nat := 886100728447641022326271

theorem tailTrace_1725675 : CollatzResearch.WordTrace tailWord_1725675 prefixEnd_1725675 886100728447641022326271 := by
  unfold tailWord_1725675
  simp only [CollatzResearch.WordTrace]
  refine ⟨62940538023181671671106479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41960358682121114447404319 62940538023181671671106479)
  ·
    refine ⟨94410807034772507506659719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62940538023181671671106479 94410807034772507506659719)
    ·
      refine ⟨141616210552158761259989579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94410807034772507506659719 141616210552158761259989579)
      ·
        refine ⟨212424315828238141889984369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141616210552158761259989579 212424315828238141889984369)
        ·
          refine ⟨159318236871178606417488277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212424315828238141889984369 159318236871178606417488277)
          ·
            refine ⟨7468042353336497175819763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 159318236871178606417488277 7468042353336497175819763)
            ·
              refine ⟨11202063530004745763729645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7468042353336497175819763 11202063530004745763729645)
              ·
                refine ⟨4200773823751779661398617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11202063530004745763729645 4200773823751779661398617)
                ·
                  refine ⟨3150580367813834746048963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4200773823751779661398617 3150580367813834746048963)
                  ·
                    refine ⟨4725870551720752119073445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3150580367813834746048963 4725870551720752119073445)
                    ·
                      refine ⟨886100728447641022326271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4725870551720752119073445 886100728447641022326271)
                      ·
                        rfl

theorem cell23_1725675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 4].length) (baseStart_1725675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725675 prefixEnd_1725675 := by exact prefixLift 1725675
  have htrace : WordTrace (prefixWord ++ tailWord_1725675) baseStart_1725675 baseEnd_1725675 := by
    simpa [prefixWord, tailWord_1725675, baseEnd_1725675] using wordTrace_append hprefix tailTrace_1725675
  have hstable : (prefixWord ++ tailWord_1725675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725675).length < 2 ^ (prefixWord ++ tailWord_1725675).sum := by decide
  have hdescent : baseEnd_1725675 < baseStart_1725675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725736 : List Nat := [2, 1, 5, 1, 2, 2, 2, 3, 1, 4]
def baseStart_1725736 : Nat := 118140960795 + 1725736 * 2 ^ 59
def prefixEnd_1725736 : Nat := 4983230072969 + 3 ^ 40 * 1725736 * 2
def baseEnd_1725736 : Nat := 295377350255855094554497

theorem tailTrace_1725736 : CollatzResearch.WordTrace tailWord_1725736 prefixEnd_1725736 295377350255855094554497 := by
  unfold tailWord_1725736
  simp only [CollatzResearch.WordTrace]
  refine ⟨31471381437980339544538531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41961841917307119392718041 31471381437980339544538531)
  ·
    refine ⟨47207072156970509316807797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31471381437980339544538531 47207072156970509316807797)
    ·
      refine ⟨4425663014715985248450731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47207072156970509316807797 4425663014715985248450731)
      ·
        refine ⟨6638494522073977872676097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4425663014715985248450731 6638494522073977872676097)
        ·
          refine ⟨4978870891555483404507073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6638494522073977872676097 4978870891555483404507073)
          ·
            refine ⟨3734153168666612553380305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4978870891555483404507073 3734153168666612553380305)
            ·
              refine ⟨2800614876499959415035229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3734153168666612553380305 2800614876499959415035229)
              ·
                refine ⟨1050230578687484780638211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2800614876499959415035229 1050230578687484780638211)
                ·
                  refine ⟨1575345868031227170957317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050230578687484780638211 1575345868031227170957317)
                  ·
                    refine ⟨295377350255855094554497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1575345868031227170957317 295377350255855094554497)
                    ·
                      rfl

theorem cell23_1725736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_1725736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725736 prefixEnd_1725736 := by exact prefixLift 1725736
  have htrace : WordTrace (prefixWord ++ tailWord_1725736) baseStart_1725736 baseEnd_1725736 := by
    simpa [prefixWord, tailWord_1725736, baseEnd_1725736] using wordTrace_append hprefix tailTrace_1725736
  have hstable : (prefixWord ++ tailWord_1725736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725736).length < 2 ^ (prefixWord ++ tailWord_1725736).sum := by decide
  have hdescent : baseEnd_1725736 < baseStart_1725736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725752 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 4, 3, 2]
def baseStart_1725752 : Nat := 118140960795 + 1725752 * 2 ^ 59
def prefixEnd_1725752 : Nat := 4983230072969 + 3 ^ 40 * 1725752 * 2
def baseEnd_1725752 : Nat := 886140266458037221063417

theorem tailTrace_1725752 : CollatzResearch.WordTrace tailWord_1725752 prefixEnd_1725752 886140266458037221063417 := by
  unfold tailWord_1725752
  simp only [CollatzResearch.WordTrace]
  refine ⟨31471673221951356910829755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41962230962601809214439673 31471673221951356910829755)
  ·
    refine ⟨47207509832927035366244633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31471673221951356910829755 47207509832927035366244633)
    ·
      refine ⟨35405632374695276524683475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47207509832927035366244633 35405632374695276524683475)
      ·
        refine ⟨53108448562042914787025213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35405632374695276524683475 53108448562042914787025213)
        ·
          refine ⟨19915668210766093045134455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53108448562042914787025213 19915668210766093045134455)
          ·
            refine ⟨29873502316149139567701683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19915668210766093045134455 29873502316149139567701683)
            ·
              refine ⟨44810253474223709351552525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29873502316149139567701683 44810253474223709351552525)
              ·
                refine ⟨16803845052833891006832197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44810253474223709351552525 16803845052833891006832197)
                ·
                  refine ⟨3150720947406354563781037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16803845052833891006832197 3150720947406354563781037)
                  ·
                    refine ⟨1181520355277382961417889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3150720947406354563781037 1181520355277382961417889)
                    ·
                      refine ⟨886140266458037221063417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1181520355277382961417889 886140266458037221063417)
                      ·
                        rfl

theorem cell23_1725752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 4, 3, 2].length) (baseStart_1725752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725752 prefixEnd_1725752 := by exact prefixLift 1725752
  have htrace : WordTrace (prefixWord ++ tailWord_1725752) baseStart_1725752 baseEnd_1725752 := by
    simpa [prefixWord, tailWord_1725752, baseEnd_1725752] using wordTrace_append hprefix tailTrace_1725752
  have hstable : (prefixWord ++ tailWord_1725752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725752).length < 2 ^ (prefixWord ++ tailWord_1725752).sum := by decide
  have hdescent : baseEnd_1725752 < baseStart_1725752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725759 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 3, 1, 3]
def baseStart_1725759 : Nat := 118140960795 + 1725759 * 2 ^ 59
def prefixEnd_1725759 : Nat := 4983230072969 + 3 ^ 40 * 1725759 * 2
def baseEnd_1725759 : Nat := 886143860822618693675885

theorem tailTrace_1725759 : CollatzResearch.WordTrace tailWord_1725759 prefixEnd_1725759 886143860822618693675885 := by
  unfold tailWord_1725759
  simp only [CollatzResearch.WordTrace]
  refine ⟨62943601754877354017164331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41962401169918236011442887 62943601754877354017164331)
  ·
    refine ⟨94415402632316031025746497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62943601754877354017164331 94415402632316031025746497)
    ·
      refine ⟨70811551974237023269309873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94415402632316031025746497 70811551974237023269309873)
      ·
        refine ⟨53108663980677767451982405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70811551974237023269309873 53108663980677767451982405)
        ·
          refine ⟨9957874496377081397246701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53108663980677767451982405 9957874496377081397246701)
          ·
            refine ⟨3734202936141405523967513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9957874496377081397246701 3734202936141405523967513)
            ·
              refine ⟨2800652202106054142975635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3734202936141405523967513 2800652202106054142975635)
              ·
                refine ⟨4200978303159081214463453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2800652202106054142975635 4200978303159081214463453)
                ·
                  refine ⟨1575366863684655455423795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4200978303159081214463453 1575366863684655455423795)
                  ·
                    refine ⟨2363050295526983183135693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1575366863684655455423795 2363050295526983183135693)
                    ·
                      refine ⟨886143860822618693675885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2363050295526983183135693 886143860822618693675885)
                      ·
                        rfl

theorem cell23_1725759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 1, 3].length) (baseStart_1725759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725759 prefixEnd_1725759 := by exact prefixLift 1725759
  have htrace : WordTrace (prefixWord ++ tailWord_1725759) baseStart_1725759 baseEnd_1725759 := by
    simpa [prefixWord, tailWord_1725759, baseEnd_1725759] using wordTrace_append hprefix tailTrace_1725759
  have hstable : (prefixWord ++ tailWord_1725759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725759).length < 2 ^ (prefixWord ++ tailWord_1725759).sum := by decide
  have hdescent : baseEnd_1725759 < baseStart_1725759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725765 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 5, 1, 4]
def baseStart_1725765 : Nat := 118140960795 + 1725765 * 2 ^ 59
def prefixEnd_1725765 : Nat := 4983230072969 + 3 ^ 40 * 1725765 * 2
def baseEnd_1725765 : Nat := 886146941706545670200857

theorem tailTrace_1725765 : CollatzResearch.WordTrace tailWord_1725765 prefixEnd_1725765 886146941706545670200857 := by
  unfold tailWord_1725765
  simp only [CollatzResearch.WordTrace]
  refine ⟨62943820592855617041882749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41962547061903744694588499 62943820592855617041882749)
  ·
    refine ⟨23603932722320856390706031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62943820592855617041882749 23603932722320856390706031)
    ·
      refine ⟨35405899083481284586059047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23603932722320856390706031 35405899083481284586059047)
      ·
        refine ⟨53108848625221926879088571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35405899083481284586059047 53108848625221926879088571)
        ·
          refine ⟨79663272937832890318632857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53108848625221926879088571 79663272937832890318632857)
          ·
            refine ⟨59747454703374667738974643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79663272937832890318632857 59747454703374667738974643)
            ·
              refine ⟨89621182055062001608461965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59747454703374667738974643 89621182055062001608461965)
              ·
                refine ⟨33607943270648250603173237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89621182055062001608461965 33607943270648250603173237)
                ·
                  refine ⟨3150744681623273494047491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33607943270648250603173237 3150744681623273494047491)
                  ·
                    refine ⟨4726117022434910241071237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3150744681623273494047491 4726117022434910241071237)
                    ·
                      refine ⟨886146941706545670200857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4726117022434910241071237 886146941706545670200857)
                      ·
                        rfl

theorem cell23_1725765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_1725765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725765 prefixEnd_1725765 := by exact prefixLift 1725765
  have htrace : WordTrace (prefixWord ++ tailWord_1725765) baseStart_1725765 baseEnd_1725765 := by
    simpa [prefixWord, tailWord_1725765, baseEnd_1725765] using wordTrace_append hprefix tailTrace_1725765
  have hstable : (prefixWord ++ tailWord_1725765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725765).length < 2 ^ (prefixWord ++ tailWord_1725765).sum := by decide
  have hdescent : baseEnd_1725765 < baseStart_1725765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725792 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 4, 4]
def baseStart_1725792 : Nat := 118140960795 + 1725792 * 2 ^ 59
def prefixEnd_1725792 : Nat := 4983230072969 + 3 ^ 40 * 1725792 * 2
def baseEnd_1725792 : Nat := 295386935228072354854411

theorem tailTrace_1725792 : CollatzResearch.WordTrace tailWord_1725792 prefixEnd_1725792 295386935228072354854411 := by
  unfold tailWord_1725792
  simp only [CollatzResearch.WordTrace]
  refine ⟨31472402681878900326557815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41963203575838533768743753 31472402681878900326557815)
  ·
    refine ⟨47208604022818350489836723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31472402681878900326557815 47208604022818350489836723)
    ·
      refine ⟨70812906034227525734755085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47208604022818350489836723 70812906034227525734755085)
      ·
        refine ⟨26554839762835322150533157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70812906034227525734755085 26554839762835322150533157)
        ·
          refine ⟨4979032455531622903224967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26554839762835322150533157 4979032455531622903224967)
          ·
            refine ⟨7468548683297434354837451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4979032455531622903224967 7468548683297434354837451)
            ·
              refine ⟨11202823024946151532256177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7468548683297434354837451 11202823024946151532256177)
              ·
                refine ⟨8402117268709613649192133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11202823024946151532256177 8402117268709613649192133)
                ·
                  refine ⟨1575396987883052559223525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8402117268709613649192133 1575396987883052559223525)
                  ·
                    refine ⟨295386935228072354854411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1575396987883052559223525 295386935228072354854411)
                    ·
                      rfl

theorem cell23_1725792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 4, 4].length) (baseStart_1725792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725792 prefixEnd_1725792 := by exact prefixLift 1725792
  have htrace : WordTrace (prefixWord ++ tailWord_1725792) baseStart_1725792 baseEnd_1725792 := by
    simpa [prefixWord, tailWord_1725792, baseEnd_1725792] using wordTrace_append hprefix tailTrace_1725792
  have hstable : (prefixWord ++ tailWord_1725792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725792).length < 2 ^ (prefixWord ++ tailWord_1725792).sum := by decide
  have hdescent : baseEnd_1725792 < baseStart_1725792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725805 : List Nat := [1, 5, 1, 1, 1, 3, 11]
def baseStart_1725805 : Nat := 118140960795 + 1725805 * 2 ^ 59
def prefixEnd_1725805 : Nat := 4983230072969 + 3 ^ 40 * 1725805 * 2
def baseEnd_1725805 : Nat := 10940339270774389058033

theorem tailTrace_1725805 : CollatzResearch.WordTrace tailWord_1725805 prefixEnd_1725805 10940339270774389058033 := by
  unfold tailWord_1725805
  simp only [CollatzResearch.WordTrace]
  refine ⟨62945279512710703873338869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41963519675140469248892579 62945279512710703873338869)
  ·
    refine ⟨5901119954316628488125519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62945279512710703873338869 5901119954316628488125519)
    ·
      refine ⟨8851679931474942732188279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5901119954316628488125519 8851679931474942732188279)
      ·
        refine ⟨13277519897212414098282419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8851679931474942732188279 13277519897212414098282419)
        ·
          refine ⟨19916279845818621147423629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13277519897212414098282419 19916279845818621147423629)
          ·
            refine ⟨7468604942181982930283861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19916279845818621147423629 7468604942181982930283861)
            ·
              refine ⟨10940339270774389058033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7468604942181982930283861 10940339270774389058033)
              ·
                rfl

theorem cell23_1725805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 11].length) (baseStart_1725805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725805 prefixEnd_1725805 := by exact prefixLift 1725805
  have htrace : WordTrace (prefixWord ++ tailWord_1725805) baseStart_1725805 baseEnd_1725805 := by
    simpa [prefixWord, tailWord_1725805, baseEnd_1725805] using wordTrace_append hprefix tailTrace_1725805
  have hstable : (prefixWord ++ tailWord_1725805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725805).length < 2 ^ (prefixWord ++ tailWord_1725805).sum := by decide
  have hdescent : baseEnd_1725805 < baseStart_1725805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725845 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_1725845 : Nat := 118140960795 + 1725845 * 2 ^ 59
def prefixEnd_1725845 : Nat := 4983230072969 + 3 ^ 40 * 1725845 * 2
def baseEnd_1725845 : Nat := 886188020158905357200489

theorem tailTrace_1725845 : CollatzResearch.WordTrace tailWord_1725845 prefixEnd_1725845 886188020158905357200489 := by
  unfold tailWord_1725845
  simp only [CollatzResearch.WordTrace]
  refine ⟨62946738432565790704794989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41964492288377193803196659 62946738432565790704794989)
  ·
    refine ⟨23605026912212171514298121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62946738432565790704794989 23605026912212171514298121)
    ·
      refine ⟨17703770184159128635723591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23605026912212171514298121 17703770184159128635723591)
      ·
        refine ⟨26555655276238692953585387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17703770184159128635723591 26555655276238692953585387)
        ·
          refine ⟨39833482914358039430378081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26555655276238692953585387 39833482914358039430378081)
          ·
            refine ⟨29875112185768529572783561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39833482914358039430378081 29875112185768529572783561)
            ·
              refine ⟨22406334139326397179587671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29875112185768529572783561 22406334139326397179587671)
              ·
                refine ⟨33609501208989595769381507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22406334139326397179587671 33609501208989595769381507)
                ·
                  refine ⟨50414251813484393654072261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33609501208989595769381507 50414251813484393654072261)
                  ·
                    refine ⟨9452672215028323810138549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50414251813484393654072261 9452672215028323810138549)
                    ·
                      refine ⟨886188020158905357200489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9452672215028323810138549 886188020158905357200489)
                      ·
                        rfl

theorem cell23_1725845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_1725845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725845 prefixEnd_1725845 := by exact prefixLift 1725845
  have htrace : WordTrace (prefixWord ++ tailWord_1725845) baseStart_1725845 baseEnd_1725845 := by
    simpa [prefixWord, tailWord_1725845, baseEnd_1725845] using wordTrace_append hprefix tailTrace_1725845
  have hstable : (prefixWord ++ tailWord_1725845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725845).length < 2 ^ (prefixWord ++ tailWord_1725845).sum := by decide
  have hdescent : baseEnd_1725845 < baseStart_1725845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725875 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 5]
def baseStart_1725875 : Nat := 118140960795 + 1725875 * 2 ^ 59
def prefixEnd_1725875 : Nat := 4983230072969 + 3 ^ 40 * 1725875 * 2
def baseEnd_1725875 : Nat := 886203424578540239825351

theorem tailTrace_1725875 : CollatzResearch.WordTrace tailWord_1725875 prefixEnd_1725875 886203424578540239825351 := by
  unfold tailWord_1725875
  simp only [CollatzResearch.WordTrace]
  refine ⟨62947832622457105828387079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41965221748304737218924719 62947832622457105828387079)
  ·
    refine ⟨94421748933685658742580619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62947832622457105828387079 94421748933685658742580619)
    ·
      refine ⟨141632623400528488113870929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94421748933685658742580619 141632623400528488113870929)
      ·
        refine ⟨106224467550396366085403197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141632623400528488113870929 106224467550396366085403197)
        ·
          refine ⟨39834175331398637282026199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106224467550396366085403197 39834175331398637282026199)
          ·
            refine ⟨59751262997097955923039299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39834175331398637282026199 59751262997097955923039299)
            ·
              refine ⟨89626894495646933884558949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59751262997097955923039299 89626894495646933884558949)
              ·
                refine ⟨16805042717933800103354803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89626894495646933884558949 16805042717933800103354803)
                ·
                  refine ⟨25207564076900700155032205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16805042717933800103354803 25207564076900700155032205)
                  ·
                    refine ⟨9452836528837762558137077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25207564076900700155032205 9452836528837762558137077)
                    ·
                      refine ⟨886203424578540239825351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9452836528837762558137077 886203424578540239825351)
                      ·
                        rfl

theorem cell23_1725875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_1725875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725875 prefixEnd_1725875 := by exact prefixLift 1725875
  have htrace : WordTrace (prefixWord ++ tailWord_1725875) baseStart_1725875 baseEnd_1725875 := by
    simpa [prefixWord, tailWord_1725875, baseEnd_1725875] using wordTrace_append hprefix tailTrace_1725875
  have hstable : (prefixWord ++ tailWord_1725875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725875).length < 2 ^ (prefixWord ++ tailWord_1725875).sum := by decide
  have hdescent : baseEnd_1725875 < baseStart_1725875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725890 : List Nat := [3, 5, 2, 1, 1, 1, 3, 7]
def baseStart_1725890 : Nat := 118140960795 + 1725890 * 2 ^ 59
def prefixEnd_1725890 : Nat := 4983230072969 + 3 ^ 40 * 1725890 * 2
def baseEnd_1725890 : Nat := 32822634325494728931029

theorem tailTrace_1725890 : CollatzResearch.WordTrace tailWord_1725890 prefixEnd_1725890 32822634325494728931029 := by
  unfold tailWord_1725890
  simp only [CollatzResearch.WordTrace]
  refine ⟨15737094929350690847545781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41965586478268508926788749 15737094929350690847545781)
  ·
    refine ⟨1475352649626627266957417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15737094929350690847545781 1475352649626627266957417)
    ·
      refine ⟨1106514487219970450218063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1475352649626627266957417 1106514487219970450218063)
      ·
        refine ⟨1659771730829955675327095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1106514487219970450218063 1659771730829955675327095)
        ·
          refine ⟨2489657596244933512990643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1659771730829955675327095 2489657596244933512990643)
          ·
            refine ⟨3734486394367400269485965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2489657596244933512990643 3734486394367400269485965)
            ·
              refine ⟨1400432397887775101057237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3734486394367400269485965 1400432397887775101057237)
              ·
                refine ⟨32822634325494728931029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1400432397887775101057237 32822634325494728931029)
                ·
                  rfl

theorem cell23_1725890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 7].length) (baseStart_1725890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725890 prefixEnd_1725890 := by exact prefixLift 1725890
  have htrace : WordTrace (prefixWord ++ tailWord_1725890) baseStart_1725890 baseEnd_1725890 := by
    simpa [prefixWord, tailWord_1725890, baseEnd_1725890] using wordTrace_append hprefix tailTrace_1725890
  have hstable : (prefixWord ++ tailWord_1725890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725890).length < 2 ^ (prefixWord ++ tailWord_1725890).sum := by decide
  have hdescent : baseEnd_1725890 < baseStart_1725890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725905 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 7]
def baseStart_1725905 : Nat := 118140960795 + 1725905 * 2 ^ 59
def prefixEnd_1725905 : Nat := 4983230072969 + 3 ^ 40 * 1725905 * 2
def baseEnd_1725905 : Nat := 886218828998175122450213

theorem tailTrace_1725905 : CollatzResearch.WordTrace tailWord_1725905 prefixEnd_1725905 886218828998175122450213 := by
  unfold tailWord_1725905
  simp only [CollatzResearch.WordTrace]
  refine ⟨62948926812348420951979169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41965951208232280634652779 62948926812348420951979169)
  ·
    refine ⟨47211695109261315713984377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62948926812348420951979169 47211695109261315713984377)
    ·
      refine ⟨35408771331945986785488283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47211695109261315713984377 35408771331945986785488283)
      ·
        refine ⟨53113156997918980178232425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35408771331945986785488283 53113156997918980178232425)
        ·
          refine ⟨39834867748439235133674319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53113156997918980178232425 39834867748439235133674319)
          ·
            refine ⟨59752301622658852700511479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39834867748439235133674319 59752301622658852700511479)
            ·
              refine ⟨89628452433988279050767219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59752301622658852700511479 89628452433988279050767219)
              ·
                refine ⟨134442678650982418576150829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89628452433988279050767219 134442678650982418576150829)
                ·
                  refine ⟨50416004494118406966056561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134442678650982418576150829 50416004494118406966056561)
                  ·
                    refine ⟨37812003370588805224542421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50416004494118406966056561 37812003370588805224542421)
                    ·
                      refine ⟨886218828998175122450213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37812003370588805224542421 886218828998175122450213)
                      ·
                        rfl

theorem cell23_1725905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_1725905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725905 prefixEnd_1725905 := by exact prefixLift 1725905
  have htrace : WordTrace (prefixWord ++ tailWord_1725905) baseStart_1725905 baseEnd_1725905 := by
    simpa [prefixWord, tailWord_1725905, baseEnd_1725905] using wordTrace_append hprefix tailTrace_1725905
  have hstable : (prefixWord ++ tailWord_1725905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725905).length < 2 ^ (prefixWord ++ tailWord_1725905).sum := by decide
  have hdescent : baseEnd_1725905 < baseStart_1725905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725910 : List Nat := [5, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_1725910 : Nat := 118140960795 + 1725910 * 2 ^ 59
def prefixEnd_1725910 : Nat := 4983230072969 + 3 ^ 40 * 1725910 * 2
def baseEnd_1725910 : Nat := 886221396401447602887691

theorem tailTrace_1725910 : CollatzResearch.WordTrace tailWord_1725910 prefixEnd_1725910 886221396401447602887691 := by
  unfold tailWord_1725910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3934319323583144175369449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41966072784886871203940789 3934319323583144175369449)
  ·
    refine ⟨2950739492687358131527087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3934319323583144175369449 2950739492687358131527087)
    ·
      refine ⟨4426109239031037197290631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2950739492687358131527087 4426109239031037197290631)
      ·
        refine ⟨6639163858546555795935947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4426109239031037197290631 6639163858546555795935947)
        ·
          refine ⟨9958745787819833693903921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6639163858546555795935947 9958745787819833693903921)
          ·
            refine ⟨7469059340864875270427941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9958745787819833693903921 7469059340864875270427941)
            ·
              refine ⟨1400448626412164113205239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7469059340864875270427941 1400448626412164113205239)
              ·
                refine ⟨2100672939618246169807859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1400448626412164113205239 2100672939618246169807859)
                ·
                  refine ⟨3151009409427369254711789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2100672939618246169807859 3151009409427369254711789)
                  ·
                    refine ⟨1181628528535263470516921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3151009409427369254711789 1181628528535263470516921)
                    ·
                      refine ⟨886221396401447602887691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1181628528535263470516921 886221396401447602887691)
                      ·
                        rfl

theorem cell23_1725910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_1725910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725910 prefixEnd_1725910 := by exact prefixLift 1725910
  have htrace : WordTrace (prefixWord ++ tailWord_1725910) baseStart_1725910 baseEnd_1725910 := by
    simpa [prefixWord, tailWord_1725910, baseEnd_1725910] using wordTrace_append hprefix tailTrace_1725910
  have hstable : (prefixWord ++ tailWord_1725910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725910).length < 2 ^ (prefixWord ++ tailWord_1725910).sum := by decide
  have hdescent : baseEnd_1725910 < baseStart_1725910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725923 : List Nat := [1, 1, 1, 6, 2, 1, 3, 2, 2, 2, 2]
def baseStart_1725923 : Nat := 118140960795 + 1725923 * 2 ^ 59
def prefixEnd_1725923 : Nat := 4983230072969 + 3 ^ 40 * 1725923 * 2
def baseEnd_1725923 : Nat := 886228071649956052025131

theorem tailTrace_1725923 : CollatzResearch.WordTrace tailWord_1725923 prefixEnd_1725923 886228071649956052025131 := by
  unfold tailWord_1725923
  simp only [CollatzResearch.WordTrace]
  refine ⟨62949583326283210026134423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41966388884188806684089615 62949583326283210026134423)
  ·
    refine ⟨94424374989424815039201635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62949583326283210026134423 94424374989424815039201635)
    ·
      refine ⟨141636562484137222558802453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94424374989424815039201635 141636562484137222558802453)
      ·
        refine ⟨6639213866443932307443865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 141636562484137222558802453 6639213866443932307443865)
        ·
          refine ⟨4979410399832949230582899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6639213866443932307443865 4979410399832949230582899)
          ·
            refine ⟨7469115599749423845874349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4979410399832949230582899 7469115599749423845874349)
            ·
              refine ⟨2800918349906033942202881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7469115599749423845874349 2800918349906033942202881)
              ·
                refine ⟨2100688762429525456652161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2800918349906033942202881 2100688762429525456652161)
                ·
                  refine ⟨1575516571822144092489121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2100688762429525456652161 1575516571822144092489121)
                  ·
                    refine ⟨1181637428866608069366841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1575516571822144092489121 1181637428866608069366841)
                    ·
                      refine ⟨886228071649956052025131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1181637428866608069366841 886228071649956052025131)
                      ·
                        rfl

theorem cell23_1725923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_1725923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725923 prefixEnd_1725923 := by exact prefixLift 1725923
  have htrace : WordTrace (prefixWord ++ tailWord_1725923) baseStart_1725923 baseEnd_1725923 := by
    simpa [prefixWord, tailWord_1725923, baseEnd_1725923] using wordTrace_append hprefix tailTrace_1725923
  have hstable : (prefixWord ++ tailWord_1725923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725923).length < 2 ^ (prefixWord ++ tailWord_1725923).sum := by decide
  have hdescent : baseEnd_1725923 < baseStart_1725923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1725963 : List Nat := [1, 1, 1, 1, 9, 1, 1, 3, 5]
def baseStart_1725963 : Nat := 118140960795 + 1725963 * 2 ^ 59
def prefixEnd_1725963 : Nat := 4983230072969 + 3 ^ 40 * 1725963 * 2
def baseEnd_1725963 : Nat := 98472067875126210613883

theorem tailTrace_1725963 : CollatzResearch.WordTrace tailWord_1725963 prefixEnd_1725963 98472067875126210613883 := by
  unfold tailWord_1725963
  simp only [CollatzResearch.WordTrace]
  refine ⟨62951042246138296857590543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41967361497425531238393695 62951042246138296857590543)
  ·
    refine ⟨94426563369207445286385815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62951042246138296857590543 94426563369207445286385815)
    ·
      refine ⟨141639845053811167929578723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94426563369207445286385815 141639845053811167929578723)
      ·
        refine ⟨212459767580716751894368085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141639845053811167929578723 212459767580716751894368085)
        ·
          refine ⟨1244881450668262218131063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 212459767580716751894368085 1244881450668262218131063)
          ·
            refine ⟨1867322176002393327196595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244881450668262218131063 1867322176002393327196595)
            ·
              refine ⟨2800983264003589990794893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1867322176002393327196595 2800983264003589990794893)
              ·
                refine ⟨1050368724001346246548085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2800983264003589990794893 1050368724001346246548085)
                ·
                  refine ⟨98472067875126210613883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1050368724001346246548085 98472067875126210613883)
                  ·
                    rfl

theorem cell23_1725963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 5].length) (baseStart_1725963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1725963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1725963 prefixEnd_1725963 := by exact prefixLift 1725963
  have htrace : WordTrace (prefixWord ++ tailWord_1725963) baseStart_1725963 baseEnd_1725963 := by
    simpa [prefixWord, tailWord_1725963, baseEnd_1725963] using wordTrace_append hprefix tailTrace_1725963
  have hstable : (prefixWord ++ tailWord_1725963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1725963).length < 2 ^ (prefixWord ++ tailWord_1725963).sum := by decide
  have hdescent : baseEnd_1725963 < baseStart_1725963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1725963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726042 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5]
def baseStart_1726042 : Nat := 118140960795 + 1726042 * 2 ^ 59
def prefixEnd_1726042 : Nat := 4983230072969 + 3 ^ 40 * 1726042 * 2
def baseEnd_1726042 : Nat := 886289175847841086437083

theorem tailTrace_1726042 : CollatzResearch.WordTrace tailWord_1726042 prefixEnd_1726042 886289175847841086437083 := by
  unfold tailWord_1726042
  simp only [CollatzResearch.WordTrace]
  refine ⟨15738480903213023337429095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41969282408568062233144253 15738480903213023337429095)
  ·
    refine ⟨23607721354819535006143643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15738480903213023337429095 23607721354819535006143643)
    ·
      refine ⟨35411582032229302509215465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23607721354819535006143643 35411582032229302509215465)
      ·
        refine ⟨26558686524171976881911599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35411582032229302509215465 26558686524171976881911599)
        ·
          refine ⟨39838029786257965322867399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26558686524171976881911599 39838029786257965322867399)
          ·
            refine ⟨59757044679386947984301099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39838029786257965322867399 59757044679386947984301099)
            ·
              refine ⟨89635567019080421976451649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59757044679386947984301099 89635567019080421976451649)
              ·
                refine ⟨67226675264310316482338737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89635567019080421976451649 67226675264310316482338737)
                ·
                  refine ⟨50420006448232737361754053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67226675264310316482338737 50420006448232737361754053)
                  ·
                    refine ⟨9453751209043638255328885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50420006448232737361754053 9453751209043638255328885)
                    ·
                      refine ⟨886289175847841086437083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9453751209043638255328885 886289175847841086437083)
                      ·
                        rfl

theorem cell23_1726042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_1726042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726042 prefixEnd_1726042 := by exact prefixLift 1726042
  have htrace : WordTrace (prefixWord ++ tailWord_1726042) baseStart_1726042 baseEnd_1726042 := by
    simpa [prefixWord, tailWord_1726042, baseEnd_1726042] using wordTrace_append hprefix tailTrace_1726042
  have hstable : (prefixWord ++ tailWord_1726042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726042).length < 2 ^ (prefixWord ++ tailWord_1726042).sum := by decide
  have hdescent : baseEnd_1726042 < baseStart_1726042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726072 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 2, 5, 5]
def baseStart_1726072 : Nat := 118140960795 + 1726072 * 2 ^ 59
def prefixEnd_1726072 : Nat := 4983230072969 + 3 ^ 40 * 1726072 * 2
def baseEnd_1726072 : Nat := 886304580267475969061945

theorem tailTrace_1726072 : CollatzResearch.WordTrace tailWord_1726072 prefixEnd_1726072 886304580267475969061945 := by
  unfold tailWord_1726072
  simp only [CollatzResearch.WordTrace]
  refine ⟨31477508901371704236654235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41970011868495605648872313 31477508901371704236654235)
  ·
    refine ⟨47216263352057556354981353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31477508901371704236654235 47216263352057556354981353)
    ·
      refine ⟨35412197514043167266236015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47216263352057556354981353 35412197514043167266236015)
      ·
        refine ⟨53118296271064750899354023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35412197514043167266236015 53118296271064750899354023)
        ·
          refine ⟨79677444406597126349031035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53118296271064750899354023 79677444406597126349031035)
          ·
            refine ⟨119516166609895689523546553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79677444406597126349031035 119516166609895689523546553)
            ·
              refine ⟨89637124957421767142659915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119516166609895689523546553 89637124957421767142659915)
              ·
                refine ⟨134455687436132650713989873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89637124957421767142659915 134455687436132650713989873)
                ·
                  refine ⟨100841765577099488035492405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134455687436132650713989873 100841765577099488035492405)
                  ·
                    refine ⟨9453915522853077003327413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100841765577099488035492405 9453915522853077003327413)
                    ·
                      refine ⟨886304580267475969061945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9453915522853077003327413 886304580267475969061945)
                      ·
                        rfl

theorem cell23_1726072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_1726072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726072 prefixEnd_1726072 := by exact prefixLift 1726072
  have htrace : WordTrace (prefixWord ++ tailWord_1726072) baseStart_1726072 baseEnd_1726072 := by
    simpa [prefixWord, tailWord_1726072, baseEnd_1726072] using wordTrace_append hprefix tailTrace_1726072
  have hstable : (prefixWord ++ tailWord_1726072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726072).length < 2 ^ (prefixWord ++ tailWord_1726072).sum := by decide
  have hdescent : baseEnd_1726072 < baseStart_1726072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726092 : List Nat := [2, 2, 1, 2, 1, 1, 14]
def baseStart_1726092 : Nat := 118140960795 + 1726092 * 2 ^ 59
def prefixEnd_1726092 : Nat := 4983230072969 + 3 ^ 40 * 1726092 * 2
def baseEnd_1726092 : Nat := 10942158640500813466813

theorem tailTrace_1726092 : CollatzResearch.WordTrace tailWord_1726092 prefixEnd_1726092 10942158640500813466813 := by
  unfold tailWord_1726092
  simp only [CollatzResearch.WordTrace]
  refine ⟨31477873631335475944518265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41970498175113967926024353 31477873631335475944518265)
  ·
    refine ⟨23608405223501606958388699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31477873631335475944518265 23608405223501606958388699)
    ·
      refine ⟨35412607835252410437583049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23608405223501606958388699 35412607835252410437583049)
      ·
        refine ⟨26559455876439307828187287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35412607835252410437583049 26559455876439307828187287)
        ·
          refine ⟨39839183814658961742280931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26559455876439307828187287 39839183814658961742280931)
          ·
            refine ⟨59758775721988442613421397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39839183814658961742280931 59758775721988442613421397)
            ·
              refine ⟨10942158640500813466813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 59758775721988442613421397 10942158640500813466813)
              ·
                rfl

theorem cell23_1726092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 14].length) (baseStart_1726092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726092 prefixEnd_1726092 := by exact prefixLift 1726092
  have htrace : WordTrace (prefixWord ++ tailWord_1726092) baseStart_1726092 baseEnd_1726092 := by
    simpa [prefixWord, tailWord_1726092, baseEnd_1726092] using wordTrace_append hprefix tailTrace_1726092
  have hstable : (prefixWord ++ tailWord_1726092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726092).length < 2 ^ (prefixWord ++ tailWord_1726092).sum := by decide
  have hdescent : baseEnd_1726092 < baseStart_1726092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726103 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 3, 2, 2]
def baseStart_1726103 : Nat := 118140960795 + 1726103 * 2 ^ 59
def prefixEnd_1726103 : Nat := 4983230072969 + 3 ^ 40 * 1726103 * 2
def baseEnd_1726103 : Nat := 886320498167765347774303

theorem tailTrace_1726103 : CollatzResearch.WordTrace tailWord_1726103 prefixEnd_1726103 886320498167765347774303 := by
  unfold tailWord_1726103
  simp only [CollatzResearch.WordTrace]
  refine ⟨62956148465631100767686963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41970765643754067178457975 62956148465631100767686963)
  ·
    refine ⟨94434222698446651151530445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62956148465631100767686963 94434222698446651151530445)
    ·
      refine ⟨35412833511917494181823917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94434222698446651151530445 35412833511917494181823917)
      ·
        refine ⟨13279812566969060318183969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35412833511917494181823917 13279812566969060318183969)
        ·
          refine ⟨9959859425226795238637977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13279812566969060318183969 9959859425226795238637977)
          ·
            refine ⟨7469894568920096428978483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9959859425226795238637977 7469894568920096428978483)
            ·
              refine ⟨11204841853380144643467725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7469894568920096428978483 11204841853380144643467725)
              ·
                refine ⟨4201815695017554241300397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11204841853380144643467725 4201815695017554241300397)
                ·
                  refine ⟨1575680885631582840487649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4201815695017554241300397 1575680885631582840487649)
                  ·
                    refine ⟨1181760664223687130365737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1575680885631582840487649 1181760664223687130365737)
                    ·
                      refine ⟨886320498167765347774303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1181760664223687130365737 886320498167765347774303)
                      ·
                        rfl

theorem cell23_1726103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_1726103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726103 prefixEnd_1726103 := by exact prefixLift 1726103
  have htrace : WordTrace (prefixWord ++ tailWord_1726103) baseStart_1726103 baseEnd_1726103 := by
    simpa [prefixWord, tailWord_1726103, baseEnd_1726103] using wordTrace_append hprefix tailTrace_1726103
  have hstable : (prefixWord ++ tailWord_1726103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726103).length < 2 ^ (prefixWord ++ tailWord_1726103).sum := by decide
  have hdescent : baseEnd_1726103 < baseStart_1726103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726116 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 1, 2, 4]
def baseStart_1726116 : Nat := 118140960795 + 1726116 * 2 ^ 59
def prefixEnd_1726116 : Nat := 4983230072969 + 3 ^ 40 * 1726116 * 2
def baseEnd_1726116 : Nat := 886327173416273796911743

theorem tailTrace_1726116 : CollatzResearch.WordTrace tailWord_1726116 prefixEnd_1726116 886327173416273796911743 := by
  unfold tailWord_1726116
  simp only [CollatzResearch.WordTrace]
  refine ⟨31478311307292001993955101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41971081743056002658606801 31478311307292001993955101)
  ·
    refine ⟨11804366740234500747733163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31478311307292001993955101 11804366740234500747733163)
    ·
      refine ⟨17706550110351751121599745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11804366740234500747733163 17706550110351751121599745)
      ·
        refine ⟨13279912582763813341199809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17706550110351751121599745 13279912582763813341199809)
        ·
          refine ⟨9959934437072860005899857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13279912582763813341199809 9959934437072860005899857)
          ·
            refine ⟨7469950827804645004424893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9959934437072860005899857 7469950827804645004424893)
            ·
              refine ⟨2801231560426741876659335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7469950827804645004424893 2801231560426741876659335)
              ·
                refine ⟨4201847340640112814989003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2801231560426741876659335 4201847340640112814989003)
                ·
                  refine ⟨6302771010960169222483505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4201847340640112814989003 6302771010960169222483505)
                  ·
                    refine ⟨4727078258220126916862629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6302771010960169222483505 4727078258220126916862629)
                    ·
                      refine ⟨886327173416273796911743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4727078258220126916862629 886327173416273796911743)
                      ·
                        rfl

theorem cell23_1726116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_1726116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726116 prefixEnd_1726116 := by exact prefixLift 1726116
  have htrace : WordTrace (prefixWord ++ tailWord_1726116) baseStart_1726116 baseEnd_1726116 := by
    simpa [prefixWord, tailWord_1726116, baseEnd_1726116] using wordTrace_append hprefix tailTrace_1726116
  have hstable : (prefixWord ++ tailWord_1726116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726116).length < 2 ^ (prefixWord ++ tailWord_1726116).sum := by decide
  have hdescent : baseEnd_1726116 < baseStart_1726116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726154 : List Nat := [3, 1, 2, 1, 5, 1, 3, 2, 1, 2, 2]
def baseStart_1726154 : Nat := 118140960795 + 1726154 * 2 ^ 59
def prefixEnd_1726154 : Nat := 4983230072969 + 3 ^ 40 * 1726154 * 2
def baseEnd_1726154 : Nat := 886346685681144648236569

theorem tailTrace_1726154 : CollatzResearch.WordTrace tailWord_1726154 prefixEnd_1726154 886346685681144648236569 := by
  unfold tailWord_1726154
  simp only [CollatzResearch.WordTrace]
  refine ⟨15739502147111584119448379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41972005725630890985195677 15739502147111584119448379)
  ·
    refine ⟨23609253220667376179172569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15739502147111584119448379 23609253220667376179172569)
    ·
      refine ⟨17706939915500532134379427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23609253220667376179172569 17706939915500532134379427)
      ·
        refine ⟨26560409873250798201569141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17706939915500532134379427 26560409873250798201569141)
        ·
          refine ⟨2490038425617262331397107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26560409873250798201569141 2490038425617262331397107)
          ·
            refine ⟨3735057638425893497095661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490038425617262331397107 3735057638425893497095661)
            ·
              refine ⟨1400646614409710061410873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3735057638425893497095661 1400646614409710061410873)
              ·
                refine ⟨1050484960807282546058155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1400646614409710061410873 1050484960807282546058155)
                ·
                  refine ⟨1575727441210923819087233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050484960807282546058155 1575727441210923819087233)
                  ·
                    refine ⟨1181795580908192864315425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1575727441210923819087233 1181795580908192864315425)
                    ·
                      refine ⟨886346685681144648236569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1181795580908192864315425 886346685681144648236569)
                      ·
                        rfl

theorem cell23_1726154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_1726154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726154 prefixEnd_1726154 := by exact prefixLift 1726154
  have htrace : WordTrace (prefixWord ++ tailWord_1726154) baseStart_1726154 baseEnd_1726154 := by
    simpa [prefixWord, tailWord_1726154, baseEnd_1726154] using wordTrace_append hprefix tailTrace_1726154
  have hstable : (prefixWord ++ tailWord_1726154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726154).length < 2 ^ (prefixWord ++ tailWord_1726154).sum := by decide
  have hdescent : baseEnd_1726154 < baseStart_1726154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726170 : List Nat := [3, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3]
def baseStart_1726170 : Nat := 118140960795 + 1726170 * 2 ^ 59
def prefixEnd_1726170 : Nat := 4983230072969 + 3 ^ 40 * 1726170 * 2
def baseEnd_1726170 : Nat := 886354901371616585636495

theorem tailTrace_1726170 : CollatzResearch.WordTrace tailWord_1726170 prefixEnd_1726170 886354901371616585636495 := by
  unfold tailWord_1726170
  simp only [CollatzResearch.WordTrace]
  refine ⟨15739648039097092802593991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41972394770925580806917309 15739648039097092802593991)
  ·
    refine ⟨23609472058645639203890987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15739648039097092802593991 23609472058645639203890987)
    ·
      refine ⟨35414208087968458805836481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23609472058645639203890987 35414208087968458805836481)
      ·
        refine ⟨26560656065976344104377361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35414208087968458805836481 26560656065976344104377361)
        ·
          refine ⟨19920492049482258078283021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26560656065976344104377361 19920492049482258078283021)
          ·
            refine ⟨7470184518555846779356133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19920492049482258078283021 7470184518555846779356133)
            ·
              refine ⟨1400659597229221271129275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7470184518555846779356133 1400659597229221271129275)
              ·
                refine ⟨2100989395843831906693913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1400659597229221271129275 2100989395843831906693913)
                ·
                  refine ⟨1575742046882873930020435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2100989395843831906693913 1575742046882873930020435)
                  ·
                    refine ⟨2363613070324310895030653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1575742046882873930020435 2363613070324310895030653)
                    ·
                      refine ⟨886354901371616585636495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2363613070324310895030653 886354901371616585636495)
                      ·
                        rfl

theorem cell23_1726170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_1726170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726170 prefixEnd_1726170 := by exact prefixLift 1726170
  have htrace : WordTrace (prefixWord ++ tailWord_1726170) baseStart_1726170 baseEnd_1726170 := by
    simpa [prefixWord, tailWord_1726170, baseEnd_1726170] using wordTrace_append hprefix tailTrace_1726170
  have hstable : (prefixWord ++ tailWord_1726170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726170).length < 2 ^ (prefixWord ++ tailWord_1726170).sum := by decide
  have hdescent : baseEnd_1726170 < baseStart_1726170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726193 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 1, 4, 2]
def baseStart_1726193 : Nat := 118140960795 + 1726193 * 2 ^ 59
def prefixEnd_1726193 : Nat := 4983230072969 + 3 ^ 40 * 1726193 * 2
def baseEnd_1726193 : Nat := 886366711426669995648889

theorem tailTrace_1726193 : CollatzResearch.WordTrace tailWord_1726193 prefixEnd_1726193 886366711426669995648889 := by
  unfold tailWord_1726193
  simp only [CollatzResearch.WordTrace]
  refine ⟨62959431035305046138463233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41972954023536697425642155 62959431035305046138463233)
  ·
    refine ⟨47219573276478784603847425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62959431035305046138463233 47219573276478784603847425)
    ·
      refine ⟨35414679957359088452885569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47219573276478784603847425 35414679957359088452885569)
      ·
        refine ⟨26561009968019316339664177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35414679957359088452885569 26561009968019316339664177)
        ·
          refine ⟨19920757476014487254748133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26561009968019316339664177 19920757476014487254748133)
          ·
            refine ⟨3735142026752716360265275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19920757476014487254748133 3735142026752716360265275)
            ·
              refine ⟨5602713040129074540397913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3735142026752716360265275 5602713040129074540397913)
              ·
                refine ⟨4202034780096805905298435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5602713040129074540397913 4202034780096805905298435)
                ·
                  refine ⟨6303052170145208857947653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4202034780096805905298435 6303052170145208857947653)
                  ·
                    refine ⟨1181822281902226660865185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6303052170145208857947653 1181822281902226660865185)
                    ·
                      refine ⟨886366711426669995648889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1181822281902226660865185 886366711426669995648889)
                      ·
                        rfl

theorem cell23_1726193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_1726193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726193 prefixEnd_1726193 := by exact prefixLift 1726193
  have htrace : WordTrace (prefixWord ++ tailWord_1726193) baseStart_1726193 baseEnd_1726193 := by
    simpa [prefixWord, tailWord_1726193, baseEnd_1726193] using wordTrace_append hprefix tailTrace_1726193
  have hstable : (prefixWord ++ tailWord_1726193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726193).length < 2 ^ (prefixWord ++ tailWord_1726193).sum := by decide
  have hdescent : baseEnd_1726193 < baseStart_1726193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726209 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_1726209 : Nat := 118140960795 + 1726209 * 2 ^ 59
def prefixEnd_1726209 : Nat := 4983230072969 + 3 ^ 40 * 1726209 * 2
def baseEnd_1726209 : Nat := 886374927117141933048815

theorem tailTrace_1726209 : CollatzResearch.WordTrace tailWord_1726209 prefixEnd_1726209 886374927117141933048815 := by
  unfold tailWord_1726209
  simp only [CollatzResearch.WordTrace]
  refine ⟨62960014603247080871045681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41973343068831387247363787 62960014603247080871045681)
  ·
    refine ⟨47220010952435310653284261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62960014603247080871045681 47220010952435310653284261)
    ·
      refine ⟨8853752053581620747490799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47220010952435310653284261 8853752053581620747490799)
      ·
        refine ⟨13280628080372431121236199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8853752053581620747490799 13280628080372431121236199)
        ·
          refine ⟨19920942120558646681854299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13280628080372431121236199 19920942120558646681854299)
          ·
            refine ⟨29881413180837970022781449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19920942120558646681854299 29881413180837970022781449)
            ·
              refine ⟨22411059885628477517086087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29881413180837970022781449 22411059885628477517086087)
              ·
                refine ⟨33616589828442716275629131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22411059885628477517086087 33616589828442716275629131)
                ·
                  refine ⟨50424884742664074413443697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33616589828442716275629131 50424884742664074413443697)
                  ·
                    refine ⟨37818663556998055810082773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50424884742664074413443697 37818663556998055810082773)
                    ·
                      refine ⟨886374927117141933048815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37818663556998055810082773 886374927117141933048815)
                      ·
                        rfl

theorem cell23_1726209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_1726209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726209 prefixEnd_1726209 := by exact prefixLift 1726209
  have htrace : WordTrace (prefixWord ++ tailWord_1726209) baseStart_1726209 baseEnd_1726209 := by
    simpa [prefixWord, tailWord_1726209, baseEnd_1726209] using wordTrace_append hprefix tailTrace_1726209
  have hstable : (prefixWord ++ tailWord_1726209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726209).length < 2 ^ (prefixWord ++ tailWord_1726209).sum := by decide
  have hdescent : baseEnd_1726209 < baseStart_1726209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726293 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 3, 4]
def baseStart_1726293 : Nat := 118140960795 + 1726293 * 2 ^ 59
def prefixEnd_1726293 : Nat := 4983230072969 + 3 ^ 40 * 1726293 * 2
def baseEnd_1726293 : Nat := 295472686497373201466143

theorem tailTrace_1726293 : CollatzResearch.WordTrace tailWord_1726293 prefixEnd_1726293 295472686497373201466143 := by
  unfold tailWord_1726293
  simp only [CollatzResearch.WordTrace]
  refine ⟨62963078334942763217103533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41975385556628508811402355 62963078334942763217103533)
  ·
    refine ⟨23611154375603536206413825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62963078334942763217103533 23611154375603536206413825)
    ·
      refine ⟨17708365781702652154810369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23611154375603536206413825 17708365781702652154810369)
      ·
        refine ⟨13281274336276989116107777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17708365781702652154810369 13281274336276989116107777)
        ·
          refine ⟨9960955752207741837080833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13281274336276989116107777 9960955752207741837080833)
          ·
            refine ⟨7470716814155806377810625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9960955752207741837080833 7470716814155806377810625)
            ·
              refine ⟨5603037610616854783357969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7470716814155806377810625 5603037610616854783357969)
              ·
                refine ⟨4202278207962641087518477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5603037610616854783357969 4202278207962641087518477)
                ·
                  refine ⟨1575854327985990407819429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4202278207962641087518477 1575854327985990407819429)
                  ·
                    refine ⟨295472686497373201466143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1575854327985990407819429 295472686497373201466143)
                    ·
                      rfl

theorem cell23_1726293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_1726293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726293 prefixEnd_1726293 := by exact prefixLift 1726293
  have htrace : WordTrace (prefixWord ++ tailWord_1726293) baseStart_1726293 baseEnd_1726293 := by
    simpa [prefixWord, tailWord_1726293, baseEnd_1726293] using wordTrace_append hprefix tailTrace_1726293
  have hstable : (prefixWord ++ tailWord_1726293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726293).length < 2 ^ (prefixWord ++ tailWord_1726293).sum := by decide
  have hdescent : baseEnd_1726293 < baseStart_1726293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726336 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 3, 5]
def baseStart_1726336 : Nat := 118140960795 + 1726336 * 2 ^ 59
def prefixEnd_1726336 : Nat := 4983230072969 + 3 ^ 40 * 1726336 * 2
def baseEnd_1726336 : Nat := 295480046386754312053577

theorem tailTrace_1726336 : CollatzResearch.WordTrace tailWord_1726336 prefixEnd_1726336 295480046386754312053577 := by
  unfold tailWord_1726336
  simp only [CollatzResearch.WordTrace]
  refine ⟨31482323336893490780459431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41976431115857987707279241 31482323336893490780459431)
  ·
    refine ⟨47223485005340236170689147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31482323336893490780459431 47223485005340236170689147)
    ·
      refine ⟨70835227508010354256033721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47223485005340236170689147 70835227508010354256033721)
      ·
        refine ⟨53126420631007765692025291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70835227508010354256033721 53126420631007765692025291)
        ·
          refine ⟨79689630946511648538037937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53126420631007765692025291 79689630946511648538037937)
          ·
            refine ⟨59767223209883736403528453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79689630946511648538037937 59767223209883736403528453)
            ·
              refine ⟨11206354351853200575661585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59767223209883736403528453 11206354351853200575661585)
              ·
                refine ⟨8404765763889900431746189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11206354351853200575661585 8404765763889900431746189)
                ·
                  refine ⟨3151787161458712661904821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8404765763889900431746189 3151787161458712661904821)
                  ·
                    refine ⟨295480046386754312053577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3151787161458712661904821 295480046386754312053577)
                    ·
                      rfl

theorem cell23_1726336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 3, 5].length) (baseStart_1726336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726336 prefixEnd_1726336 := by exact prefixLift 1726336
  have htrace : WordTrace (prefixWord ++ tailWord_1726336) baseStart_1726336 baseEnd_1726336 := by
    simpa [prefixWord, tailWord_1726336, baseEnd_1726336] using wordTrace_append hprefix tailTrace_1726336
  have hstable : (prefixWord ++ tailWord_1726336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726336).length < 2 ^ (prefixWord ++ tailWord_1726336).sum := by decide
  have hdescent : baseEnd_1726336 < baseStart_1726336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726353 : List Nat := [1, 2, 2, 1, 1, 1, 7, 2, 1, 5]
def baseStart_1726353 : Nat := 118140960795 + 1726353 * 2 ^ 59
def prefixEnd_1726353 : Nat := 4983230072969 + 3 ^ 40 * 1726353 * 2
def baseEnd_1726353 : Nat := 295482956110463123216051

theorem tailTrace_1726353 : CollatzResearch.WordTrace tailWord_1726353 prefixEnd_1726353 295482956110463123216051 := by
  unfold tailWord_1726353
  simp only [CollatzResearch.WordTrace]
  refine ⟨62965266714725393464287713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41976844476483595642858475 62965266714725393464287713)
  ·
    refine ⟨47223950036044045098215785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62965266714725393464287713 47223950036044045098215785)
    ·
      refine ⟨35417962527033033823661839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47223950036044045098215785 35417962527033033823661839)
      ·
        refine ⟨53126943790549550735492759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35417962527033033823661839 53126943790549550735492759)
        ·
          refine ⟨79690415685824326103239139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53126943790549550735492759 79690415685824326103239139)
          ·
            refine ⟨119535623528736489154858709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79690415685824326103239139 119535623528736489154858709)
            ·
              refine ⟨2801616176454761464567001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 119535623528736489154858709 2801616176454761464567001)
              ·
                refine ⟨2101212132341071098425251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2801616176454761464567001 2101212132341071098425251)
                ·
                  refine ⟨3151818198511606647637877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2101212132341071098425251 3151818198511606647637877)
                  ·
                    refine ⟨295482956110463123216051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3151818198511606647637877 295482956110463123216051)
                    ·
                      rfl

theorem cell23_1726353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_1726353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726353 prefixEnd_1726353 := by exact prefixLift 1726353
  have htrace : WordTrace (prefixWord ++ tailWord_1726353) baseStart_1726353 baseEnd_1726353 := by
    simpa [prefixWord, tailWord_1726353, baseEnd_1726353] using wordTrace_append hprefix tailTrace_1726353
  have hstable : (prefixWord ++ tailWord_1726353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726353).length < 2 ^ (prefixWord ++ tailWord_1726353).sum := by decide
  have hdescent : baseEnd_1726353 < baseStart_1726353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726373 : List Nat := [1, 3, 1, 2, 1, 1, 1, 7, 1, 1, 4]
def baseStart_1726373 : Nat := 118140960795 + 1726373 * 2 ^ 59
def prefixEnd_1726373 : Nat := 4983230072969 + 3 ^ 40 * 1726373 * 2
def baseEnd_1726373 : Nat := 886459137944479291398061

theorem tailTrace_1726373 : CollatzResearch.WordTrace tailWord_1726373 prefixEnd_1726373 886459137944479291398061 := by
  unfold tailWord_1726373
  simp only [CollatzResearch.WordTrace]
  refine ⟨62965996174652936880015773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41977330783101957920010515 62965996174652936880015773)
  ·
    refine ⟨23612248565494851330005915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62965996174652936880015773 23612248565494851330005915)
    ·
      refine ⟨35418372848242276995008873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23612248565494851330005915 35418372848242276995008873)
      ·
        refine ⟨26563779636181707746256655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35418372848242276995008873 26563779636181707746256655)
        ·
          refine ⟨39845669454272561619384983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26563779636181707746256655 39845669454272561619384983)
          ·
            refine ⟨59768504181408842429077475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39845669454272561619384983 59768504181408842429077475)
            ·
              refine ⟨89652756272113263643616213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59768504181408842429077475 89652756272113263643616213)
              ·
                refine ⟨2101236475127654616647255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 89652756272113263643616213 2101236475127654616647255)
                ·
                  refine ⟨3151854712691481924970883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2101236475127654616647255 3151854712691481924970883)
                  ·
                    refine ⟨4727782069037222887456325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3151854712691481924970883 4727782069037222887456325)
                    ·
                      refine ⟨886459137944479291398061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4727782069037222887456325 886459137944479291398061)
                      ·
                        rfl

theorem cell23_1726373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_1726373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726373 prefixEnd_1726373 := by exact prefixLift 1726373
  have htrace : WordTrace (prefixWord ++ tailWord_1726373) baseStart_1726373 baseEnd_1726373 := by
    simpa [prefixWord, tailWord_1726373, baseEnd_1726373] using wordTrace_append hprefix tailTrace_1726373
  have hstable : (prefixWord ++ tailWord_1726373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726373).length < 2 ^ (prefixWord ++ tailWord_1726373).sum := by decide
  have hdescent : baseEnd_1726373 < baseStart_1726373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726386 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_1726386 : Nat := 118140960795 + 1726386 * 2 ^ 59
def prefixEnd_1726386 : Nat := 4983230072969 + 3 ^ 40 * 1726386 * 2
def baseEnd_1726386 : Nat := 886465813192987740535501

theorem tailTrace_1726386 : CollatzResearch.WordTrace tailWord_1726386 prefixEnd_1726386 886465813192987740535501 := by
  unfold tailWord_1726386
  simp only [CollatzResearch.WordTrace]
  refine ⟨15741617580901460025059753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41977646882403893400159341 15741617580901460025059753)
  ·
    refine ⟨11806213185676095018794815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15741617580901460025059753 11806213185676095018794815)
    ·
      refine ⟨17709319778514142528192223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11806213185676095018794815 17709319778514142528192223)
      ·
        refine ⟨26563979667771213792288335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17709319778514142528192223 26563979667771213792288335)
        ·
          refine ⟨39845969501656820688432503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26563979667771213792288335 39845969501656820688432503)
          ·
            refine ⟨59768954252485231032648755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39845969501656820688432503 59768954252485231032648755)
            ·
              refine ⟨89653431378727846548973133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59768954252485231032648755 89653431378727846548973133)
              ·
                refine ⟨33620036767022942455864925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89653431378727846548973133 33620036767022942455864925)
                ·
                  refine ⟨12607513787633603420949347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33620036767022942455864925 12607513787633603420949347)
                  ·
                    refine ⟨18911270681450405131424021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12607513787633603420949347 18911270681450405131424021)
                    ·
                      refine ⟨886465813192987740535501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18911270681450405131424021 886465813192987740535501)
                      ·
                        rfl

theorem cell23_1726386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_1726386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726386 prefixEnd_1726386 := by exact prefixLift 1726386
  have htrace : WordTrace (prefixWord ++ tailWord_1726386) baseStart_1726386 baseEnd_1726386 := by
    simpa [prefixWord, tailWord_1726386, baseEnd_1726386] using wordTrace_append hprefix tailTrace_1726386
  have hstable : (prefixWord ++ tailWord_1726386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726386).length < 2 ^ (prefixWord ++ tailWord_1726386).sum := by decide
  have hdescent : baseEnd_1726386 < baseStart_1726386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726393 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 5, 2, 3]
def baseStart_1726393 : Nat := 118140960795 + 1726393 * 2 ^ 59
def prefixEnd_1726393 : Nat := 4983230072969 + 3 ^ 40 * 1726393 * 2
def baseEnd_1726393 : Nat := 886469407557569213147969

theorem tailTrace_1726393 : CollatzResearch.WordTrace tailWord_1726393 prefixEnd_1726393 886469407557569213147969 := by
  unfold tailWord_1726393
  simp only [CollatzResearch.WordTrace]
  refine ⟨62966725634580480295743833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41977817089720320197162555 62966725634580480295743833)
  ·
    refine ⟨47225044225935360221807875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62966725634580480295743833 47225044225935360221807875)
    ·
      refine ⟨70837566338903040332711813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47225044225935360221807875 70837566338903040332711813)
      ·
        refine ⟨13282043688544320062383465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70837566338903040332711813 13282043688544320062383465)
        ·
          refine ⟨9961532766408240046787599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13282043688544320062383465 9961532766408240046787599)
          ·
            refine ⟨14942299149612360070181399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9961532766408240046787599 14942299149612360070181399)
            ·
              refine ⟨22413448724418540105272099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14942299149612360070181399 22413448724418540105272099)
              ·
                refine ⟨33620173086627810157908149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22413448724418540105272099 33620173086627810157908149)
                ·
                  refine ⟨3151891226871357202303889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33620173086627810157908149 3151891226871357202303889)
                  ·
                    refine ⟨2363918420153517901727917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3151891226871357202303889 2363918420153517901727917)
                    ·
                      refine ⟨886469407557569213147969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2363918420153517901727917 886469407557569213147969)
                      ·
                        rfl

theorem cell23_1726393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_1726393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726393 prefixEnd_1726393 := by exact prefixLift 1726393
  have htrace : WordTrace (prefixWord ++ tailWord_1726393) baseStart_1726393 baseEnd_1726393 := by
    simpa [prefixWord, tailWord_1726393, baseEnd_1726393] using wordTrace_append hprefix tailTrace_1726393
  have hstable : (prefixWord ++ tailWord_1726393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726393).length < 2 ^ (prefixWord ++ tailWord_1726393).sum := by decide
  have hdescent : baseEnd_1726393 < baseStart_1726393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726423 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 3]
def baseStart_1726423 : Nat := 118140960795 + 1726423 * 2 ^ 59
def prefixEnd_1726423 : Nat := 4983230072969 + 3 ^ 40 * 1726423 * 2
def baseEnd_1726423 : Nat := 886484811977204095772831

theorem tailTrace_1726423 : CollatzResearch.WordTrace tailWord_1726423 prefixEnd_1726423 886484811977204095772831 := by
  unfold tailWord_1726423
  simp only [CollatzResearch.WordTrace]
  refine ⟨62967819824471795419335923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41978546549647863612890615 62967819824471795419335923)
  ·
    refine ⟨94451729736707693129003885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62967819824471795419335923 94451729736707693129003885)
    ·
      refine ⟨35419398651265384923376457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94451729736707693129003885 35419398651265384923376457)
      ·
        refine ⟨26564548988449038692532343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35419398651265384923376457 26564548988449038692532343)
        ·
          refine ⟨39846823482673558038798515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26564548988449038692532343 39846823482673558038798515)
          ·
            refine ⟨59770235224010337058197773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39846823482673558038798515 59770235224010337058197773)
            ·
              refine ⟨22413838209003876396824165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59770235224010337058197773 22413838209003876396824165)
              ·
                refine ⟨4202594664188226824404531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22413838209003876396824165 4202594664188226824404531)
                ·
                  refine ⟨6303891996282340236606797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4202594664188226824404531 6303891996282340236606797)
                  ·
                    refine ⟨2363959498605877588727549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6303891996282340236606797 2363959498605877588727549)
                    ·
                      refine ⟨886484811977204095772831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2363959498605877588727549 886484811977204095772831)
                      ·
                        rfl

theorem cell23_1726423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_1726423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726423 prefixEnd_1726423 := by exact prefixLift 1726423
  have htrace : WordTrace (prefixWord ++ tailWord_1726423) baseStart_1726423 baseEnd_1726423 := by
    simpa [prefixWord, tailWord_1726423, baseEnd_1726423] using wordTrace_append hprefix tailTrace_1726423
  have hstable : (prefixWord ++ tailWord_1726423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726423).length < 2 ^ (prefixWord ++ tailWord_1726423).sum := by decide
  have hdescent : baseEnd_1726423 < baseStart_1726423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726424 : List Nat := [2, 1, 2, 2, 2, 2, 4, 3, 1, 2, 2]
def baseStart_1726424 : Nat := 118140960795 + 1726424 * 2 ^ 59
def prefixEnd_1726424 : Nat := 4983230072969 + 3 ^ 40 * 1726424 * 2
def baseEnd_1726424 : Nat := 886485325457858591860327

theorem tailTrace_1726424 : CollatzResearch.WordTrace tailWord_1726424 prefixEnd_1726424 886485325457858591860327 := by
  unfold tailWord_1726424
  simp only [CollatzResearch.WordTrace]
  refine ⟨31483928148734086295061163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41978570864978781726748217 31483928148734086295061163)
  ·
    refine ⟨47225892223101129442591745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31483928148734086295061163 47225892223101129442591745)
    ·
      refine ⟨35419419167325847081943809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47225892223101129442591745 35419419167325847081943809)
      ·
        refine ⟨26564564375494385311457857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35419419167325847081943809 26564564375494385311457857)
        ·
          refine ⟨19923423281620788983593393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26564564375494385311457857 19923423281620788983593393)
          ·
            refine ⟨14942567461215591737695045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19923423281620788983593393 14942567461215591737695045)
            ·
              refine ⟨2801731398977923450817821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14942567461215591737695045 2801731398977923450817821)
              ·
                refine ⟨1050649274616721294056683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2801731398977923450817821 1050649274616721294056683)
                ·
                  refine ⟨1575973911925081941085025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050649274616721294056683 1575973911925081941085025)
                  ·
                    refine ⟨1181980433943811455813769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1575973911925081941085025 1181980433943811455813769)
                    ·
                      refine ⟨886485325457858591860327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1181980433943811455813769 886485325457858591860327)
                      ·
                        rfl

theorem cell23_1726424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_1726424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726424 prefixEnd_1726424 := by exact prefixLift 1726424
  have htrace : WordTrace (prefixWord ++ tailWord_1726424) baseStart_1726424 baseEnd_1726424 := by
    simpa [prefixWord, tailWord_1726424, baseEnd_1726424] using wordTrace_append hprefix tailTrace_1726424
  have hstable : (prefixWord ++ tailWord_1726424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726424).length < 2 ^ (prefixWord ++ tailWord_1726424).sum := by decide
  have hdescent : baseEnd_1726424 < baseStart_1726424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726454 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4]
def baseStart_1726454 : Nat := 118140960795 + 1726454 * 2 ^ 59
def prefixEnd_1726454 : Nat := 4983230072969 + 3 ^ 40 * 1726454 * 2
def baseEnd_1726454 : Nat := 886500729877493474485189

theorem tailTrace_1726454 : CollatzResearch.WordTrace tailWord_1726454 prefixEnd_1726454 886500729877493474485189 := by
  unfold tailWord_1726454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3935559405459967982107151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41979300324906325142476277 3935559405459967982107151)
  ·
    refine ⟨5903339108189951973160727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3935559405459967982107151 5903339108189951973160727)
    ·
      refine ⟨8855008662284927959741091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5903339108189951973160727 8855008662284927959741091)
      ·
        refine ⟨13282512993427391939611637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8855008662284927959741091 13282512993427391939611637)
        ·
          refine ⟨1245235593133817994338591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13282512993427391939611637 1245235593133817994338591)
          ·
            refine ⟨1867853389700726991507887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245235593133817994338591 1867853389700726991507887)
            ·
              refine ⟨2801780084551090487261831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1867853389700726991507887 2801780084551090487261831)
              ·
                refine ⟨4202670126826635730892747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2801780084551090487261831 4202670126826635730892747)
                ·
                  refine ⟨6304005190239953596339121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4202670126826635730892747 6304005190239953596339121)
                  ·
                    refine ⟨4728003892679965197254341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6304005190239953596339121 4728003892679965197254341)
                    ·
                      refine ⟨886500729877493474485189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4728003892679965197254341 886500729877493474485189)
                      ·
                        rfl

theorem cell23_1726454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_1726454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726454 prefixEnd_1726454 := by exact prefixLift 1726454
  have htrace : WordTrace (prefixWord ++ tailWord_1726454) baseStart_1726454 baseEnd_1726454 := by
    simpa [prefixWord, tailWord_1726454, baseEnd_1726454] using wordTrace_append hprefix tailTrace_1726454
  have hstable : (prefixWord ++ tailWord_1726454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726454).length < 2 ^ (prefixWord ++ tailWord_1726454).sum := by decide
  have hdescent : baseEnd_1726454 < baseStart_1726454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726514 : List Nat := [3, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2]
def baseStart_1726514 : Nat := 118140960795 + 1726514 * 2 ^ 59
def prefixEnd_1726514 : Nat := 4983230072969 + 3 ^ 40 * 1726514 * 2
def baseEnd_1726514 : Nat := 886531538716763239734913

theorem tailTrace_1726514 : CollatzResearch.WordTrace tailWord_1726514 prefixEnd_1726514 886531538716763239734913 := by
  unfold tailWord_1726514
  simp only [CollatzResearch.WordTrace]
  refine ⟨15742784716785529490224649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41980759244761411973932397 15742784716785529490224649)
  ·
    refine ⟨11807088537589147117668487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15742784716785529490224649 11807088537589147117668487)
    ·
      refine ⟨17710632806383720676502731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11807088537589147117668487 17710632806383720676502731)
      ·
        refine ⟨26565949209575581014754097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17710632806383720676502731 26565949209575581014754097)
        ·
          refine ⟨19924461907181685761065573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26565949209575581014754097 19924461907181685761065573)
          ·
            refine ⟨3735836607596566080199795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19924461907181685761065573 3735836607596566080199795)
            ·
              refine ⟨5603754911394849120299693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3735836607596566080199795 5603754911394849120299693)
              ·
                refine ⟨2101408091773068420112385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5603754911394849120299693 2101408091773068420112385)
                ·
                  refine ⟨1576056068829801315084289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2101408091773068420112385 1576056068829801315084289)
                  ·
                    refine ⟨1182042051622350986313217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1576056068829801315084289 1182042051622350986313217)
                    ·
                      refine ⟨886531538716763239734913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1182042051622350986313217 886531538716763239734913)
                      ·
                        rfl

theorem cell23_1726514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_1726514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726514 prefixEnd_1726514 := by exact prefixLift 1726514
  have htrace : WordTrace (prefixWord ++ tailWord_1726514) baseStart_1726514 baseEnd_1726514 := by
    simpa [prefixWord, tailWord_1726514, baseEnd_1726514] using wordTrace_append hprefix tailTrace_1726514
  have hstable : (prefixWord ++ tailWord_1726514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726514).length < 2 ^ (prefixWord ++ tailWord_1726514).sum := by decide
  have hdescent : baseEnd_1726514 < baseStart_1726514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726600 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_1726600 : Nat := 118140960795 + 1726600 * 2 ^ 59
def prefixEnd_1726600 : Nat := 4983230072969 + 3 ^ 40 * 1726600 * 2
def baseEnd_1726600 : Nat := 886575698053049903259517

theorem tailTrace_1726600 : CollatzResearch.WordTrace tailWord_1726600 prefixEnd_1726600 886575698053049903259517 := by
  unfold tailWord_1726600
  simp only [CollatzResearch.WordTrace]
  refine ⟨31487137772415277324264627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41982850363220369765686169 31487137772415277324264627)
  ·
    refine ⟨47230706658622915986396941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31487137772415277324264627 47230706658622915986396941)
    ·
      refine ⟨17711514996983593494898853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47230706658622915986396941 17711514996983593494898853)
      ·
        refine ⟨3320909061934423780293535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17711514996983593494898853 3320909061934423780293535)
        ·
          refine ⟨4981363592901635670440303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3320909061934423780293535 4981363592901635670440303)
          ·
            refine ⟨7472045389352453505660455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4981363592901635670440303 7472045389352453505660455)
            ·
              refine ⟨11208068084028680258490683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7472045389352453505660455 11208068084028680258490683)
              ·
                refine ⟨16812102126043020387736025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11208068084028680258490683 16812102126043020387736025)
                ·
                  refine ⟨12609076594532265290802019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16812102126043020387736025 12609076594532265290802019)
                  ·
                    refine ⟨18913614891798397936203029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12609076594532265290802019 18913614891798397936203029)
                    ·
                      refine ⟨886575698053049903259517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18913614891798397936203029 886575698053049903259517)
                      ·
                        rfl

theorem cell23_1726600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_1726600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726600 prefixEnd_1726600 := by exact prefixLift 1726600
  have htrace : WordTrace (prefixWord ++ tailWord_1726600) baseStart_1726600 baseEnd_1726600 := by
    simpa [prefixWord, tailWord_1726600, baseEnd_1726600] using wordTrace_append hprefix tailTrace_1726600
  have hstable : (prefixWord ++ tailWord_1726600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726600).length < 2 ^ (prefixWord ++ tailWord_1726600).sum := by decide
  have hdescent : baseEnd_1726600 < baseStart_1726600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726610 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 8]
def baseStart_1726610 : Nat := 118140960795 + 1726610 * 2 ^ 59
def prefixEnd_1726610 : Nat := 4983230072969 + 3 ^ 40 * 1726610 * 2
def baseEnd_1726610 : Nat := 98508981428843873792719

theorem tailTrace_1726610 : CollatzResearch.WordTrace tailWord_1726610 prefixEnd_1726610 98508981428843873792719 := by
  unfold tailWord_1726610
  simp only [CollatzResearch.WordTrace]
  refine ⟨15743660068698581589098321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41983093516529550904262189 15743660068698581589098321)
  ·
    refine ⟨11807745051523936191823741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15743660068698581589098321 11807745051523936191823741)
    ·
      refine ⟨4427904394321476071933903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11807745051523936191823741 4427904394321476071933903)
      ·
        refine ⟨6641856591482214107900855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4427904394321476071933903 6641856591482214107900855)
        ·
          refine ⟨9962784887223321161851283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6641856591482214107900855 9962784887223321161851283)
          ·
            refine ⟨14944177330834981742776925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9962784887223321161851283 14944177330834981742776925)
            ·
              refine ⟨5604066499063118153541347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14944177330834981742776925 5604066499063118153541347)
              ·
                refine ⟨8406099748594677230312021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5604066499063118153541347 8406099748594677230312021)
                ·
                  refine ⟨98508981428843873792719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8406099748594677230312021 98508981428843873792719)
                  ·
                    rfl

theorem cell23_1726610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_1726610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726610 prefixEnd_1726610 := by exact prefixLift 1726610
  have htrace : WordTrace (prefixWord ++ tailWord_1726610) baseStart_1726610 baseEnd_1726610 := by
    simpa [prefixWord, tailWord_1726610, baseEnd_1726610] using wordTrace_append hprefix tailTrace_1726610
  have hstable : (prefixWord ++ tailWord_1726610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726610).length < 2 ^ (prefixWord ++ tailWord_1726610).sum := by decide
  have hdescent : baseEnd_1726610 < baseStart_1726610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726613 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_1726613 : Nat := 118140960795 + 1726613 * 2 ^ 59
def prefixEnd_1726613 : Nat := 4983230072969 + 3 ^ 40 * 1726613 * 2
def baseEnd_1726613 : Nat := 886582373301558352396957

theorem tailTrace_1726613 : CollatzResearch.WordTrace tailWord_1726613 prefixEnd_1726613 886582373301558352396957 := by
  unfold tailWord_1726613
  simp only [CollatzResearch.WordTrace]
  refine ⟨62974749693783457868752493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41983166462522305245834995 62974749693783457868752493)
  ·
    refine ⟨23615531135168796700782185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62974749693783457868752493 23615531135168796700782185)
    ·
      refine ⟨17711648351376597525586639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23615531135168796700782185 17711648351376597525586639)
      ·
        refine ⟨26567472527064896288379959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17711648351376597525586639 26567472527064896288379959)
        ·
          refine ⟨39851208790597344432569939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26567472527064896288379959 39851208790597344432569939)
          ·
            refine ⟨59776813185896016648854909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39851208790597344432569939 59776813185896016648854909)
            ·
              refine ⟨22416304944711006243320591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59776813185896016648854909 22416304944711006243320591)
              ·
                refine ⟨33624457417066509364980887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22416304944711006243320591 33624457417066509364980887)
                ·
                  refine ⟨50436686125599764047471331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33624457417066509364980887 50436686125599764047471331)
                  ·
                    refine ⟨75655029188399646071206997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50436686125599764047471331 75655029188399646071206997)
                    ·
                      refine ⟨886582373301558352396957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 75655029188399646071206997 886582373301558352396957)
                      ·
                        rfl

theorem cell23_1726613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_1726613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726613 prefixEnd_1726613 := by exact prefixLift 1726613
  have htrace : WordTrace (prefixWord ++ tailWord_1726613) baseStart_1726613 baseEnd_1726613 := by
    simpa [prefixWord, tailWord_1726613, baseEnd_1726613] using wordTrace_append hprefix tailTrace_1726613
  have hstable : (prefixWord ++ tailWord_1726613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726613).length < 2 ^ (prefixWord ++ tailWord_1726613).sum := by decide
  have hdescent : baseEnd_1726613 < baseStart_1726613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726647 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 1, 5, 2]
def baseStart_1726647 : Nat := 118140960795 + 1726647 * 2 ^ 59
def prefixEnd_1726647 : Nat := 4983230072969 + 3 ^ 40 * 1726647 * 2
def baseEnd_1726647 : Nat := 886599831643811219371801

theorem tailTrace_1726647 : CollatzResearch.WordTrace tailWord_1726647 prefixEnd_1726647 886599831643811219371801 := by
  unfold tailWord_1726647
  simp only [CollatzResearch.WordTrace]
  refine ⟨62975989775660281675490195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41983993183773521116993463 62975989775660281675490195)
  ·
    refine ⟨94463984663490422513235293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62975989775660281675490195 94463984663490422513235293)
    ·
      refine ⟨35423994248808908442463235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94463984663490422513235293 35423994248808908442463235)
      ·
        refine ⟨53135991373213362663694853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35423994248808908442463235 53135991373213362663694853)
        ·
          refine ⟨9962998382477505499442785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53135991373213362663694853 9962998382477505499442785)
          ·
            refine ⟨7472248786858129124582089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9962998382477505499442785 7472248786858129124582089)
            ·
              refine ⟨5604186590143596843436567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7472248786858129124582089 5604186590143596843436567)
              ·
                refine ⟨8406279885215395265154851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5604186590143596843436567 8406279885215395265154851)
                ·
                  refine ⟨12609419827823092897732277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8406279885215395265154851 12609419827823092897732277)
                  ·
                    refine ⟨1182133108858414959162401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12609419827823092897732277 1182133108858414959162401)
                    ·
                      refine ⟨886599831643811219371801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1182133108858414959162401 886599831643811219371801)
                      ·
                        rfl

theorem cell23_1726647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 5, 2].length) (baseStart_1726647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726647 prefixEnd_1726647 := by exact prefixLift 1726647
  have htrace : WordTrace (prefixWord ++ tailWord_1726647) baseStart_1726647 baseEnd_1726647 := by
    simpa [prefixWord, tailWord_1726647, baseEnd_1726647] using wordTrace_append hprefix tailTrace_1726647
  have hstable : (prefixWord ++ tailWord_1726647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726647).length < 2 ^ (prefixWord ++ tailWord_1726647).sum := by decide
  have hdescent : baseEnd_1726647 < baseStart_1726647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726671 : List Nat := [1, 1, 2, 1, 1, 3, 7, 2, 1, 1, 3]
def baseStart_1726671 : Nat := 118140960795 + 1726671 * 2 ^ 59
def prefixEnd_1726671 : Nat := 4983230072969 + 3 ^ 40 * 1726671 * 2
def baseEnd_1726671 : Nat := 886612155179519125471691

theorem tailTrace_1726671 : CollatzResearch.WordTrace tailWord_1726671 prefixEnd_1726671 886612155179519125471691 := by
  unfold tailWord_1726671
  simp only [CollatzResearch.WordTrace]
  refine ⟨62976865127573333774363867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41984576751715555849575911 62976865127573333774363867)
  ·
    refine ⟨94465297691360000661545801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62976865127573333774363867 94465297691360000661545801)
    ·
      refine ⟨70848973268520000496159351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94465297691360000661545801 70848973268520000496159351)
      ·
        refine ⟨106273459902780000744239027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70848973268520000496159351 106273459902780000744239027)
        ·
          refine ⟨159410189854170001116358541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106273459902780000744239027 159410189854170001116358541)
          ·
            refine ⟨59778821195313750418634453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159410189854170001116358541 59778821195313750418634453)
            ·
              refine ⟨1401066121765166025436745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 59778821195313750418634453 1401066121765166025436745)
              ·
                refine ⟨1050799591323874519077559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1401066121765166025436745 1050799591323874519077559)
                ·
                  refine ⟨1576199386985811778616339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050799591323874519077559 1576199386985811778616339)
                  ·
                    refine ⟨2364299080478717667924509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1576199386985811778616339 2364299080478717667924509)
                    ·
                      refine ⟨886612155179519125471691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2364299080478717667924509 886612155179519125471691)
                      ·
                        rfl

theorem cell23_1726671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 1, 1, 3].length) (baseStart_1726671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726671 prefixEnd_1726671 := by exact prefixLift 1726671
  have htrace : WordTrace (prefixWord ++ tailWord_1726671) baseStart_1726671 baseEnd_1726671 := by
    simpa [prefixWord, tailWord_1726671, baseEnd_1726671] using wordTrace_append hprefix tailTrace_1726671
  have hstable : (prefixWord ++ tailWord_1726671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726671).length < 2 ^ (prefixWord ++ tailWord_1726671).sum := by decide
  have hdescent : baseEnd_1726671 < baseStart_1726671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726683 : List Nat := [1, 1, 1, 1, 1, 1, 1, 16]
def baseStart_1726683 : Nat := 118140960795 + 1726683 * 2 ^ 59
def prefixEnd_1726683 : Nat := 4983230072969 + 3 ^ 40 * 1726683 * 2
def baseEnd_1726683 : Nat := 32837715442495299204505

theorem tailTrace_1726683 : CollatzResearch.WordTrace tailWord_1726683 prefixEnd_1726683 32837715442495299204505 := by
  unfold tailWord_1726683
  simp only [CollatzResearch.WordTrace]
  refine ⟨62977302803529859823800703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41984868535686573215867135 62977302803529859823800703)
  ·
    refine ⟨94465954205294789735701055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62977302803529859823800703 94465954205294789735701055)
    ·
      refine ⟨141698931307942184603551583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94465954205294789735701055 141698931307942184603551583)
      ·
        refine ⟨212548396961913276905327375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141698931307942184603551583 212548396961913276905327375)
        ·
          refine ⟨318822595442869915357991063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212548396961913276905327375 318822595442869915357991063)
          ·
            refine ⟨478233893164304873036986595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318822595442869915357991063 478233893164304873036986595)
            ·
              refine ⟨717350839746457309555479893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478233893164304873036986595 717350839746457309555479893)
              ·
                refine ⟨32837715442495299204505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 16 717350839746457309555479893 32837715442495299204505)
                ·
                  rfl

theorem cell23_1726683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 16].length) (baseStart_1726683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726683 prefixEnd_1726683 := by exact prefixLift 1726683
  have htrace : WordTrace (prefixWord ++ tailWord_1726683) baseStart_1726683 baseEnd_1726683 := by
    simpa [prefixWord, tailWord_1726683, baseEnd_1726683] using wordTrace_append hprefix tailTrace_1726683
  have hstable : (prefixWord ++ tailWord_1726683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726683).length < 2 ^ (prefixWord ++ tailWord_1726683).sum := by decide
  have hdescent : baseEnd_1726683 < baseStart_1726683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726691 : List Nat := [1, 1, 1, 8, 1, 2, 1, 2, 1, 5]
def baseStart_1726691 : Nat := 118140960795 + 1726691 * 2 ^ 59
def prefixEnd_1726691 : Nat := 4983230072969 + 3 ^ 40 * 1726691 * 2
def baseEnd_1726691 : Nat := 295540808264203015740533

theorem tailTrace_1726691 : CollatzResearch.WordTrace tailWord_1726691 prefixEnd_1726691 295540808264203015740533 := by
  unfold tailWord_1726691
  simp only [CollatzResearch.WordTrace]
  refine ⟨62977594587500877190091927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41985063058333918126727951 62977594587500877190091927)
  ·
    refine ⟨94466391881251315785137891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62977594587500877190091927 94466391881251315785137891)
    ·
      refine ⟨141699587821876973677706837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94466391881251315785137891 141699587821876973677706837)
      ·
        refine ⟨1660542044787620785285627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 141699587821876973677706837 1660542044787620785285627)
        ·
          refine ⟨2490813067181431177928441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1660542044787620785285627 2490813067181431177928441)
          ·
            refine ⟨1868109800386073383446331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2490813067181431177928441 1868109800386073383446331)
            ·
              refine ⟨2802164700579110075169497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868109800386073383446331 2802164700579110075169497)
              ·
                refine ⟨2101623525434332556377123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2802164700579110075169497 2101623525434332556377123)
                ·
                  refine ⟨3152435288151498834565685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2101623525434332556377123 3152435288151498834565685)
                  ·
                    refine ⟨295540808264203015740533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3152435288151498834565685 295540808264203015740533)
                    ·
                      rfl

theorem cell23_1726691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 5].length) (baseStart_1726691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726691 prefixEnd_1726691 := by exact prefixLift 1726691
  have htrace : WordTrace (prefixWord ++ tailWord_1726691) baseStart_1726691 baseEnd_1726691 := by
    simpa [prefixWord, tailWord_1726691, baseEnd_1726691] using wordTrace_append hprefix tailTrace_1726691
  have hstable : (prefixWord ++ tailWord_1726691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726691).length < 2 ^ (prefixWord ++ tailWord_1726691).sum := by decide
  have hdescent : baseEnd_1726691 < baseStart_1726691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726728 : List Nat := [2, 1, 3, 2, 3, 2, 1, 4, 1, 2, 2]
def baseStart_1726728 : Nat := 118140960795 + 1726728 * 2 ^ 59
def prefixEnd_1726728 : Nat := 4983230072969 + 3 ^ 40 * 1726728 * 2
def baseEnd_1726728 : Nat := 886641423576825402458929

theorem tailTrace_1726728 : CollatzResearch.WordTrace tailWord_1726728 prefixEnd_1726728 886641423576825402458929 := by
  unfold tailWord_1726728
  simp only [CollatzResearch.WordTrace]
  refine ⟨31489472044183416254594419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41985962725577888339459225 31489472044183416254594419)
  ·
    refine ⟨47234208066275124381891629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31489472044183416254594419 47234208066275124381891629)
    ·
      refine ⟨17712828024853171643209361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47234208066275124381891629 17712828024853171643209361)
      ·
        refine ⟨13284621018639878732407021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17712828024853171643209361 13284621018639878732407021)
        ·
          refine ⟨4981732881989954524652633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13284621018639878732407021 4981732881989954524652633)
          ·
            refine ⟨3736299661492465893489475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4981732881989954524652633 3736299661492465893489475)
            ·
              refine ⟨5604449492238698840234213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3736299661492465893489475 5604449492238698840234213)
              ·
                refine ⟨1050834279794756032543915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5604449492238698840234213 1050834279794756032543915)
                ·
                  refine ⟨1576251419692134048815873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1050834279794756032543915 1576251419692134048815873)
                  ·
                    refine ⟨1182188564769100536611905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1576251419692134048815873 1182188564769100536611905)
                    ·
                      refine ⟨886641423576825402458929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1182188564769100536611905 886641423576825402458929)
                      ·
                        rfl

theorem cell23_1726728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_1726728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726728 prefixEnd_1726728 := by exact prefixLift 1726728
  have htrace : WordTrace (prefixWord ++ tailWord_1726728) baseStart_1726728 baseEnd_1726728 := by
    simpa [prefixWord, tailWord_1726728, baseEnd_1726728] using wordTrace_append hprefix tailTrace_1726728
  have hstable : (prefixWord ++ tailWord_1726728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726728).length < 2 ^ (prefixWord ++ tailWord_1726728).sum := by decide
  have hdescent : baseEnd_1726728 < baseStart_1726728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726730 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 2, 7]
def baseStart_1726730 : Nat := 118140960795 + 1726730 * 2 ^ 59
def prefixEnd_1726730 : Nat := 4983230072969 + 3 ^ 40 * 1726730 * 2
def baseEnd_1726730 : Nat := 295547483512711464877973

theorem tailTrace_1726730 : CollatzResearch.WordTrace tailWord_1726730 prefixEnd_1726730 295547483512711464877973 := by
  unfold tailWord_1726730
  simp only [CollatzResearch.WordTrace]
  refine ⟨15744754258589896712690411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41986011356239724567174429 15744754258589896712690411)
  ·
    refine ⟨23617131387884845069035617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15744754258589896712690411 23617131387884845069035617)
    ·
      refine ⟨17712848540913633801776713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23617131387884845069035617 17712848540913633801776713)
      ·
        refine ⟨13284636405685225351332535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17712848540913633801776713 13284636405685225351332535)
        ·
          refine ⟨19926954608527838026998803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13284636405685225351332535 19926954608527838026998803)
          ·
            refine ⟨29890431912791757040498205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19926954608527838026998803 29890431912791757040498205)
            ·
              refine ⟨11208911967296908890186827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29890431912791757040498205 11208911967296908890186827)
              ·
                refine ⟨16813367950945363335280241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11208911967296908890186827 16813367950945363335280241)
                ·
                  refine ⟨12610025963209022501460181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16813367950945363335280241 12610025963209022501460181)
                  ·
                    refine ⟨295547483512711464877973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12610025963209022501460181 295547483512711464877973)
                    ·
                      rfl

theorem cell23_1726730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_1726730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726730 prefixEnd_1726730 := by exact prefixLift 1726730
  have htrace : WordTrace (prefixWord ++ tailWord_1726730) baseStart_1726730 baseEnd_1726730 := by
    simpa [prefixWord, tailWord_1726730, baseEnd_1726730] using wordTrace_append hprefix tailTrace_1726730
  have hstable : (prefixWord ++ tailWord_1726730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726730).length < 2 ^ (prefixWord ++ tailWord_1726730).sum := by decide
  have hdescent : baseEnd_1726730 < baseStart_1726730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726744 : List Nat := [2, 1, 2, 3, 1, 2, 1, 5, 2, 1, 3]
def baseStart_1726744 : Nat := 118140960795 + 1726744 * 2 ^ 59
def prefixEnd_1726744 : Nat := 4983230072969 + 3 ^ 40 * 1726744 * 2
def baseEnd_1726744 : Nat := 886649639267297339858855

theorem tailTrace_1726744 : CollatzResearch.WordTrace tailWord_1726744 prefixEnd_1726744 886649639267297339858855 := by
  unfold tailWord_1726744
  simp only [CollatzResearch.WordTrace]
  refine ⟨31489763828154433620885643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41986351770872578161180857 31489763828154433620885643)
  ·
    refine ⟨47234645742231650431328465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31489763828154433620885643 47234645742231650431328465)
    ·
      refine ⟨35425984306673737823496349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47234645742231650431328465 35425984306673737823496349)
      ·
        refine ⟨13284744115002651683811131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35425984306673737823496349 13284744115002651683811131)
        ·
          refine ⟨19927116172503977525716697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13284744115002651683811131 19927116172503977525716697)
          ·
            refine ⟨14945337129377983144287523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19927116172503977525716697 14945337129377983144287523)
            ·
              refine ⟨22418005694066974716431285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14945337129377983144287523 22418005694066974716431285)
              ·
                refine ⟨2101688033818778879665433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22418005694066974716431285 2101688033818778879665433)
                ·
                  refine ⟨1576266025364084159749075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2101688033818778879665433 1576266025364084159749075)
                  ·
                    refine ⟨2364399038046126239623613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1576266025364084159749075 2364399038046126239623613)
                    ·
                      refine ⟨886649639267297339858855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2364399038046126239623613 886649639267297339858855)
                      ·
                        rfl

theorem cell23_1726744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_1726744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726744 prefixEnd_1726744 := by exact prefixLift 1726744
  have htrace : WordTrace (prefixWord ++ tailWord_1726744) baseStart_1726744 baseEnd_1726744 := by
    simpa [prefixWord, tailWord_1726744, baseEnd_1726744] using wordTrace_append hprefix tailTrace_1726744
  have hstable : (prefixWord ++ tailWord_1726744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726744).length < 2 ^ (prefixWord ++ tailWord_1726744).sum := by decide
  have hdescent : baseEnd_1726744 < baseStart_1726744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726765 : List Nat := [1, 5, 3, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_1726765 : Nat := 118140960795 + 1726765 * 2 ^ 59
def prefixEnd_1726765 : Nat := 4983230072969 + 3 ^ 40 * 1726765 * 2
def baseEnd_1726765 : Nat := 886660422361041757696259

theorem tailTrace_1726765 : CollatzResearch.WordTrace tailWord_1726765 prefixEnd_1726765 886660422361041757696259 := by
  unfold tailWord_1726765
  simp only [CollatzResearch.WordTrace]
  refine ⟨62980293589232787828285749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41986862392821858552190499 62980293589232787828285749)
  ·
    refine ⟨5904402523990573858901789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62980293589232787828285749 5904402523990573858901789)
    ·
      refine ⟨2214150946496465197088171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5904402523990573858901789 2214150946496465197088171)
      ·
        refine ⟨3321226419744697795632257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2214150946496465197088171 3321226419744697795632257)
        ·
          refine ⟨2490919814808523346724193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3321226419744697795632257 2490919814808523346724193)
          ·
            refine ⟨1868189861106392510043145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2490919814808523346724193 1868189861106392510043145)
            ·
              refine ⟨1401142395829794382532359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1868189861106392510043145 1401142395829794382532359)
              ·
                refine ⟨2101713593744691573798539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401142395829794382532359 2101713593744691573798539)
                ·
                  refine ⟨3152570390617037360697809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2101713593744691573798539 3152570390617037360697809)
                  ·
                    refine ⟨2364427792962778020523357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3152570390617037360697809 2364427792962778020523357)
                    ·
                      refine ⟨886660422361041757696259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2364427792962778020523357 886660422361041757696259)
                      ·
                        rfl

theorem cell23_1726765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_1726765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726765 prefixEnd_1726765 := by exact prefixLift 1726765
  have htrace : WordTrace (prefixWord ++ tailWord_1726765) baseStart_1726765 baseEnd_1726765 := by
    simpa [prefixWord, tailWord_1726765, baseEnd_1726765] using wordTrace_append hprefix tailTrace_1726765
  have hstable : (prefixWord ++ tailWord_1726765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726765).length < 2 ^ (prefixWord ++ tailWord_1726765).sum := by decide
  have hdescent : baseEnd_1726765 < baseStart_1726765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726777 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 2, 6]
def baseStart_1726777 : Nat := 118140960795 + 1726777 * 2 ^ 59
def prefixEnd_1726777 : Nat := 4983230072969 + 3 ^ 40 * 1726777 * 2
def baseEnd_1726777 : Nat := 295555528042965236915401

theorem tailTrace_1726777 : CollatzResearch.WordTrace tailWord_1726777 prefixEnd_1726777 295555528042965236915401 := by
  unfold tailWord_1726777
  simp only [CollatzResearch.WordTrace]
  refine ⟨62980731265189313877722585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41987154176792875918481723 62980731265189313877722585)
  ·
    refine ⟨47235548448891985408291939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62980731265189313877722585 47235548448891985408291939)
    ·
      refine ⟨70853322673337978112437909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47235548448891985408291939 70853322673337978112437909)
      ·
        refine ⟨3321249500312717724020527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70853322673337978112437909 3321249500312717724020527)
        ·
          refine ⟨4981874250469076586030791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3321249500312717724020527 4981874250469076586030791)
          ·
            refine ⟨7472811375703614879046187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4981874250469076586030791 7472811375703614879046187)
            ·
              refine ⟨11209217063555422318569281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7472811375703614879046187 11209217063555422318569281)
              ·
                refine ⟨8406912797666566738926961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11209217063555422318569281 8406912797666566738926961)
                ·
                  refine ⟨6305184598249925054195221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8406912797666566738926961 6305184598249925054195221)
                  ·
                    refine ⟨295555528042965236915401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6305184598249925054195221 295555528042965236915401)
                    ·
                      rfl

theorem cell23_1726777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 6].length) (baseStart_1726777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726777 prefixEnd_1726777 := by exact prefixLift 1726777
  have htrace : WordTrace (prefixWord ++ tailWord_1726777) baseStart_1726777 baseEnd_1726777 := by
    simpa [prefixWord, tailWord_1726777, baseEnd_1726777] using wordTrace_append hprefix tailTrace_1726777
  have hstable : (prefixWord ++ tailWord_1726777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726777).length < 2 ^ (prefixWord ++ tailWord_1726777).sum := by decide
  have hdescent : baseEnd_1726777 < baseStart_1726777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726801 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 1, 4, 2]
def baseStart_1726801 : Nat := 118140960795 + 1726801 * 2 ^ 59
def prefixEnd_1726801 : Nat := 4983230072969 + 3 ^ 40 * 1726801 * 2
def baseEnd_1726801 : Nat := 886678907664603616846093

theorem tailTrace_1726801 : CollatzResearch.WordTrace tailWord_1726801 prefixEnd_1726801 886678907664603616846093 := by
  unfold tailWord_1726801
  simp only [CollatzResearch.WordTrace]
  refine ⟨62981606617102365976596257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41987737744734910651064171 62981606617102365976596257)
  ·
    refine ⟨47236204962826774482447193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62981606617102365976596257 47236204962826774482447193)
    ·
      refine ⟨35427153722120080861835395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47236204962826774482447193 35427153722120080861835395)
      ·
        refine ⟨53140730583180121292753093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35427153722120080861835395 53140730583180121292753093)
        ·
          refine ⟨9963886984346272742391205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53140730583180121292753093 9963886984346272742391205)
          ·
            refine ⟨1868228809564926139198351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9963886984346272742391205 1868228809564926139198351)
            ·
              refine ⟨2802343214347389208797527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868228809564926139198351 2802343214347389208797527)
              ·
                refine ⟨4203514821521083813196291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2802343214347389208797527 4203514821521083813196291)
                ·
                  refine ⟨6305272232281625719794437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4203514821521083813196291 6305272232281625719794437)
                  ·
                    refine ⟨1182238543552804822461457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6305272232281625719794437 1182238543552804822461457)
                    ·
                      refine ⟨886678907664603616846093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1182238543552804822461457 886678907664603616846093)
                      ·
                        rfl

theorem cell23_1726801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 4, 2].length) (baseStart_1726801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726801 prefixEnd_1726801 := by exact prefixLift 1726801
  have htrace : WordTrace (prefixWord ++ tailWord_1726801) baseStart_1726801 baseEnd_1726801 := by
    simpa [prefixWord, tailWord_1726801, baseEnd_1726801] using wordTrace_append hprefix tailTrace_1726801
  have hstable : (prefixWord ++ tailWord_1726801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726801).length < 2 ^ (prefixWord ++ tailWord_1726801).sum := by decide
  have hdescent : baseEnd_1726801 < baseStart_1726801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726840 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 1, 4, 8]
def baseStart_1726840 : Nat := 118140960795 + 1726840 * 2 ^ 59
def prefixEnd_1726840 : Nat := 4983230072969 + 3 ^ 40 * 1726840 * 2
def baseEnd_1726840 : Nat := 886698933410128964258413

theorem tailTrace_1726840 : CollatzResearch.WordTrace tailWord_1726840 prefixEnd_1726840 886698933410128964258413 := by
  unfold tailWord_1726840
  simp only [CollatzResearch.WordTrace]
  refine ⟨31491514531980537818632987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41988686042640717091510649 31491514531980537818632987)
  ·
    refine ⟨47237271797970806727949481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31491514531980537818632987 47237271797970806727949481)
    ·
      refine ⟨35427953848478105045962111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47237271797970806727949481 35427953848478105045962111)
      ·
        refine ⟨53141930772717157568943167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35427953848478105045962111 53141930772717157568943167)
        ·
          refine ⟨79712896159075736353414751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53141930772717157568943167 79712896159075736353414751)
          ·
            refine ⟨119569344238613604530122127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79712896159075736353414751 119569344238613604530122127)
            ·
              refine ⟨179354016357920406795183191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119569344238613604530122127 179354016357920406795183191)
              ·
                refine ⟨269031024536880610192774787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179354016357920406795183191 269031024536880610192774787)
                ·
                  refine ⟨403546536805320915289162181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 269031024536880610192774787 403546536805320915289162181)
                  ·
                    refine ⟨75664975650997671616717909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 403546536805320915289162181 75664975650997671616717909)
                    ·
                      refine ⟨886698933410128964258413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 75664975650997671616717909 886698933410128964258413)
                      ·
                        rfl

theorem cell23_1726840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_1726840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726840 prefixEnd_1726840 := by exact prefixLift 1726840
  have htrace : WordTrace (prefixWord ++ tailWord_1726840) baseStart_1726840 baseEnd_1726840 := by
    simpa [prefixWord, tailWord_1726840, baseEnd_1726840] using wordTrace_append hprefix tailTrace_1726840
  have hstable : (prefixWord ++ tailWord_1726840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726840).length < 2 ^ (prefixWord ++ tailWord_1726840).sum := by decide
  have hdescent : baseEnd_1726840 < baseStart_1726840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726874 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1726874 : Nat := 118140960795 + 1726874 * 2 ^ 59
def prefixEnd_1726874 : Nat := 4983230072969 + 3 ^ 40 * 1726874 * 2
def baseEnd_1726874 : Nat := 886716391752381831233257

theorem tailTrace_1726874 : CollatzResearch.WordTrace tailWord_1726874 prefixEnd_1726874 886716391752381831233257 := by
  unfold tailWord_1726874
  simp only [CollatzResearch.WordTrace]
  refine ⟨15746067286459474861000919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41989512763891932962669117 15746067286459474861000919)
  ·
    refine ⟨23619100929689212291501379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15746067286459474861000919 23619100929689212291501379)
    ·
      refine ⟨35428651394533818437252069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23619100929689212291501379 35428651394533818437252069)
      ·
        refine ⟨6642872136475090956984763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35428651394533818437252069 6642872136475090956984763)
        ·
          refine ⟨9964308204712636435477145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6642872136475090956984763 9964308204712636435477145)
          ·
            refine ⟨7473231153534477326607859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9964308204712636435477145 7473231153534477326607859)
            ·
              refine ⟨11209846730301715989911789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7473231153534477326607859 11209846730301715989911789)
              ·
                refine ⟨4203692523863143496216921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11209846730301715989911789 4203692523863143496216921)
                ·
                  refine ⟨3152769392897357622162691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4203692523863143496216921 3152769392897357622162691)
                  ·
                    refine ⟨4729154089346036433244037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3152769392897357622162691 4729154089346036433244037)
                    ·
                      refine ⟨886716391752381831233257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4729154089346036433244037 886716391752381831233257)
                      ·
                        rfl

theorem cell23_1726874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1726874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726874 prefixEnd_1726874 := by exact prefixLift 1726874
  have htrace : WordTrace (prefixWord ++ tailWord_1726874) baseStart_1726874 baseEnd_1726874 := by
    simpa [prefixWord, tailWord_1726874, baseEnd_1726874] using wordTrace_append hprefix tailTrace_1726874
  have hstable : (prefixWord ++ tailWord_1726874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726874).length < 2 ^ (prefixWord ++ tailWord_1726874).sum := by decide
  have hdescent : baseEnd_1726874 < baseStart_1726874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726941 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_1726941 : Nat := 118140960795 + 1726941 * 2 ^ 59
def prefixEnd_1726941 : Nat := 4983230072969 + 3 ^ 40 * 1726941 * 2
def baseEnd_1726941 : Nat := 886750794956233069095449

theorem tailTrace_1726941 : CollatzResearch.WordTrace tailWord_1726941 prefixEnd_1726941 886750794956233069095449 := by
  unfold tailWord_1726941
  simp only [CollatzResearch.WordTrace]
  refine ⟨62986712836595169886692677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41991141891063446591128451 62986712836595169886692677)
  ·
    refine ⟨11810008656861594353754877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62986712836595169886692677 11810008656861594353754877)
    ·
      refine ⟨4428753246323097882658079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11810008656861594353754877 4428753246323097882658079)
      ·
        refine ⟨6643129869484646823987119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4428753246323097882658079 6643129869484646823987119)
        ·
          refine ⟨9964694804226970235980679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6643129869484646823987119 9964694804226970235980679)
          ·
            refine ⟨14947042206340455353971019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9964694804226970235980679 14947042206340455353971019)
            ·
              refine ⟨22420563309510683030956529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14947042206340455353971019 22420563309510683030956529)
              ·
                refine ⟨16815422482133012273217397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22420563309510683030956529 16815422482133012273217397)
                ·
                  refine ⟨1576445857699969900614131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16815422482133012273217397 1576445857699969900614131)
                  ·
                    refine ⟨2364668786549954850921197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1576445857699969900614131 2364668786549954850921197)
                    ·
                      refine ⟨886750794956233069095449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2364668786549954850921197 886750794956233069095449)
                      ·
                        rfl

theorem cell23_1726941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_1726941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726941 prefixEnd_1726941 := by exact prefixLift 1726941
  have htrace : WordTrace (prefixWord ++ tailWord_1726941) baseStart_1726941 baseEnd_1726941 := by
    simpa [prefixWord, tailWord_1726941, baseEnd_1726941] using wordTrace_append hprefix tailTrace_1726941
  have hstable : (prefixWord ++ tailWord_1726941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726941).length < 2 ^ (prefixWord ++ tailWord_1726941).sum := by decide
  have hdescent : baseEnd_1726941 < baseStart_1726941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726944 : List Nat := [2, 1, 1, 3, 1, 1, 5, 3, 1, 5]
def baseStart_1726944 : Nat := 118140960795 + 1726944 * 2 ^ 59
def prefixEnd_1726944 : Nat := 4983230072969 + 3 ^ 40 * 1726944 * 2
def baseEnd_1726944 : Nat := 295584111799398852452645

theorem tailTrace_1726944 : CollatzResearch.WordTrace tailWord_1726944 prefixEnd_1726944 295584111799398852452645 := by
  unfold tailWord_1726944
  simp only [CollatzResearch.WordTrace]
  refine ⟨31493411127792150699525943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41991214837056200932701257 31493411127792150699525943)
  ·
    refine ⟨47240116691688226049288915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31493411127792150699525943 47240116691688226049288915)
    ·
      refine ⟨70860175037532339073933373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47240116691688226049288915 70860175037532339073933373)
      ·
        refine ⟨26572565639074627152725015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70860175037532339073933373 26572565639074627152725015)
        ·
          refine ⟨39858848458611940729087523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26572565639074627152725015 39858848458611940729087523)
          ·
            refine ⟨59788272687917911093631285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39858848458611940729087523 59788272687917911093631285)
            ·
              refine ⟨5605150564492304165027933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59788272687917911093631285 5605150564492304165027933)
              ·
                refine ⟨2101931461684614061885475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5605150564492304165027933 2101931461684614061885475)
                ·
                  refine ⟨3152897192526921092828213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2101931461684614061885475 3152897192526921092828213)
                  ·
                    refine ⟨295584111799398852452645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3152897192526921092828213 295584111799398852452645)
                    ·
                      rfl

theorem cell23_1726944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 1, 5].length) (baseStart_1726944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726944 prefixEnd_1726944 := by exact prefixLift 1726944
  have htrace : WordTrace (prefixWord ++ tailWord_1726944) baseStart_1726944 baseEnd_1726944 := by
    simpa [prefixWord, tailWord_1726944, baseEnd_1726944] using wordTrace_append hprefix tailTrace_1726944
  have hstable : (prefixWord ++ tailWord_1726944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726944).length < 2 ^ (prefixWord ++ tailWord_1726944).sum := by decide
  have hdescent : baseEnd_1726944 < baseStart_1726944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1726951 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 4, 3, 2]
def baseStart_1726951 : Nat := 118140960795 + 1726951 * 2 ^ 59
def prefixEnd_1726951 : Nat := 4983230072969 + 3 ^ 40 * 1726951 * 2
def baseEnd_1726951 : Nat := 886755929762778029970403

theorem tailTrace_1726951 : CollatzResearch.WordTrace tailWord_1726951 prefixEnd_1726951 886755929762778029970403 := by
  unfold tailWord_1726951
  simp only [CollatzResearch.WordTrace]
  refine ⟨62987077566558941594556707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41991385044372627729704471 62987077566558941594556707)
  ·
    refine ⟨94480616349838412391835061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62987077566558941594556707 94480616349838412391835061)
    ·
      refine ⟨8857557782797351161734537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94480616349838412391835061 8857557782797351161734537)
      ·
        refine ⟨6643168337098013371300903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8857557782797351161734537 6643168337098013371300903)
        ·
          refine ⟨9964752505647020056951355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6643168337098013371300903 9964752505647020056951355)
          ·
            refine ⟨14947128758470530085427033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9964752505647020056951355 14947128758470530085427033)
            ·
              refine ⟨11210346568852897564070275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14947128758470530085427033 11210346568852897564070275)
              ·
                refine ⟨16815519853279346346105413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11210346568852897564070275 16815519853279346346105413)
                ·
                  refine ⟨3152909972489877439894765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16815519853279346346105413 3152909972489877439894765)
                  ·
                    refine ⟨1182341239683704039960537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3152909972489877439894765 1182341239683704039960537)
                    ·
                      refine ⟨886755929762778029970403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1182341239683704039960537 886755929762778029970403)
                      ·
                        rfl

theorem cell23_1726951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_1726951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1726951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1726951 prefixEnd_1726951 := by exact prefixLift 1726951
  have htrace : WordTrace (prefixWord ++ tailWord_1726951) baseStart_1726951 baseEnd_1726951 := by
    simpa [prefixWord, tailWord_1726951, baseEnd_1726951] using wordTrace_append hprefix tailTrace_1726951
  have hstable : (prefixWord ++ tailWord_1726951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1726951).length < 2 ^ (prefixWord ++ tailWord_1726951).sum := by decide
  have hdescent : baseEnd_1726951 < baseStart_1726951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1726951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
